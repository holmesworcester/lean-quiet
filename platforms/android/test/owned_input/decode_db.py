#!/usr/bin/env python3
"""Decode actual canonical verdict facts and authenticate every sealed message.
Only synthetic fixture content is emitted; content keys never leave this process.
"""
from pathlib import Path
import ctypes,json,sqlite3,sys

class Decoder:
    def __init__(self,bs):self.bs=bs;self.i=0
    def nat(self):
        start=self.i;n=0;shift=0
        while True:
            if self.i>=len(self.bs):raise ValueError('short nat')
            b=self.bs[self.i];self.i+=1;n|=(b&127)<<shift
            if not b&128:break
            shift+=7
        if encode_nat(n)!=self.bs[start:self.i]:raise ValueError('noncanonical nat')
        return n
    def blob(self):
        n=self.nat();end=self.i+n
        if end>len(self.bs):raise ValueError('short blob')
        b=self.bs[self.i:end];self.i=end;return b
    def done(self):
        if self.i!=len(self.bs):raise ValueError('unconsumed fact bytes')

def encode_nat(n):
    b=bytearray()
    while n>=128:b.append((n&127)|128);n>>=7
    b.append(n);return bytes(b)
def encode_blob(b):return encode_nat(len(b))+b

def checkpoint_drafts(path):
    """Parse the actual latest app-owned checkpoint op, including saved drafts."""
    db=sqlite3.connect(path)
    try:
        assert db.execute('pragma integrity_check').fetchone()[0]=='ok'
        row=db.execute('select seq,bytes from app_ops order by seq desc limit 1').fetchone()
        if row is None:return None
        raw=row[1];assert raw[:2]==bytes([239,0]),'not the empty-requirement checkpoint op'
        op=Decoder(raw[2:]);body=op.blob();op.done();d=Decoder(body)
        version,page=d.nat(),d.nat();acceptance,anchor=d.blob(),d.blob();offset=d.nat()
        fields=[]
        while d.bs[d.i]==1:d.i+=1;fields.append(d.blob())
        assert d.bs[d.i]==0;d.i+=1;d.done()
        assert version==1 and len(fields)>7
        d=Decoder(fields[7]);drafts=[]
        while d.bs[d.i]==1:
            d.i+=1;owner,text=d.blob(),d.blob();photos=[]
            while d.bs[d.i]==1:d.i+=1;photos.append(d.blob())
            assert d.bs[d.i]==0;d.i+=1
            drafts.append({'acceptance':owner.hex(),'text':text.decode('utf-8'),'photos':len(photos)})
        assert d.bs[d.i]==0;d.i+=1;d.done()
        return {'sequence':row[0],'page':page,'current':acceptance.hex(),'drafts':drafts}
    finally:db.close()

def names(path):
    """Canonical actual valid verdicts for community names and user profiles."""
    db=sqlite3.connect(path)
    try:
        assert db.execute('pragma integrity_check').fetchone()[0]=='ok'
        result=[]
        for oid,raw in db.execute('select s.id,s.verdict from status s join ops o on o.id=s.id'):
            if len(raw)<3 or raw[:2]!=b'\x01\x00' or raw[2] not in (6,14):continue
            d=Decoder(raw[3:]);c,u,text=d.blob(),d.blob(),d.blob();counter=d.nat();d.done()
            result.append({'id':oid.hex(),'community':c.hex(),'user':u.hex(),
                'kind':'profile' if raw[2]==6 else 'named','value':text.decode('utf-8'),
                'counter':counter,'valid_fact':True,'op_bytes_present':True})
        return result
    finally:db.close()

def decode(path):
    db=sqlite3.connect(path)
    assert db.execute('pragma integrity_check').fetchone()[0]=='ok'
    keys={};messages=[]
    for oid,raw,opbytes in db.execute('select s.id,s.verdict,o.bytes from status s join ops o on o.id=s.id'):
        if len(raw)<3 or raw[:2]!=b'\x01\x00':continue
        tag=raw[2]
        if tag not in (16,21,23):continue
        d=Decoder(raw[3:])
        if tag==16:
            c,kid,key=d.blob(),d.blob(),d.blob();d.done()
            assert len(key)==32
            if (c,kid) in keys:assert keys[c,kid]==key
            keys[c,kid]=key
        else:
            c,user,device,kid,sealed=[d.blob() for _ in range(5)]
            sequence,time=d.nat(),d.nat();root=d.blob() if tag==23 else None;d.done()
            messages.append((oid,c,kid,sealed,sequence,time))
    sodium=ctypes.CDLL('libsodium.so.23');assert sodium.sodium_init()>=0
    decrypt=sodium.crypto_aead_xchacha20poly1305_ietf_decrypt
    decrypt.argtypes=[ctypes.c_void_p,ctypes.POINTER(ctypes.c_ulonglong),ctypes.c_void_p,ctypes.c_void_p,ctypes.c_ulonglong,ctypes.c_void_p,ctypes.c_ulonglong,ctypes.c_void_p,ctypes.c_void_p]
    decrypt.restype=ctypes.c_int
    evidence=[]
    for oid,c,kid,sealed,sequence,time in messages:
        key=keys[c,kid];assert len(sealed)>=40
        nonce,cipher=sealed[:24],sealed[24:]
        ad=encode_blob(c)+encode_blob(kid);plain=ctypes.create_string_buffer(len(cipher));n=ctypes.c_ulonglong()
        assert decrypt(plain,ctypes.byref(n),None,cipher,len(cipher),ad,len(ad),nonce,key)==0,'AEAD authentication failed'
        text=plain.raw[:n.value].decode('utf-8',errors='strict')
        evidence.append({'id':oid.hex(),'community':c.hex(),'sequence':sequence,'time':time,'plaintext':text,'valid_fact':True,'op_bytes_present':True,'aead_authenticated':True})
    return evidence
if __name__=='__main__':print(json.dumps(decode(sys.argv[1]),indent=2))
