#!/usr/bin/env python3
"""Serve only the built workspace and optional cached public Lean runtime."""
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler
from pathlib import Path
from urllib.parse import urlsplit, unquote
import argparse, os
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser()
p.add_argument('--port',type=int,default=4173)
p.add_argument('--bind',default='127.0.0.1')
p.add_argument('--runtime',default=os.environ.get('QUIET_LEAN_RUNTIME','/mnt/storage/holmes-tmp/quiet-lean-browser-runtime'))
a=p.parse_args()
class Handler(SimpleHTTPRequestHandler):
    def __init__(self,*args,**kwargs):super().__init__(*args,directory=str(ROOT/'dist'),**kwargs)
    def translate_path(self,path):
        name=unquote(urlsplit(path).path)
        if name.startswith('/lean-runtime/'):
            asset=name.removeprefix('/lean-runtime/')
            if asset in ('lean.js','lean.wasm','lean-lib.tar.gz'):return str(Path(a.runtime)/asset)
            return str(ROOT/'dist'/'not-found')
        return super().translate_path(path)
    def end_headers(self):
        self.send_header('Cross-Origin-Opener-Policy','same-origin')
        self.send_header('Cross-Origin-Embedder-Policy','require-corp')
        self.send_header('Cross-Origin-Resource-Policy','same-origin')
        self.send_header('X-Content-Type-Options','nosniff')
        self.send_header('Cache-Control','no-cache' if not self.path.startswith('/lean-runtime/') else 'public, max-age=86400')
        super().end_headers()
    def list_directory(self,path):self.send_error(404);return None
print(f'Quiet workspace: http://{a.bind}:{a.port}',flush=True)
ThreadingHTTPServer((a.bind,a.port),Handler).serve_forever()
