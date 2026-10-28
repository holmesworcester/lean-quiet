//! The engine's crypto behind a C ABI: SHA-256, Ed25519, X25519, the
//! Ed25519 -> X25519 conversion, ChaCha20-Poly1305 (IETF, Noise's
//! nonce), XChaCha20-Poly1305, and the OS's random bytes. Byte for byte
//! what libsodium gives for the same inputs (tests/crypto_compat.c), with
//! libquiet's crates. Every function takes sizes it checks in C first
//! (native/crypto.c); none panics on any input.

use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{ChaCha20Poly1305, XChaCha20Poly1305};
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::montgomery::MontgomeryPoint;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use sha2::{Digest, Sha256, Sha512};
use zeroize::Zeroize;

unsafe fn slice<'a>(p: *const u8, n: usize) -> &'a [u8] {
    if n == 0 { &[] } else { std::slice::from_raw_parts(p, n) }
}

unsafe fn arr<const N: usize>(p: *const u8) -> [u8; N] {
    let mut a = [0u8; N];
    a.copy_from_slice(std::slice::from_raw_parts(p, N));
    a
}

unsafe fn put(out: *mut u8, b: &[u8]) {
    std::ptr::copy_nonoverlapping(b.as_ptr(), out, b.len());
}

#[no_mangle]
pub unsafe extern "C" fn lq_sha256(out: *mut u8, m: *const u8, n: usize) {
    put(out, &Sha256::digest(slice(m, n)));
}

/// seed (32) -> pk (32), sk (64 = seed ++ pk, libsodium's layout).
#[no_mangle]
pub unsafe extern "C" fn lq_ed25519_keypair(pk: *mut u8, sk: *mut u8, seed: *const u8) {
    let mut s = arr::<32>(seed);
    let key = SigningKey::from_bytes(&s);
    let p = key.verifying_key().to_bytes();
    put(pk, &p);
    put(sk, &s);
    put(sk.add(32), &p);
    s.zeroize();
}

/// sk (64: seed ++ pk) -> signature (64) of m.
#[no_mangle]
pub unsafe extern "C" fn lq_ed25519_sign(sig: *mut u8, sk: *const u8, m: *const u8, n: usize) {
    let mut s = arr::<32>(sk);
    let key = SigningKey::from_bytes(&s);
    put(sig, &key.sign(slice(m, n)).to_bytes());
    s.zeroize();
}

/// 0 if sig is pk's signature of m (strict: no small-order key or R,
/// canonical S), -1 otherwise.
#[no_mangle]
pub unsafe extern "C" fn lq_ed25519_verify(sig: *const u8, m: *const u8, n: usize, pk: *const u8) -> i32 {
    let Ok(vk) = VerifyingKey::from_bytes(&arr::<32>(pk)) else { return -1 };
    let s = Signature::from_bytes(&arr::<64>(sig));
    if vk.verify_strict(slice(m, n), &s).is_ok() { 0 } else { -1 }
}

/// sk, pk -> shared secret; -1 if it is all zeros (a small-order key).
#[no_mangle]
pub unsafe extern "C" fn lq_x25519(q: *mut u8, sk: *const u8, pk: *const u8) -> i32 {
    let mut s = arr::<32>(sk);
    let r = MontgomeryPoint(arr::<32>(pk)).mul_clamped(s).to_bytes();
    s.zeroize();
    put(q, &r);
    if r.iter().all(|b| *b == 0) { -1 } else { 0 }
}

#[no_mangle]
pub unsafe extern "C" fn lq_x25519_base(q: *mut u8, sk: *const u8) {
    let mut s = arr::<32>(sk);
    put(q, &MontgomeryPoint::mul_base_clamped(s).to_bytes());
    s.zeroize();
}

/// An Ed25519 secret key (64: seed ++ pk) -> its X25519 secret key: the
/// clamped first half of SHA-512(seed), as libsodium derives it.
#[no_mangle]
pub unsafe extern "C" fn lq_ed_sk_to_x(x: *mut u8, sk: *const u8) {
    let mut h: [u8; 64] = Sha512::digest(slice(sk, 32)).into();
    h[0] &= 248;
    h[31] &= 127;
    h[31] |= 64;
    put(x, &h[..32]);
    h.zeroize();
}

/// An Ed25519 public key -> its X25519 public key; -1 if it is not a
/// point, is of small order, or is outside the prime-order subgroup
/// (libsodium refuses all three).
#[no_mangle]
pub unsafe extern "C" fn lq_ed_pk_to_x(x: *mut u8, pk: *const u8) -> i32 {
    match CompressedEdwardsY(arr::<32>(pk)).decompress() {
        Some(p) if !p.is_small_order() && p.is_torsion_free() => {
            put(x, &p.to_montgomery().to_bytes());
            0
        }
        _ => -1,
    }
}

/// Noise's ChaChaPoly nonce: 32 zero bits, then n little-endian.
fn noise_nonce(n: u64) -> [u8; 12] {
    let mut o = [0u8; 12];
    o[4..].copy_from_slice(&n.to_le_bytes());
    o
}

/// ciphertext ++ tag (16) into c (m + 16 bytes).
#[no_mangle]
pub unsafe extern "C" fn lq_chachapoly_seal(c: *mut u8, k: *const u8, n: u64, ad: *const u8,
    adlen: usize, p: *const u8, m: usize) -> i32 {
    let cipher = ChaCha20Poly1305::new(&arr::<32>(k).into());
    match cipher.encrypt(&noise_nonce(n).into(), Payload { msg: slice(p, m), aad: slice(ad, adlen) }) {
        Ok(v) => { put(c, &v); 0 }
        Err(_) => -1,
    }
}

/// plaintext (clen - 16 bytes) into p; -1 if the tag is wrong.
#[no_mangle]
pub unsafe extern "C" fn lq_chachapoly_open(p: *mut u8, k: *const u8, n: u64, ad: *const u8,
    adlen: usize, c: *const u8, clen: usize) -> i32 {
    let cipher = ChaCha20Poly1305::new(&arr::<32>(k).into());
    match cipher.decrypt(&noise_nonce(n).into(), Payload { msg: slice(c, clen), aad: slice(ad, adlen) }) {
        Ok(v) => { put(p, &v); 0 }
        Err(_) => -1,
    }
}

#[no_mangle]
pub unsafe extern "C" fn lq_xchacha_seal(c: *mut u8, k: *const u8, n: *const u8, ad: *const u8,
    adlen: usize, p: *const u8, m: usize) -> i32 {
    let cipher = XChaCha20Poly1305::new(&arr::<32>(k).into());
    match cipher.encrypt(&arr::<24>(n).into(), Payload { msg: slice(p, m), aad: slice(ad, adlen) }) {
        Ok(v) => { put(c, &v); 0 }
        Err(_) => -1,
    }
}

#[no_mangle]
pub unsafe extern "C" fn lq_xchacha_open(p: *mut u8, k: *const u8, n: *const u8, ad: *const u8,
    adlen: usize, c: *const u8, clen: usize) -> i32 {
    let cipher = XChaCha20Poly1305::new(&arr::<32>(k).into());
    match cipher.decrypt(&arr::<24>(n).into(), Payload { msg: slice(c, clen), aad: slice(ad, adlen) }) {
        Ok(v) => { put(p, &v); 0 }
        Err(_) => -1,
    }
}

/// n random bytes from the OS; -1 if it has none to give.
#[no_mangle]
pub unsafe extern "C" fn lq_random(out: *mut u8, n: usize) -> i32 {
    if n == 0 { return 0; }
    let b = std::slice::from_raw_parts_mut(out, n);
    if getrandom::fill(b).is_ok() { 0 } else { -1 }
}
