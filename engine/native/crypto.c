// The engine's crypto for Lean, on every platform: these externs call
// the Rust library in native/crypto (libquiet's pure-Rust crates), so
// the desktop, Android and iOS run one implementation. Sizes are checked
// here; tests/crypto_compat.c checks the bytes against libsodium's.
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

void lq_sha256(uint8_t* out, const uint8_t* m, size_t n);
void lq_ed25519_keypair(uint8_t* pk, uint8_t* sk, const uint8_t* seed);
void lq_ed25519_sign(uint8_t* sig, const uint8_t* sk, const uint8_t* m, size_t n);
int lq_ed25519_verify(const uint8_t* sig, const uint8_t* m, size_t n, const uint8_t* pk);
int lq_x25519(uint8_t* q, const uint8_t* sk, const uint8_t* pk);
void lq_x25519_base(uint8_t* q, const uint8_t* sk);
void lq_ed_sk_to_x(uint8_t* x, const uint8_t* sk);
int lq_ed_pk_to_x(uint8_t* x, const uint8_t* pk);
int lq_chachapoly_seal(uint8_t* c, const uint8_t* k, uint64_t n, const uint8_t* ad, size_t adlen,
    const uint8_t* p, size_t m);
int lq_chachapoly_open(uint8_t* p, const uint8_t* k, uint64_t n, const uint8_t* ad, size_t adlen,
    const uint8_t* c, size_t clen);
int lq_xchacha_seal(uint8_t* c, const uint8_t* k, const uint8_t* n, const uint8_t* ad, size_t adlen,
    const uint8_t* p, size_t m);
int lq_xchacha_open(uint8_t* p, const uint8_t* k, const uint8_t* n, const uint8_t* ad, size_t adlen,
    const uint8_t* c, size_t clen);
int lq_random(uint8_t* out, size_t n);

static lean_obj_res bytes(const void* p, size_t n) {
  lean_object* b = lean_alloc_sarray(1, n, n);
  if (n) memcpy(lean_sarray_cptr(b), p, n);
  return b;
}

static lean_obj_res some(lean_object* v) {
  lean_object* r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, v);
  return r;
}

static const uint8_t* ptr(b_lean_obj_arg a) { return lean_sarray_cptr(a); }

LEAN_EXPORT lean_obj_res le_sha256(b_lean_obj_arg in) {
  uint8_t out[32];
  lq_sha256(out, ptr(in), lean_sarray_size(in));
  return bytes(out, 32);
}

// seed (32 bytes) -> pk (32) ++ sk (64 = seed ++ pk)
LEAN_EXPORT lean_obj_res le_ed25519_keypair(b_lean_obj_arg seed) {
  uint8_t out[96];
  if (lean_sarray_size(seed) != 32) return bytes(out, 0);
  lq_ed25519_keypair(out, out + 32, ptr(seed));
  lean_obj_res r = bytes(out, 96);
  memset(out, 0, sizeof out);
  return r;
}

LEAN_EXPORT lean_obj_res le_ed25519_sign(b_lean_obj_arg sk, b_lean_obj_arg msg) {
  uint8_t sig[64];
  if (lean_sarray_size(sk) != 64) return bytes(sig, 0);
  lq_ed25519_sign(sig, ptr(sk), ptr(msg), lean_sarray_size(msg));
  return bytes(sig, 64);
}

LEAN_EXPORT uint8_t le_ed25519_verify(b_lean_obj_arg pk, b_lean_obj_arg msg, b_lean_obj_arg sig) {
  if (lean_sarray_size(pk) != 32 || lean_sarray_size(sig) != 64) return 0;
  return lq_ed25519_verify(ptr(sig), ptr(msg), lean_sarray_size(msg), ptr(pk)) == 0;
}

// sk (32), pk (32) -> the shared secret, or empty bytes for a bad point.
LEAN_EXPORT lean_obj_res le_x25519(b_lean_obj_arg sk, b_lean_obj_arg pk) {
  uint8_t q[32];
  if (lean_sarray_size(sk) != 32 || lean_sarray_size(pk) != 32) return bytes(q, 0);
  if (lq_x25519(q, ptr(sk), ptr(pk)) != 0) return bytes(q, 0);
  return bytes(q, 32);
}

// sk (32) -> pk (32); a wrong-sized key gives 32 zero bytes, which no DH
// accepts.
LEAN_EXPORT lean_obj_res le_x25519_base(b_lean_obj_arg sk) {
  uint8_t q[32] = {0};
  if (lean_sarray_size(sk) == 32) lq_x25519_base(q, ptr(sk));
  return bytes(q, 32);
}

// An Ed25519 secret key (64: seed ++ pk) -> its X25519 secret key (32).
LEAN_EXPORT lean_obj_res le_ed_sk_to_x(b_lean_obj_arg sk) {
  uint8_t x[32] = {0};
  if (lean_sarray_size(sk) == 64) lq_ed_sk_to_x(x, ptr(sk));
  lean_obj_res r = bytes(x, 32);
  memset(x, 0, sizeof x);
  return r;
}

// An Ed25519 public key (32) -> its X25519 public key, or empty bytes if
// it is not a valid point.
LEAN_EXPORT lean_obj_res le_ed_pk_to_x(b_lean_obj_arg pk) {
  uint8_t x[32];
  if (lean_sarray_size(pk) != 32) return bytes(x, 0);
  if (lq_ed_pk_to_x(x, ptr(pk)) != 0) return bytes(x, 0);
  return bytes(x, 32);
}

// key (32), counter nonce, ad, plaintext -> ciphertext; empty bytes if the
// key is not 32 bytes, as le_xchacha_seal does. Never a fallback key: open
// refuses a wrong-sized key, so sealing under one must too.
LEAN_EXPORT lean_obj_res le_chachapoly_seal(b_lean_obj_arg k, uint64_t n, b_lean_obj_arg ad,
    b_lean_obj_arg p) {
  if (lean_sarray_size(k) != 32) return bytes(NULL, 0);
  size_t m = lean_sarray_size(p);
  lean_object* r = lean_alloc_sarray(1, m + 16, m + 16);
  lq_chachapoly_seal(lean_sarray_cptr(r), ptr(k), n, ptr(ad), lean_sarray_size(ad), ptr(p), m);
  return r;
}

LEAN_EXPORT lean_obj_res le_chachapoly_open(b_lean_obj_arg k, uint64_t n, b_lean_obj_arg ad,
    b_lean_obj_arg c) {
  size_t m = lean_sarray_size(c);
  if (m < 16 || lean_sarray_size(k) != 32) return lean_box(0);
  lean_object* r = lean_alloc_sarray(1, m - 16, m - 16);
  if (lq_chachapoly_open(lean_sarray_cptr(r), ptr(k), n, ptr(ad), lean_sarray_size(ad), ptr(c), m) != 0) {
    lean_dec_ref(r);
    return lean_box(0);
  }
  return some(r);
}

// key (32), nonce (24), ad, plaintext -> ciphertext; empty bytes if a
// size is wrong.
LEAN_EXPORT lean_obj_res le_xchacha_seal(b_lean_obj_arg k, b_lean_obj_arg n, b_lean_obj_arg ad,
    b_lean_obj_arg p) {
  if (lean_sarray_size(k) != 32 || lean_sarray_size(n) != 24) return bytes(NULL, 0);
  size_t m = lean_sarray_size(p);
  lean_object* r = lean_alloc_sarray(1, m + 16, m + 16);
  lq_xchacha_seal(lean_sarray_cptr(r), ptr(k), ptr(n), ptr(ad), lean_sarray_size(ad), ptr(p), m);
  return r;
}

LEAN_EXPORT lean_obj_res le_xchacha_open(b_lean_obj_arg k, b_lean_obj_arg n, b_lean_obj_arg ad,
    b_lean_obj_arg c) {
  size_t m = lean_sarray_size(c);
  if (m < 16 || lean_sarray_size(k) != 32 || lean_sarray_size(n) != 24) return lean_box(0);
  lean_object* r = lean_alloc_sarray(1, m - 16, m - 16);
  if (lq_xchacha_open(lean_sarray_cptr(r), ptr(k), ptr(n), ptr(ad), lean_sarray_size(ad), ptr(c), m) != 0) {
    lean_dec_ref(r);
    return lean_box(0);
  }
  return some(r);
}

LEAN_EXPORT lean_obj_res le_random(uint32_t n, lean_obj_arg w) {
  (void)w;
  lean_object* r = lean_alloc_sarray(1, n, n);
  if (lq_random(lean_sarray_cptr(r), n) != 0) {
    lean_dec_ref(r);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("no random bytes")));
  }
  return lean_io_result_mk_ok(r);
}
