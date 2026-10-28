// The handshake's primitives from libsodium (linked from its shared
// library, whose headers this box lacks): X25519, ChaCha20-Poly1305
// (IETF, Noise's ChaChaPoly nonce), the Ed25519 -> X25519 key
// conversion, and the OS's random bytes. Everything else in the
// handshake is Lean (Connection/Noise.lean).
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

// ---- libsodium, declared by hand -------------------------------------------
int sodium_init(void);
void randombytes_buf(void* buf, size_t size);
int crypto_scalarmult(unsigned char* q, const unsigned char* n, const unsigned char* p);
int crypto_scalarmult_base(unsigned char* q, const unsigned char* n);
int crypto_sign_ed25519_sk_to_curve25519(unsigned char* x, const unsigned char* ed_sk);
int crypto_sign_ed25519_pk_to_curve25519(unsigned char* x, const unsigned char* ed_pk);
int crypto_aead_chacha20poly1305_ietf_encrypt(unsigned char* c, unsigned long long* clen,
    const unsigned char* m, unsigned long long mlen, const unsigned char* ad,
    unsigned long long adlen, const unsigned char* nsec, const unsigned char* npub,
    const unsigned char* k);
int crypto_aead_chacha20poly1305_ietf_decrypt(unsigned char* m, unsigned long long* mlen,
    unsigned char* nsec, const unsigned char* c, unsigned long long clen,
    const unsigned char* ad, unsigned long long adlen, const unsigned char* npub,
    const unsigned char* k);

static lean_obj_res bytes(const unsigned char* p, size_t n) {
  lean_object* r = lean_alloc_sarray(1, n, n);
  if (n) memcpy(lean_sarray_cptr(r), p, n);
  return r;
}

static lean_obj_res some(lean_object* v) {
  lean_object* r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, v);
  return r;
}

// Noise's ChaChaPoly nonce: 32 zero bits, then n little-endian.
static void nonce(unsigned char out[12], uint64_t n) {
  memset(out, 0, 4);
  for (int i = 0; i < 8; i++) out[4 + i] = (unsigned char)(n >> (8 * i));
}

// sk (32), pk (32) -> the shared secret, or empty bytes for a bad point
// (libsodium refuses an all-zero result).
LEAN_EXPORT lean_obj_res le_x25519(b_lean_obj_arg sk, b_lean_obj_arg pk) {
  unsigned char q[32];
  if (lean_sarray_size(sk) != 32 || lean_sarray_size(pk) != 32) return bytes(q, 0);
  if (crypto_scalarmult(q, lean_sarray_cptr(sk), lean_sarray_cptr(pk)) != 0) return bytes(q, 0);
  return bytes(q, 32);
}

// sk (32) -> pk (32); a wrong-sized key gives 32 zero bytes, which no
// DH accepts.
LEAN_EXPORT lean_obj_res le_x25519_base(b_lean_obj_arg sk) {
  unsigned char q[32] = {0};
  if (lean_sarray_size(sk) == 32) crypto_scalarmult_base(q, lean_sarray_cptr(sk));
  return bytes(q, 32);
}

LEAN_EXPORT lean_obj_res le_chachapoly_seal(b_lean_obj_arg k, uint64_t n, b_lean_obj_arg ad,
    b_lean_obj_arg p) {
  size_t m = lean_sarray_size(p);
  lean_object* r = lean_alloc_sarray(1, m + 16, m + 16);
  unsigned char npub[12], zero[32] = {0};
  unsigned long long clen;
  nonce(npub, n);
  const unsigned char* key = lean_sarray_size(k) == 32 ? lean_sarray_cptr(k) : zero;
  crypto_aead_chacha20poly1305_ietf_encrypt(lean_sarray_cptr(r), &clen, lean_sarray_cptr(p), m,
      lean_sarray_cptr(ad), lean_sarray_size(ad), NULL, npub, key);
  return r;
}

LEAN_EXPORT lean_obj_res le_chachapoly_open(b_lean_obj_arg k, uint64_t n, b_lean_obj_arg ad,
    b_lean_obj_arg c) {
  size_t m = lean_sarray_size(c);
  if (m < 16 || lean_sarray_size(k) != 32) return lean_box(0);
  lean_object* r = lean_alloc_sarray(1, m - 16, m - 16);
  unsigned char npub[12];
  unsigned long long plen;
  nonce(npub, n);
  if (crypto_aead_chacha20poly1305_ietf_decrypt(lean_sarray_cptr(r), &plen, NULL,
          lean_sarray_cptr(c), m, lean_sarray_cptr(ad), lean_sarray_size(ad), npub,
          lean_sarray_cptr(k)) != 0) {
    lean_dec_ref(r);
    return lean_box(0);
  }
  return some(r);
}

// An Ed25519 secret key (64: seed ++ pk) -> its X25519 secret key (32).
LEAN_EXPORT lean_obj_res le_ed_sk_to_x(b_lean_obj_arg sk) {
  unsigned char x[32] = {0};
  if (lean_sarray_size(sk) == 64) crypto_sign_ed25519_sk_to_curve25519(x, lean_sarray_cptr(sk));
  return bytes(x, 32);
}

// An Ed25519 public key (32) -> its X25519 public key, or empty bytes if
// it is not a valid point.
LEAN_EXPORT lean_obj_res le_ed_pk_to_x(b_lean_obj_arg pk) {
  unsigned char x[32];
  if (lean_sarray_size(pk) != 32) return bytes(x, 0);
  if (crypto_sign_ed25519_pk_to_curve25519(x, lean_sarray_cptr(pk)) != 0) return bytes(x, 0);
  return bytes(x, 32);
}

LEAN_EXPORT lean_obj_res le_random(uint32_t n, lean_obj_arg w) {
  (void)w;
  sodium_init();
  lean_object* r = lean_alloc_sarray(1, n, n);
  randombytes_buf(lean_sarray_cptr(r), n);
  return lean_io_result_mk_ok(r);
}
