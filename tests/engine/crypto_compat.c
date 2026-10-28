// The engine's Rust crypto (native/crypto) against libsodium, byte for
// byte, on random inputs: SHA-256, Ed25519 (keys, signatures, verifying,
// and refusing a changed message), X25519, the Ed25519 -> X25519
// conversions (including refused keys), ChaCha20-Poly1305 and
// XChaCha20-Poly1305 (sealing, opening, and refusing a changed frame).
// The engine used libsodium until this library replaced it, so equal
// bytes mean every stored id and signature stays as it was.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
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

int sodium_init(void);
int crypto_hash_sha256(unsigned char*, const unsigned char*, unsigned long long);
int crypto_sign_ed25519_seed_keypair(unsigned char* pk, unsigned char* sk, const unsigned char* seed);
int crypto_sign_ed25519_detached(unsigned char*, unsigned long long*, const unsigned char*,
    unsigned long long, const unsigned char*);
int crypto_sign_ed25519_verify_detached(const unsigned char*, const unsigned char*,
    unsigned long long, const unsigned char*);
int crypto_scalarmult(unsigned char*, const unsigned char*, const unsigned char*);
int crypto_scalarmult_base(unsigned char*, const unsigned char*);
int crypto_sign_ed25519_sk_to_curve25519(unsigned char*, const unsigned char*);
int crypto_sign_ed25519_pk_to_curve25519(unsigned char*, const unsigned char*);
int crypto_aead_chacha20poly1305_ietf_encrypt(unsigned char*, unsigned long long*,
    const unsigned char*, unsigned long long, const unsigned char*, unsigned long long,
    const unsigned char*, const unsigned char*, const unsigned char*);
int crypto_aead_chacha20poly1305_ietf_decrypt(unsigned char*, unsigned long long*, unsigned char*,
    const unsigned char*, unsigned long long, const unsigned char*, unsigned long long,
    const unsigned char*, const unsigned char*);
int crypto_aead_xchacha20poly1305_ietf_encrypt(unsigned char*, unsigned long long*,
    const unsigned char*, unsigned long long, const unsigned char*, unsigned long long,
    const unsigned char*, const unsigned char*, const unsigned char*);
int crypto_aead_xchacha20poly1305_ietf_decrypt(unsigned char*, unsigned long long*, unsigned char*,
    const unsigned char*, unsigned long long, const unsigned char*, unsigned long long,
    const unsigned char*, const unsigned char*);

static int bad = 0;
static void check(const char* what, int ok) {
  if (!ok) { bad++; if (bad < 20) fprintf(stderr, "FAIL: %s\n", what); }
}
static void fill(uint8_t* b, size_t n) { for (size_t i = 0; i < n; i++) b[i] = (uint8_t)rand(); }

int main(void) {
  sodium_init();
  srand(11);
  static uint8_t m[4096], c1[4096 + 16], c2[4096 + 16], p1[4096], p2[4096];
  int rounds = 2000, refusedKeys = 0;
  for (int t = 0; t < rounds; t++) {
    size_t n = (size_t)(rand() % 4096), adn = (size_t)(rand() % 64);
    uint8_t ad[64], seed[32], k[32], xn[24], a[32], b[32];
    fill(m, n); fill(ad, adn); fill(seed, 32); fill(k, 32); fill(xn, 24);
    uint64_t nn = ((uint64_t)rand() << 32) | (uint64_t)rand();

    lq_sha256(a, m, n); crypto_hash_sha256(b, m, n);
    check("sha256", memcmp(a, b, 32) == 0);

    uint8_t pk1[32], sk1[64], pk2[32], sk2[64], s1[64], s2[64];
    lq_ed25519_keypair(pk1, sk1, seed); crypto_sign_ed25519_seed_keypair(pk2, sk2, seed);
    check("ed25519 keypair", memcmp(pk1, pk2, 32) == 0 && memcmp(sk1, sk2, 64) == 0);
    lq_ed25519_sign(s1, sk1, m, n); crypto_sign_ed25519_detached(s2, NULL, m, n, sk2);
    check("ed25519 sign", memcmp(s1, s2, 64) == 0);
    check("ed25519 verify", lq_ed25519_verify(s1, m, n, pk1) == 0);
    if (n > 0) {
      m[0] ^= 1;
      check("ed25519 refuses a changed message",
          lq_ed25519_verify(s1, m, n, pk1) != 0 && crypto_sign_ed25519_verify_detached(s1, m, n, pk2) != 0);
      m[0] ^= 1;
    }

    uint8_t x1[32], x2[32], q1[32], q2[32];
    lq_ed_sk_to_x(x1, sk1); crypto_sign_ed25519_sk_to_curve25519(x2, sk2);
    check("ed sk to x", memcmp(x1, x2, 32) == 0);
    int r1 = lq_ed_pk_to_x(x1, pk1), r2 = crypto_sign_ed25519_pk_to_curve25519(x2, pk2);
    check("ed pk to x", r1 == 0 && r2 == 0 && memcmp(x1, x2, 32) == 0);
    // A random 32 bytes is often not a point: both must refuse it alike.
    uint8_t junk[32]; fill(junk, 32);
    r1 = lq_ed_pk_to_x(x1, junk); r2 = crypto_sign_ed25519_pk_to_curve25519(x2, junk);
    check("ed pk to x refuses alike", (r1 == 0) == (r2 == 0) && (r1 != 0 || memcmp(x1, x2, 32) == 0));
    refusedKeys += r1 != 0;

    lq_x25519_base(q1, k); crypto_scalarmult_base(q2, k);
    check("x25519 base", memcmp(q1, q2, 32) == 0);
    r1 = lq_x25519(a, seed, q1); r2 = crypto_scalarmult(b, seed, q2);
    check("x25519", r1 == 0 && r2 == 0 && memcmp(a, b, 32) == 0);

    unsigned long long clen;
    lq_chachapoly_seal(c1, k, nn, ad, adn, m, n);
    uint8_t npub[12] = {0};
    for (int i = 0; i < 8; i++) npub[4 + i] = (uint8_t)(nn >> (8 * i));
    crypto_aead_chacha20poly1305_ietf_encrypt(c2, &clen, m, n, ad, adn, NULL, npub, k);
    check("chachapoly seal", clen == n + 16 && memcmp(c1, c2, n + 16) == 0);
    check("chachapoly open", lq_chachapoly_open(p1, k, nn, ad, adn, c2, n + 16) == 0 && memcmp(p1, m, n) == 0);
    c1[(size_t)rand() % (n + 16)] ^= 0x40;
    check("chachapoly refuses a changed frame", lq_chachapoly_open(p1, k, nn, ad, adn, c1, n + 16) != 0);

    lq_xchacha_seal(c1, k, xn, ad, adn, m, n);
    crypto_aead_xchacha20poly1305_ietf_encrypt(c2, &clen, m, n, ad, adn, NULL, xn, k);
    check("xchacha seal", clen == n + 16 && memcmp(c1, c2, n + 16) == 0);
    unsigned long long plen;
    check("xchacha open", lq_xchacha_open(p1, k, xn, ad, adn, c2, n + 16) == 0 &&
        crypto_aead_xchacha20poly1305_ietf_decrypt(p2, &plen, NULL, c1, n + 16, ad, adn, xn, k) == 0 &&
        memcmp(p1, m, n) == 0 && memcmp(p2, m, n) == 0);
    c1[(size_t)rand() % (n + 16)] ^= 0x40;
    check("xchacha refuses a changed frame", lq_xchacha_open(p1, k, xn, ad, adn, c1, n + 16) != 0);
    if (adn > 0) {
      ad[0] ^= 1;
      check("xchacha refuses another session's ad", lq_xchacha_open(p1, k, xn, ad, adn, c2, n + 16) != 0);
    }
  }
  // A small-order key: both refuse the conversion, and its DH is refused.
  uint8_t ident[32] = {1}, x[32], q[32], sk[32];
  fill(sk, 32);
  check("small-order ed key refused", lq_ed_pk_to_x(x, ident) != 0 && crypto_sign_ed25519_pk_to_curve25519(x, ident) != 0);
  uint8_t zero[32] = {0};
  check("all-zero DH refused", lq_x25519(q, sk, zero) != 0 && crypto_scalarmult(q, sk, zero) != 0);
  uint8_t r1[32] = {0}, r2[32] = {0};
  check("random bytes", lq_random(r1, 32) == 0 && lq_random(r2, 32) == 0 && memcmp(r1, r2, 32) != 0);
  printf("crypto compat: %d rounds (%d junk keys refused alike), %d failed\n", rounds, refusedKeys, bad);
  return bad != 0;
}
