// Host check: the vendored SHA-256 and Monocypher's Ed25519 give the same
// bytes as libsodium (the engine's host glue) for the same inputs.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "monocypher-ed25519.h"

void quiet_sha256(uint8_t out[32], const uint8_t* in, size_t n);
int sodium_init(void);
int crypto_hash_sha256(unsigned char* out, const unsigned char* in, unsigned long long n);
int crypto_sign_ed25519_seed_keypair(unsigned char* pk, unsigned char* sk, const unsigned char* seed);
int crypto_sign_ed25519_detached(unsigned char* sig, unsigned long long* siglen,
  const unsigned char* m, unsigned long long mlen, const unsigned char* sk);
int crypto_sign_ed25519_verify_detached(const unsigned char* sig, const unsigned char* m,
  unsigned long long mlen, const unsigned char* pk);

int main(void) {
  sodium_init();
  srand(7);
  uint8_t buf[1000];
  int bad = 0;
  for (int t = 0; t < 300; t++) {
    size_t n = (size_t)(t * 7 % 1000);
    for (size_t i = 0; i < n; i++) buf[i] = (uint8_t)rand();
    uint8_t a[32], b[32];
    quiet_sha256(a, buf, n);
    crypto_hash_sha256(b, buf, n);
    bad += memcmp(a, b, 32) != 0;
    uint8_t seed[32], s2[32], pk1[32], sk1[64], pk2[32], sk2[64], sig1[64], sig2[64];
    for (int i = 0; i < 32; i++) seed[i] = (uint8_t)rand();
    memcpy(s2, seed, 32);
    crypto_ed25519_key_pair(sk1, pk1, s2);
    crypto_sign_ed25519_seed_keypair(pk2, sk2, seed);
    bad += memcmp(pk1, pk2, 32) != 0 || memcmp(sk1, sk2, 64) != 0;
    crypto_ed25519_sign(sig1, sk1, buf, n);
    crypto_sign_ed25519_detached(sig2, NULL, buf, n, sk2);
    bad += memcmp(sig1, sig2, 64) != 0;
    bad += crypto_sign_ed25519_verify_detached(sig1, buf, n, pk2) != 0;
    bad += crypto_ed25519_check(sig2, pk1, buf, n) != 0;
    if (n > 0) { buf[0] ^= 1; bad += crypto_ed25519_check(sig2, pk1, buf, n) == 0; }
  }
  printf("compat: %s (%d mismatches over 300 cases)\n", bad ? "FAIL" : "ok", bad);
  return bad != 0;
}
