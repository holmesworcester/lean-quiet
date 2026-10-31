// Exercise the production Lean wrappers when Rust refuses to encrypt.
// GNU ld wraps only the two seals: success delegates to the real Rust;
// failure writes a recognizable partial result and returns Err. No large
// allocation is needed to reproduce the ignored-return-code failure mode.
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

void lean_initialize_runtime_module(void);
lean_obj_res le_chachapoly_seal(b_lean_obj_arg k, uint64_t n,
    b_lean_obj_arg ad, b_lean_obj_arg p);
lean_obj_res le_chachapoly_open(b_lean_obj_arg k, uint64_t n,
    b_lean_obj_arg ad, b_lean_obj_arg c);
lean_obj_res le_xchacha_seal(b_lean_obj_arg k, b_lean_obj_arg n,
    b_lean_obj_arg ad, b_lean_obj_arg p);
lean_obj_res le_xchacha_open(b_lean_obj_arg k, b_lean_obj_arg n,
    b_lean_obj_arg ad, b_lean_obj_arg c);
int __real_lq_chachapoly_seal(uint8_t*, const uint8_t*, uint64_t,
    const uint8_t*, size_t, const uint8_t*, size_t);
int __real_lq_xchacha_seal(uint8_t*, const uint8_t*, const uint8_t*,
    const uint8_t*, size_t, const uint8_t*, size_t);

static int reject_chacha, reject_xchacha;
static unsigned chacha_calls, xchacha_calls, checks, failures;

int __wrap_lq_chachapoly_seal(uint8_t* out, const uint8_t* key, uint64_t nonce,
    const uint8_t* ad, size_t adlen, const uint8_t* p, size_t len) {
  chacha_calls++;
  if (!reject_chacha) return __real_lq_chachapoly_seal(out, key, nonce, ad, adlen, p, len);
  memset(out, 0xa5, len + 16);
  return -1;
}
int __wrap_lq_xchacha_seal(uint8_t* out, const uint8_t* key, const uint8_t* nonce,
    const uint8_t* ad, size_t adlen, const uint8_t* p, size_t len) {
  xchacha_calls++;
  if (!reject_xchacha) return __real_lq_xchacha_seal(out, key, nonce, ad, adlen, p, len);
  memset(out, 0xa5, len + 16);
  return -1;
}

static lean_object* repeated(size_t len, uint8_t byte) {
  lean_object* out = lean_alloc_sarray(1, len, len);
  memset(lean_sarray_cptr(out), byte, len);
  return out;
}
static void check(const char* label, int ok) {
  checks++;
  if (!ok) { failures++; if (failures <= 8) fprintf(stderr, "FAIL: %s\n", label); }
}
static void opened(const char* label, lean_object* result, lean_object* p) {
  int ok = !lean_is_scalar(result);
  if (ok) {
    lean_object* out = lean_ctor_get(result, 0);
    ok = lean_sarray_size(out) == lean_sarray_size(p) &&
      memcmp(lean_sarray_cptr(out), lean_sarray_cptr(p), lean_sarray_size(p)) == 0;
  }
  check(label, ok);
  lean_dec(result);
}

int main(void) {
  lean_initialize_runtime_module();
  lean_object* key = repeated(32, 7);
  lean_object* nonce = repeated(24, 9);
  lean_object* ad = repeated(11, 13);
  uint8_t expected[53];
  for (size_t len = 0; len <= 37; len += 37) {
    lean_object* p = repeated(len, 42);
    reject_chacha = reject_xchacha = 0;
    lean_object* c = le_chachapoly_seal(key, UINT64_MAX, ad, p);
    int rc = __real_lq_chachapoly_seal(expected, lean_sarray_cptr(key), UINT64_MAX,
      lean_sarray_cptr(ad), lean_sarray_size(ad), lean_sarray_cptr(p), len);
    check("ChaCha success preserves exact real Rust bytes", rc == 0 &&
      lean_sarray_size(c) == len + 16 && memcmp(lean_sarray_cptr(c), expected, len + 16) == 0);
    opened("ChaCha success opens original bytes", le_chachapoly_open(key, UINT64_MAX, ad, c), p);
    lean_dec_ref(c);
    c = le_xchacha_seal(key, nonce, ad, p);
    rc = __real_lq_xchacha_seal(expected, lean_sarray_cptr(key), lean_sarray_cptr(nonce),
      lean_sarray_cptr(ad), lean_sarray_size(ad), lean_sarray_cptr(p), len);
    check("XChaCha success preserves exact real Rust bytes", rc == 0 &&
      lean_sarray_size(c) == len + 16 && memcmp(lean_sarray_cptr(c), expected, len + 16) == 0);
    opened("XChaCha success opens original bytes", le_xchacha_open(key, nonce, ad, c), p);
    lean_dec_ref(c);
    reject_chacha = reject_xchacha = 1;
    for (unsigned i = 0; i < 32; i++) {
      c = le_chachapoly_seal(key, 5, ad, p);
      check("ChaCha Err exposes no allocated or partial ciphertext", lean_sarray_size(c) == 0);
      lean_dec_ref(c);
      c = le_xchacha_seal(key, nonce, ad, p);
      check("XChaCha Err exposes no allocated or partial ciphertext", lean_sarray_size(c) == 0);
      lean_dec_ref(c);
    }
    lean_dec_ref(p);
  }
  // Size guards refuse before calling either Rust function.
  lean_object* p = repeated(3, 21);
  for (size_t len = 31; len <= 33; len += 2) {
    lean_object* bad = repeated(len, 1);
    unsigned calls = chacha_calls;
    lean_object* c = le_chachapoly_seal(bad, 0, ad, p);
    check("wrong ChaCha key bypasses Rust", chacha_calls == calls && lean_sarray_size(c) == 0);
    lean_dec_ref(c);
    calls = xchacha_calls;
    c = le_xchacha_seal(bad, nonce, ad, p);
    check("wrong XChaCha key bypasses Rust", xchacha_calls == calls && lean_sarray_size(c) == 0);
    lean_dec_ref(c);
    lean_dec_ref(bad);
  }
  for (size_t len = 23; len <= 25; len += 2) {
    lean_object* bad = repeated(len, 1);
    unsigned calls = xchacha_calls;
    lean_object* c = le_xchacha_seal(key, bad, ad, p);
    check("wrong XChaCha nonce bypasses Rust", xchacha_calls == calls && lean_sarray_size(c) == 0);
    lean_dec_ref(c);
    lean_dec_ref(bad);
  }
  lean_dec_ref(p);
  lean_dec_ref(key);
  lean_dec_ref(nonce);
  lean_dec_ref(ad);
  printf("native seal failure injection: %u checks, %u failed\n", checks, failures);
  return failures ? 1 : 0;
}
