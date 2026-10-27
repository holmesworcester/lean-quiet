// SQLite and Ed25519 for Lean. SQLite statements take blob parameters
// and return every column as bytes; libsodium (linked from its shared
// library, whose headers this box lacks) supplies Ed25519 and SHA-256.
#include <lean/lean.h>
#include <sqlite3.h>
#include <string.h>

// ---- libsodium, declared by hand -------------------------------------------
int sodium_init(void);
int crypto_hash_sha256(unsigned char* out, const unsigned char* in, unsigned long long n);
int crypto_sign_ed25519_seed_keypair(unsigned char* pk, unsigned char* sk, const unsigned char* seed);
int crypto_sign_ed25519_detached(unsigned char* sig, unsigned long long* siglen,
  const unsigned char* m, unsigned long long mlen, const unsigned char* sk);
int crypto_sign_ed25519_verify_detached(const unsigned char* sig, const unsigned char* m,
  unsigned long long mlen, const unsigned char* pk);

static lean_obj_res bytes(const void* p, size_t n) {
  lean_object* b = lean_alloc_sarray(1, n, n);
  if (n) memcpy(lean_sarray_cptr(b), p, n);
  return b;
}

static lean_obj_res io_error(const char* msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

LEAN_EXPORT lean_obj_res le_sha256(b_lean_obj_arg in) {
  unsigned char out[32];
  crypto_hash_sha256(out, lean_sarray_cptr(in), lean_sarray_size(in));
  return bytes(out, 32);
}

// seed (32 bytes) -> pk (32) ++ sk (64)
LEAN_EXPORT lean_obj_res le_ed25519_keypair(b_lean_obj_arg seed) {
  unsigned char pk[32], sk[64], out[96];
  if (lean_sarray_size(seed) != 32) return bytes(out, 0);
  sodium_init();
  crypto_sign_ed25519_seed_keypair(pk, sk, lean_sarray_cptr(seed));
  memcpy(out, pk, 32);
  memcpy(out + 32, sk, 64);
  return bytes(out, 96);
}

LEAN_EXPORT lean_obj_res le_ed25519_sign(b_lean_obj_arg sk, b_lean_obj_arg msg) {
  unsigned char sig[64];
  if (lean_sarray_size(sk) != 64) return bytes(sig, 0);
  crypto_sign_ed25519_detached(sig, NULL, lean_sarray_cptr(msg), lean_sarray_size(msg),
    lean_sarray_cptr(sk));
  return bytes(sig, 64);
}

LEAN_EXPORT uint8_t le_ed25519_verify(b_lean_obj_arg pk, b_lean_obj_arg msg, b_lean_obj_arg sig) {
  if (lean_sarray_size(pk) != 32 || lean_sarray_size(sig) != 64) return 0;
  return crypto_sign_ed25519_verify_detached(lean_sarray_cptr(sig), lean_sarray_cptr(msg),
    lean_sarray_size(msg), lean_sarray_cptr(pk)) == 0;
}

// ---- SQLite ------------------------------------------------------------------

static lean_external_class* db_class;

static void db_finalize(void* p) { sqlite3_close_v2((sqlite3*)p); }
static void db_foreach(void* p, b_lean_obj_arg f) { (void)p; (void)f; }

static sqlite3* db_of(b_lean_obj_arg o) { return (sqlite3*)lean_get_external_data(o); }

LEAN_EXPORT lean_obj_res le_sql_open(b_lean_obj_arg path) {
  if (db_class == NULL) db_class = lean_register_external_class(db_finalize, db_foreach);
  sqlite3* db;
  if (sqlite3_open(lean_string_cstr(path), &db) != SQLITE_OK) {
    lean_obj_res e = io_error(sqlite3_errmsg(db));
    sqlite3_close_v2(db);
    return e;
  }
  sqlite3_busy_timeout(db, 5000);
  return lean_io_result_mk_ok(lean_alloc_external(db_class, db));
}

LEAN_EXPORT lean_obj_res le_sql_exec(b_lean_obj_arg o, b_lean_obj_arg sql) {
  char* err = NULL;
  if (sqlite3_exec(db_of(o), lean_string_cstr(sql), NULL, NULL, &err) != SQLITE_OK) {
    lean_obj_res e = io_error(err ? err : "sqlite exec failed");
    sqlite3_free(err);
    return e;
  }
  return lean_io_result_mk_ok(lean_box(0));
}

// One statement, its parameters bound as blobs; every row, every column
// as bytes (NULL as empty).
LEAN_EXPORT lean_obj_res le_sql_query(b_lean_obj_arg o, b_lean_obj_arg sql, b_lean_obj_arg args) {
  sqlite3*      db = db_of(o);
  sqlite3_stmt* st;
  if (sqlite3_prepare_v2(db, lean_string_cstr(sql), -1, &st, NULL) != SQLITE_OK) {
    return io_error(sqlite3_errmsg(db));
  }
  size_t n = lean_array_size(args);
  for (size_t i = 0; i < n; i++) {
    lean_object* a = lean_array_get_core(args, i);
    sqlite3_bind_blob(st, (int)i + 1, lean_sarray_cptr(a), (int)lean_sarray_size(a), SQLITE_TRANSIENT);
  }
  lean_object* rows = lean_mk_empty_array();
  int rc;
  while ((rc = sqlite3_step(st)) == SQLITE_ROW) {
    int cols = sqlite3_column_count(st);
    lean_object* row = lean_mk_empty_array();
    for (int c = 0; c < cols; c++) {
      const void* p = sqlite3_column_blob(st, c);
      int len = sqlite3_column_bytes(st, c);
      row = lean_array_push(row, bytes(p, p ? (size_t)len : 0));
    }
    rows = lean_array_push(rows, row);
  }
  if (rc != SQLITE_DONE) {
    lean_obj_res e = io_error(sqlite3_errmsg(db));
    sqlite3_finalize(st);
    lean_dec(rows);
    return e;
  }
  sqlite3_finalize(st);
  return lean_io_result_mk_ok(rows);
}
