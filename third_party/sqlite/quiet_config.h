// SQLite options shared by Lake, Android and iOS. Keep the amalgamation
// itself untouched; each build includes this before compiling sqlite3.c.
#define SQLITE_THREADSAFE 2
#define SQLITE_DQS 0
#define SQLITE_DEFAULT_MEMSTATUS 0
#define SQLITE_OMIT_LOAD_EXTENSION
