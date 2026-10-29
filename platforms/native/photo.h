#ifndef LQ_PHOTO_H
#define LQ_PHOTO_H
/* One owned, bounded picker result. Both native platforms call this core.
 * UI callbacks may finish after cancellation or a newer request. */
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

typedef struct {
  pthread_mutex_t mutex;
  uint32_t token, status, width, height;
  unsigned char *bytes;
  size_t size;
} LqPhoto;
#define LQ_PHOTO_INIT {PTHREAD_MUTEX_INITIALIZER, 0, 0, 0, 0, NULL, 0}

static void lq_photo_begin(LqPhoto *p, uint32_t token) {
  pthread_mutex_lock(&p->mutex);
  free(p->bytes);
  p->bytes = NULL; p->size = 0; p->status = 0;
  p->width = p->height = 0; p->token = token;
  pthread_mutex_unlock(&p->mutex);
}

static bool lq_photo_current(LqPhoto *p, uint32_t token) {
  pthread_mutex_lock(&p->mutex);
  bool current = token && p->token == token && !p->status;
  pthread_mutex_unlock(&p->mutex);
  return current;
}

/* 1 = RGBA success, 2 = cancelled, 3 = unavailable/failed. First result wins. */
static bool lq_photo_publish(LqPhoto *p, uint32_t token, uint32_t status,
    uint32_t w, uint32_t h, const unsigned char *bytes, size_t size) {
  if (!token || status < 1 || status > 3) return false;
  if (status == 1 && (!w || !h || w > 2048 || h > 2048 || !bytes || size != (size_t)w*h*4)) return false;
  pthread_mutex_lock(&p->mutex);
  if (p->token != token || p->status) { pthread_mutex_unlock(&p->mutex); return false; }
  if (status == 1) {
    p->bytes = malloc(size);
    if (p->bytes) { memcpy(p->bytes, bytes, size); p->size = size; }
    else status = 3;
  }
  p->status = status; p->width = status == 1 ? w : 0; p->height = status == 1 ? h : 0;
  pthread_mutex_unlock(&p->mutex);
  return true;
}

/* Transfers ownership, including zero-byte cancel/error completions. */
static bool lq_photo_take(LqPhoto *p, uint32_t header[4], unsigned char **bytes, size_t *size) {
  pthread_mutex_lock(&p->mutex);
  bool ready = p->status != 0;
  *bytes = NULL; *size = 0;
  if (ready) {
    header[0] = p->token; header[1] = p->status; header[2] = p->width; header[3] = p->height;
    *bytes = p->bytes; *size = p->size;
    p->bytes = NULL; p->size = 0; p->status = 0; p->token = 0;
  }
  pthread_mutex_unlock(&p->mutex);
  return ready;
}
#endif
