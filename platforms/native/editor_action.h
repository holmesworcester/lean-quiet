/* One owned semantic candidate. Callers serialize every operation. The latest
 * editor text is separate: this bounded snapshot cannot be changed by typing.
 * Ticket/owner zero are never admitted; exhaustion never reuses a ticket. */
#ifndef LQ_EDITOR_ACTION_H
#define LQ_EDITOR_ACTION_H
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#define LQ_ACTION_MAX (1024u * 1024u)
enum { LQ_ACTION_OK=0, LQ_ACTION_BUSY=1, LQ_ACTION_STALE=2,
       LQ_ACTION_LARGE=3, LQ_ACTION_EXHAUSTED=4, LQ_ACTION_MEMORY=5 };
typedef struct {
  uint64_t next, ticket, owner, revision, content, last_ticket;
  uint64_t consumed_owner, consumed_revision;
  uint32_t last_disposition;
  size_t length;
  uint32_t pos[4];
  char *text;
  bool clearing;
} LqEditorAction;
#ifndef LQ_EDITOR_ALLOC
#define LQ_EDITOR_ALLOC(n,site) malloc(n)
#endif
/* The same checked copy is used for admission and both read paths. A caller
 * must report NULL as failure, never as a successful empty payload. */
static inline char *lq_editor_copy(const char *text,size_t n,unsigned site) {
  (void)site;
  char *copy=LQ_EDITOR_ALLOC(n+1u,site);
  if(copy){if(n)memcpy(copy,text,n);copy[n]=0;}return copy;
}
static inline bool lq_action_consumed(const LqEditorAction *s,uint64_t owner,uint64_t revision) {
  return owner&&revision&&owner==s->consumed_owner&&revision==s->consumed_revision;
}
static inline void lq_action_release(LqEditorAction *s) {
  free(s->text);s->text=NULL;s->ticket=0;s->owner=0;s->revision=0;s->length=0;s->clearing=false;
}
static inline void lq_action_retire(LqEditorAction *s) {
  if(s->ticket){s->last_ticket=s->ticket;s->last_disposition=5;}
  lq_action_release(s);
}
static inline uint32_t lq_action_admit(LqEditorAction *s,uint64_t owner,uint64_t revision,uint64_t content,
    const char *text,size_t n,const uint32_t pos[4],bool ready) {
  if(!ready||!owner||!revision)return LQ_ACTION_STALE;
  if(s->ticket)return LQ_ACTION_BUSY;
  if(lq_action_consumed(s,owner,revision))return LQ_ACTION_STALE;
  if(s->next==UINT64_MAX)return LQ_ACTION_EXHAUSTED;
  if(n>LQ_ACTION_MAX)return LQ_ACTION_LARGE;
  char *copy=lq_editor_copy(text,n,0);if(!copy)return LQ_ACTION_MEMORY;
  s->ticket=++s->next;s->owner=owner;s->revision=revision;s->content=content;s->text=copy;s->length=n;
  memcpy(s->pos,pos,sizeof s->pos);s->clearing=false;return LQ_ACTION_OK;
}
/* Stale or duplicate receipts cannot release another incarnation. */
static inline bool lq_action_finish(LqEditorAction *s,uint64_t ticket,uint32_t disposition) {
  if(!ticket||s->ticket!=ticket||s->clearing)return false;
  if(disposition==3){s->clearing=true;s->consumed_owner=s->owner;s->consumed_revision=s->revision;}else {s->last_ticket=ticket;s->last_disposition=disposition;lq_action_release(s);}
  return true;
}
static inline void lq_action_clear_done(LqEditorAction *s,uint64_t ticket) {
  if(ticket&&s->ticket==ticket&&s->clearing) {s->last_ticket=ticket;s->last_disposition=4;lq_action_release(s);}
}
#endif
