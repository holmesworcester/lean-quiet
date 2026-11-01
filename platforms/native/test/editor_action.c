#include <stdlib.h>
#include <stddef.h>
static int fail_site=-1;
static unsigned allocations[3];
static void *test_alloc(size_t n,unsigned site) {
  if(site<3)allocations[site]++;
  return fail_site==(int)site?NULL:malloc(n);
}
#define LQ_EDITOR_ALLOC(n,site) test_alloc(n,site)
#include "../editor_action.h"
#include <stdio.h>
static int failures,checks;
#define CHECK(name, value) do { checks++;if(!(value)){fprintf(stderr,"FAIL editor-action: %s\n",name);failures++;}}while(0)
int main(void) {
  LqEditorAction s={0};uint32_t pos[4]={1,1,0,0};char latest[8]="A";
  CHECK("admission owns actual immutable bytes",lq_action_admit(&s,7,11,100,latest,1,pos,true)==0);
  uint64_t first=s.ticket;latest[0]='B';
  CHECK("later typing cannot replace captured Send",s.length==1&&s.text[0]=='A'&&s.revision==11&&s.owner==7);
  CHECK("busy refuses without replacing accepted action",lq_action_admit(&s,7,12,100,latest,1,pos,true)==LQ_ACTION_BUSY&&s.ticket==first&&s.text[0]=='A');
  CHECK("stale cleanup cannot release accepted action",!lq_action_finish(&s,first+1,2)&&s.ticket==first);
  CHECK("consumed action owns asynchronous clear",lq_action_finish(&s,first,3)&&s.clearing);
  CHECK("logical consumption is exact owner and revision",lq_action_consumed(&s,7,11)&&!lq_action_consumed(&s,7,12)&&!lq_action_consumed(&s,8,11));
  CHECK("duplicate cleanup cannot steal pending clear",!lq_action_finish(&s,first,1)&&s.clearing);
  CHECK("busy remains explicit while clear callback pending",lq_action_admit(&s,7,12,100,latest,1,pos,true)==LQ_ACTION_BUSY);
  lq_action_clear_done(&s,first+1);
  CHECK("unrelated completion cannot release clear",s.ticket==first);
  lq_action_clear_done(&s,first);
  CHECK("actual completion records consumed disposition",!s.ticket&&s.last_ticket==first&&s.last_disposition==4);
  CHECK("consumed text cannot resurrect after clear completion",lq_action_consumed(&s,7,11));
  CHECK("consumed raw text cannot be readmitted after failed clear",lq_action_admit(&s,7,11,100,latest,1,pos,true)==LQ_ACTION_STALE&&!s.ticket);
  CHECK("newer draft can be admitted after completion",lq_action_admit(&s,7,12,100,latest,1,pos,true)==0&&s.ticket>first&&s.text[0]=='B');
  uint64_t next=s.ticket;lq_action_retire(&s);
  CHECK("revoke has an explicit terminal receipt",!s.ticket&&s.last_ticket==next&&s.last_disposition==5);
  CHECK("revoke preserves prior consumed marker but not newer text",lq_action_consumed(&s,7,11)&&!lq_action_consumed(&s,7,12));
  CHECK("uninstalled editor refuses",lq_action_admit(&s,7,12,100,latest,1,pos,false)==LQ_ACTION_STALE);
  CHECK("zero owner never aliases a real editor",lq_action_admit(&s,0,12,100,latest,1,pos,true)==LQ_ACTION_STALE);
  char unicode[]={ 'A',0,(char)0xf0,(char)0x9f,(char)0x98,(char)0x80,'B' };
  CHECK("snapshot preserves NUL and supplementary UTF8 bytes",lq_action_admit(&s,8,1,100,unicode,sizeof unicode,pos,true)==0&&s.length==sizeof unicode&&!memcmp(s.text,unicode,sizeof unicode));
  lq_action_retire(&s);
  char *large=malloc(LQ_ACTION_MAX+1u);if(!large)return 2;memset(large,'x',LQ_ACTION_MAX+1u);
  CHECK("existing exact frame byte bound is accepted",lq_action_admit(&s,8,2,100,large,LQ_ACTION_MAX,pos,true)==0&&s.length==LQ_ACTION_MAX);
  lq_action_retire(&s);uint64_t before=s.next;
  unsigned allocated=allocations[0];
  CHECK("oversize is refused before snapshot allocation or ticket advance",lq_action_admit(&s,8,3,100,large,LQ_ACTION_MAX+1u,pos,true)==LQ_ACTION_LARGE&&!s.ticket&&!s.text&&s.next==before);
  CHECK("oversize did not invoke allocator",allocations[0]==allocated);
  free(large);
  fail_site=0;
  CHECK("admission allocation failure explicitly refuses without consuming ticket",lq_action_admit(&s,8,4,100,latest,1,pos,true)==LQ_ACTION_MEMORY&&!s.ticket&&!s.text&&s.next==before);
  fail_site=-1;
  CHECK("slot recovers after allocation failure",lq_action_admit(&s,8,4,101,latest,1,pos,true)==0&&s.content==101);
  uint64_t owned=s.ticket;
  fail_site=2;char *copy=lq_editor_copy(s.text,s.length,2);
  CHECK("snapshot read failure cannot mutate or retire accepted action",copy==NULL&&s.ticket==owned&&s.length==1&&s.text[0]=='B');
  fail_site=1;copy=lq_editor_copy(latest,1,1);
  CHECK("latest text copy failure is distinguishable from empty text",copy==NULL&&latest[0]=='B');
  fail_site=-1;copy=lq_editor_copy(s.text,s.length,2);
  CHECK("snapshot read recovers exact captured bytes",copy&&copy[0]=='B'&&copy[1]==0&&s.ticket==owned);free(copy);
  CHECK("consumption of newer draft moves exact marker",lq_action_finish(&s,owned,3)&&lq_action_consumed(&s,8,4)&&!lq_action_consumed(&s,7,11));
  lq_action_retire(&s);
  CHECK("background retirement keeps consumed revision",!s.ticket&&lq_action_consumed(&s,8,4));
  lq_action_clear_done(&s,owned);
  CHECK("late clear callback cannot erase persistent consumption",!s.ticket&&lq_action_consumed(&s,8,4));
  s.next=UINT64_MAX;
  CHECK("ticket exhaustion never wraps or admits",lq_action_admit(&s,8,5,100,latest,1,pos,true)==LQ_ACTION_EXHAUSTED&&!s.ticket);
  printf("editor-action: %d passed, %d failed\n",checks-failures,failures);return failures?1:0;
}
