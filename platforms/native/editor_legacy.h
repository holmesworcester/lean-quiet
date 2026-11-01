#ifndef LQ_EDITOR_LEGACY_H
#define LQ_EDITOR_LEGACY_H
static lean_obj_res lq_editor_legacy(void) {
 lean_object *p=lean_alloc_ctor(0,2,0);lean_ctor_set(p,0,lean_mk_string(""));
 lean_ctor_set(p,1,lean_mk_empty_array());return lean_io_result_mk_ok(p);
}
lean_obj_res lq_editor(uint32_t mode,uint64_t owner,uint64_t rev,b_lean_obj_arg text) {
 (void)mode;(void)owner;(void)rev;(void)text;return lq_editor_legacy();
}
lean_obj_res lq_editor_action(uint64_t token,uint32_t disposition) {
 (void)token;(void)disposition;return lq_editor_legacy();
}
#endif
