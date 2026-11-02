set pagination off
set confirm off
set debuginfod enabled off
break main
run
python
# Lean 4.35.0's getter takes the value (one xchg with null), then restores
# it on one of two paths (scalar or single-threaded, and thread-shared):
# pause at either restore. Only the getter's own bytes are read.
text = gdb.execute('disassemble lean_st_ref_get', to_string=True)
exchanges = [int(l.replace('=>', '').split()[0], 16) for l in text.splitlines() if 'xchg' in l and '0x8(%rdi)' in l]
if len(exchanges) != 3:
    raise gdb.GdbError('pinned SDK getter layout changed; review the interleaving fixture')
for addr in exchanges[1:]:
    bp = gdb.Breakpoint('*' + hex(addr))
    bp.condition = 'lq_stop_probe_ref != 0 && $rdi == lq_stop_probe_ref'
end
continue
printf "SDK getter paused before restoring its old value\n"
call lq_stop_probe_release()
disable 2 3
# Catch the actual Linux exit status before concurrent worker teardown confuses
# GDB's child reaping ("No unwaited-for children left").
catch syscall exit_group
continue
set $status = $rdi
printf "publication probe exit_group status=%d\n", $status
quit $status
