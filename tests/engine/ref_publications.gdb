set pagination off
set confirm off
set debuginfod enabled off
break main
run
python
start = int(gdb.parse_and_eval('(void*)lean_st_ref_get'))
code = gdb.selected_inferior().architecture().disassemble(start, start + 150)
exchanges = [i for i in code if 'xchg' in i['asm'] and '0x8(%rdi)' in i['asm']]
if len(exchanges) != 2:
    raise gdb.GdbError('pinned SDK getter layout changed; review the interleaving fixture')
bp = gdb.Breakpoint('*' + hex(exchanges[1]['addr']))
bp.condition = 'lq_stop_probe_ref != 0 && $rdi == lq_stop_probe_ref'
end
continue
printf "SDK getter paused before restoring its old value\n"
call lq_stop_probe_release()
disable 2
# Catch the actual Linux exit status before concurrent worker teardown confuses
# GDB's child reaping ("No unwaited-for children left").
catch syscall exit_group
continue
set $status = $rdi
printf "publication probe exit_group status=%d\n", $status
quit $status
