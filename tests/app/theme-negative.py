#!/usr/bin/env python3
"""Deliberate source faults; restore every file even if a control fails."""
from pathlib import Path
import subprocess

out=Path('out/appearance/negative');out.mkdir(parents=True,exist_ok=True)
cases=[
 ('system','engine/renderer/Theme.lean','| .system => s.system','| .system => .light','Theme.follows'),
 ('forced','engine/renderer/Theme.lean','| .light => .light','| .light => .dark','Theme.forced'),
 ('roundtrip','engine/renderer/Theme.lean','| "light" => .light','| "light" => .dark','Theme.roundtrip'),
 ('selection','engine/renderer/Appearance.lean','def chosen (current choice : Theme.Setting) : Bool := current == choice','def chosen (_current _choice : Theme.Setting) : Bool := false','Appearance.selected_check'),
 ('srgb','engine/renderer/Contrast.lean','0, 303, 607','0, 0, 607','Contrast.channel_bounds'),
 ('contrast','engine/renderer/Contrast.lean','else if luminance ground ≥ 1800000000 then Palette.color .light .black','else if luminance ground ≥ 1800000000 then ground','Contrast.ink_meets / ink_control'),
 ('palette-ink','engine/renderer/Contrast.lean','if meets wanted ground then wanted','if meets wanted ground then ground','Contrast.ink_kept'),
 ('cue','engine/renderer/Cue.lean','| .selected => "✓"','| .selected => ""','Cue.nonempty'),
 ('cue-theme','engine/renderer/Cue.lean','def caption (_theme : Theme.Value) (s : State) : String := words s','def caption (theme : Theme.Value) (s : State) : String := if theme == .light then "" else words s','Cue.same'),
 ('overlap','engine/renderer/Overlay.lean','Contrast.ink (Palette.color theme .edge) under','Palette.color theme .edge','Overlay.edge_contrast'),
]
for name,file,old,new,law in cases:
 p=Path(file);original=p.read_text();assert old in original,(name,old)
 try:
  p.write_text(original.replace(old,new,1))
  got=subprocess.run(['lake','env','lean',file],capture_output=True,text=True,timeout=90)
  (out/(name+'.log')).write_text(got.stdout+got.stderr)
  assert got.returncode != 0, f'{name}: broken code passed'
  print(f'negative {name}: rejected ({law})',flush=True)
 finally:p.write_text(original)

# Rebuild the actual dependency so the laws cannot accidentally read an old .olean.
for name,old,new,law in [
 ('caches','rows := {}, imgs := {},','rows := s.rows, imgs := s.imgs,','ThemeLaws.cleared'),
 ('theme-palette','let dm := { dm with theme := Theme.effective theme }','let dm := { dm with theme := Theme.Value.dark }','ThemeLaws.palette'),
 ('content','theme := theme\n    dim := dm','theme := theme\n    text := ""\n    dim := dm','ThemeLaws.content'),
]:
 p=Path('App.lean');original=p.read_text();assert old in original
 try:
  p.write_text(original.replace(old,new,1))
  got=subprocess.run(['lake','build','engine.renderer.ThemeLaws'],capture_output=True,text=True,timeout=120)
  (out/(name+'.log')).write_text(got.stdout+got.stderr)
  assert got.returncode != 0 and 'ThemeLaws.lean:' in got.stdout+got.stderr, f'{name}: law did not reject'
  print(f'negative {name}: rejected ({law})',flush=True)
 finally:p.write_text(original)

# Restoring the source is not enough: restore all proof objects too.
subprocess.run(['lake','build','Quiet'],check=True,stdout=(out/'restored.log').open('w'))
print('13 negative controls rejected; all sources and proof objects restored',flush=True)
