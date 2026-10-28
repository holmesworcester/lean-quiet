import engine.wire.mdns.Mdns
open Mdns
def showName (n : Name) : String := ".".intercalate (n.map fun l => String.fromUTF8! ⟨l.toArray⟩)
def main (args : List String) : IO Unit := do
  for f in args do
    let p ← IO.FS.readBinFile f
    match decode p with
    | none => IO.println s!"{f}: NONE"
    | some m =>
      IO.println s!"{f}: q={m.questions.length} an={m.answers.length} au={m.authority.length} ad={m.additional.length} rt={decode (encode m) == some m}"
      for r in m.answers ++ m.additional do
        IO.println s!"   {showName r.name} {repr r.data |>.pretty 200 |>.take 100}"
