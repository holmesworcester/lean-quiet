/-
The invite link, as it is used: an inviter issues an invitation and its
link; the text is pasted (whole, broken across lines, without the
scheme) or garbled; the joiner's request composed from the parsed link
is judged by the engine with real Ed25519, and is approved and admitted.
Every truncation, garbage text and 20,000 mutated links either parse to
a valid invite or are refused.
-/
import tests.engine.Lib

open Engine Community Tests

def main : IO UInt32 := do
  let t ← Checks.new
  let f := Device.named "founder"
  let j := Device.named "joiner"
  let r := root f (keyOf f)
  let c := r.id
  let secret := sha256 "bearer seed".toUTF8
  let (inv, link) := issue c c f (keyOf f) secret ["192.168.4.77:7001".toUTF8]
  let text := link.text
  IO.println s!"link: {text.length} characters"
  t.ok "the link is valid" (decide link.Valid)
  t.ok "it reads as quiet://join/…" (text.startsWith "quiet://join/")
  t.ok "it parses back" (Invite.parse text == some link)
  let broken := String.ofList ((text.toList.zipIdx.flatMap fun (ch, k) =>
    if k % 37 == 36 then ['\n', ' ', ch] else [ch]))
  t.ok "broken across lines, it still parses" (Invite.parse broken == some link)
  t.ok "without the scheme, it parses" (Invite.parse (String.ofList (text.toList.drop 13)) == some link)
  t.ok "with spaces around, it parses" (Invite.parse ("  " ++ text ++ "\n") == some link)
  -- Truncations and garbage: refused, or (never seen) another valid invite.
  let mut odd := 0
  for n in [0:text.length] do
    match Invite.parse (String.ofList (text.toList.take n)) with
    | some i => if i == link || !decide i.Valid then odd := odd + 1
    | none => pure ()
  t.ok "no truncation parses to the link or to anything invalid" (odd == 0)
  for g in ["", "quiet://join/", "quiet://join/!!!", "hello", "quiet://join/0", String.ofList (List.replicate 5000 'z')] do
    t.ok s!"garbage refused: {g.take 20}" (Invite.parse g == none)
  -- Mutations: whatever parses is valid (parse_valid, on the compiled code).
  let mut g := Rng.mk 99
  let mut accepted := 0
  let cs := text.toList.toArray
  for _ in [0:20000] do
    let (i, g1) := g.below cs.size
    let (k, g2) := g1.below 62
    g := g2
    let m := cs.set! i (Base62.charOf k)
    match Invite.parse (String.ofList m.toList) with
    | some inv' =>
      accepted := accepted + 1
      if !decide inv'.Valid then t.ok "a mutant parsed to an invalid invite" false
    | none => pure ()
  IO.println s!"mutants: 20000, {accepted} parsed (all valid)"
  -- The engine: the request composed from the parsed link is Valid, and
  -- with an approval it admits the joiner.
  let some parsed := Invite.parse text | t.ok "parse" false; return 1
  let req := parsed.request j (keyOf j)
  let ok := approve c req.id c f
  let adm := admit c req.id [ok.id]
  let fam := family ed25519
  let m := modelRun fam [r, inv, req, ok, adm]
  let valid (o : Op) := match m.status o.id with | some (.valid _) => true | _ => false
  t.ok "the request from the link is valid" (valid req)
  t.ok "approved, it admits the joiner" (valid adm && (allowPeer c (keyOf j)).eval m)
  -- A link with another seed: its request fails the bearer check.
  let forged := { parsed with secret := sha256 "another seed".toUTF8 }
  let m2 := modelRun fam [r, inv, forged.request j (keyOf j)]
  t.ok "a request from a link with the wrong seed is invalid"
    (m2.status (forged.request j (keyOf j)).id == some .invalid)
  t.finish "linkcheck"
