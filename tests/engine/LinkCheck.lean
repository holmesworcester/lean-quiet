/-
The invite link, as it is used: an inviter issues an invitation and its
link; the text (the join page link) or the URI the page opens is
pasted (whole, broken across lines, without the page or the scheme)
or garbled; the joiner's request composed from the parsed link
is judged by the engine with real Ed25519, and is approved and admitted.
Every truncation, garbage text and 20,000 mutated links either parse to
a valid invite or are refused.
-/
import tests.engine.Lib

open Engine Community Tests

/-- `--print`: two invites' links and URIs only (site/test.py and the
Android link e2e use them); `--print-device`: a device link and its URI. -/
def main (args : List String) : IO UInt32 := do
  let t ← Checks.new
  let f := Device.named "founder"
  let j := Device.named "joiner"
  let r := root f (keyOf f) .empty
  let c := r.id
  let secret := sha256 "bearer seed".toUTF8
  let (inv, link) := issue c c f (keyOf f) secret ["192.168.4.77:7001".toUTF8]
  let text := link.text
  if args == ["--print"] then
    -- two invitations of the community: their links, then their URIs
    let (_, other) := issue c c f (keyOf f) (sha256 "second seed".toUTF8) ["192.168.4.77:7001".toUTF8]
    IO.println text; IO.println other.text; IO.println link.uri; IO.println other.uri; return 0
  let (dinv, dlink) := issue c c f (keyOf f) (sha256 "device seed".toUTF8) ["192.168.4.77:7001".toUTF8] (link := true)
  if args == ["--print-device"] then
    IO.println dlink.text; IO.println dlink.uri; return 0
  IO.println s!"link: {text.length} characters"
  t.ok "the link is valid" (decide link.Valid)
  t.ok "it reads as the join page, the fields after #"
    (text.startsWith "https://holmesworcester.github.io/lean-quiet/join#")
  t.ok "it parses back" (Invite.parse text == some link)
  let uri := link.uri
  t.ok "the page opens leanquiet://join/ and the same fields"
    (uri.startsWith "leanquiet://join/" && uri.drop 17 == text.drop 50)
  t.ok "the URI parses back" (Invite.parse uri == some link)
  let broken := String.ofList ((text.toList.zipIdx.flatMap fun (ch, k) =>
    if k % 37 == 36 then ['\n', ' ', ch] else [ch]))
  t.ok "broken across lines, it still parses" (Invite.parse broken == some link)
  t.ok "without the page, it parses" (Invite.parse (String.ofList (text.toList.drop 50)) == some link)
  t.ok "the URI broken across lines parses" (Invite.parse (uri.replace "/join/" "/join/\n") == some link)
  t.ok "with spaces around, it parses" (Invite.parse ("  " ++ text ++ "\n") == some link)
  -- Truncations and garbage: refused, or (never seen) another valid invite.
  let mut odd := 0
  for n in [0:text.length] do
    match Invite.parse (String.ofList (text.toList.take n)) with
    | some i => if i == link || !decide i.Valid then odd := odd + 1
    | none => pure ()
  t.ok "no truncation parses to the link or to anything invalid" (odd == 0)
  -- The old scheme, another site's page and a query instead of a fragment are not links.
  let code := (text.drop 50).toString
  for g in ["", "leanquiet://join/", "leanquiet://join/!!!", "hello", "leanquiet://join/0",
      "https://holmesworcester.github.io/lean-quiet/join#", "quiet://join/" ++ code,
      "https://example.com/join#" ++ code, "https://holmesworcester.github.io/lean-quiet/join?" ++ code,
      String.ofList (List.replicate 5000 'z')] do
    t.ok s!"garbage refused: {g.take 52}" (Invite.parse g == none)
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
  let adm := admit c req.id ok.id
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
  -- A device link: its own page and scheme, the same fields, kind 2.
  let dtext := dlink.text
  let dcode := (dtext.drop 50).toString
  t.ok "a device link reads as the link page" (dtext.startsWith "https://holmesworcester.github.io/lean-quiet/link#")
  t.ok "and parses back, a device link" (Invite.parse dtext == some dlink && dlink.link)
  t.ok "its URI is leanquiet://link/ and the same fields"
    (dlink.uri == "leanquiet://link/" ++ dcode && Invite.parse dlink.uri == some dlink)
  t.ok "its bare code parses, a device link" (Invite.parse dcode == some dlink)
  t.ok "behind the join page it is refused (parse_other_kind)"
    (Invite.parse ("https://holmesworcester.github.io/lean-quiet/join#" ++ dcode) == none &&
     Invite.parse ("leanquiet://join/" ++ dcode) == none)
  t.ok "and a member's link behind the link page"
    (Invite.parse ("https://holmesworcester.github.io/lean-quiet/link#" ++ code) == none &&
     Invite.parse ("leanquiet://link/" ++ code) == none)
  let dcs := dtext.toList.toArray
  let mut flipped := 0
  for _ in [0:5000] do
    let (i, g1) := g.below dcs.size
    let (k, g2) := g1.below 62
    g := g2
    match Invite.parse (String.ofList (dcs.set! i (Base62.charOf k)).toList) with
    | some inv' =>
      if !decide inv'.Valid then t.ok "a device link mutant parsed to an invalid invite" false
      if !inv'.link then flipped := flipped + 1
    | none => pure ()
  t.ok s!"no mutant of the device link page parses to a member's link ({flipped})" (flipped == 0)
  -- The engine: a device link's request names the issuer's user; another
  -- member's approval of it is invalid, the issuer's admits the device
  -- into the issuer's user.
  let some dparsed := Invite.parse dtext | t.ok "parse" false; return 1
  let f2 := Device.named "founder-2"
  let dreq := dparsed.request f2 (keyOf f2)
  let a1 := Device.named "alice"
  let invA := invite c c f (Device.named "bearer-a").pk false
  let reqA := request c invA.id a1 (keyOf a1) (Device.named "bearer-a").sk
  let okA := approve c reqA.id c f
  let admA := admit c reqA.id okA.id
  let byAlice := approve c dreq.id admA.id a1
  let byFounder := approve c dreq.id c f
  let dadm := admit c dreq.id byFounder.id
  let m3 := modelRun fam [r, inv, invA, reqA, okA, admA, dinv, dreq, byAlice, byFounder, dadm]
  let valid3 (o : Op) := match m3.status o.id with | some (.valid _) => true | _ => false
  t.ok "the device link's request is valid" (valid3 dreq)
  t.ok "another user's approval of it is invalid (link_approved_by_issuer)" (m3.status byAlice.id == some .invalid)
  t.ok "the issuer's approval admits it" (valid3 byFounder && valid3 dadm)
  t.ok "into the issuer's user (link_admits_issuer)"
    (match m3.status dadm.id with | some (.valid (.admission _ u _ _ _)) => u == c | _ => false)
  t.finish "linkcheck"
