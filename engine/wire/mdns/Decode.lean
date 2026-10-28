/-
Decoding a DNS message from a packet's bytes.

Every function here is total and reads the packet only through `b[i]?`
and a size-checked `extract`, so there is no index it can get wrong and no
input on which it loops. A parser takes the position to read at and gives
back what it read and the position after it, or `none` for a malformed
packet; nothing here panics.

Compression (RFC 1035 §4.1.4): a name may end in a pointer to an earlier
name in the packet. `nameAt` follows a pointer only to a position before
the start of the run it is reading (`lim`), so each jump moves strictly
backwards and the pointer chain ends. Lean checks this: `nameAt` is
defined by well-founded recursion on `(lim, size - pos)`, not with fuel or
`partial`. A decoded name is also never longer than 255 wire bytes, so a
packet cannot inflate into names larger than any real one.
-/
import Mdns.Wire

namespace Mdns

variable (b : Array UInt8)

def u8 (i : Nat) : Option (Nat × Nat) :=
  match b[i]? with
  | some x => some (x.toNat, i + 1)
  | none => none

def u16 (i : Nat) : Option (Nat × Nat) := do
  let (h, i) ← u8 b i
  let (l, i) ← u8 b i
  pure (h * 256 + l, i)

def u32 (i : Nat) : Option (Nat × Nat) := do
  let (h, i) ← u16 b i
  let (l, i) ← u16 b i
  pure (h * 65536 + l, i)

/-- The `n` bytes at `i`. -/
def bytes (i n : Nat) : Option (List UInt8 × Nat) :=
  if i + n ≤ b.size then some ((b.extract i (i + n)).toList, i + n) else none

/-- The labels of the name at `pos`, and the position after it in the run
that started it (after the first pointer, if it jumped). `seen` is the
wire bytes of the labels read so far; `fin` the position to return once a
pointer has been followed. A pointer must aim before `lim`. -/
def nameAt (pos lim seen : Nat) (fin : Option Nat) : Option (Name × Nat) :=
  match h : b[pos]? with
  | none => none
  | some n =>
    if n.toNat = 0 then some ([], fin.getD (pos + 1))
    else if n.toNat < 64 then
      if seen + n.toNat + 2 ≤ 255 ∧ pos + 1 + n.toNat ≤ b.size then
        have : pos < b.size := by
          rcases Array.getElem?_eq_some_iff.mp h with ⟨hp, _⟩; exact hp
        match nameAt (pos + 1 + n.toNat) lim (seen + n.toNat + 1) fin with
        | some (ls, e) => some ((b.extract (pos + 1) (pos + 1 + n.toNat)).toList :: ls, e)
        | none => none
      else none
    else if 192 ≤ n.toNat then
      match b[pos + 1]? with
      | none => none
      | some m =>
        let p := (n.toNat - 192) * 256 + m.toNat
        if p < lim then nameAt p p seen (some (fin.getD (pos + 2))) else none
    else none
termination_by (lim, b.size - pos)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by assumption)

def name (i : Nat) : Option (Name × Nat) := nameAt b i i 0 none

/-- TXT rdata in `[i, e)`: strings, each after its length byte. -/
def txtAt (i e : Nat) : Option (List (List UInt8)) :=
  if h : i < e then
    match b[i]? with
    | none => none
    | some n =>
      if i + 1 + n.toNat ≤ e ∧ e ≤ b.size then
        match txtAt (i + 1 + n.toNat) e with
        | some ss => some ((b.extract (i + 1) (i + 1 + n.toNat)).toList :: ss)
        | none => none
      else none
  else if i = e then some [] else none
termination_by e - i

/-- The rdata of type `t` in `[i, e)`. -/
def rdata (t i e : Nat) : Option RData :=
  if t = tA.toNat then
    if e = i + 4 then (bytes b i 4).map (.a ·.1) else none
  else if t = tAAAA.toNat then
    if e = i + 16 then (bytes b i 16).map (.aaaa ·.1) else none
  else if t = tPTR.toNat then
    match name b i with
    | some (n, j) => if j = e then some (.ptr n) else none
    | none => none
  else if t = tSRV.toNat then do
    let (p, j) ← u16 b i
    let (w, j) ← u16 b j
    let (port, j) ← u16 b j
    let (n, j) ← name b j
    if j = e then some (.srv p.toUInt16 w.toUInt16 port.toUInt16 n) else none
  else if t = tTXT.toNat then
    (txtAt b i e).map .txt
  else
    (bytes b i (e - i)).map (.other t.toUInt16 ·.1)

def question (i : Nat) : Option (Question × Nat) := do
  let (n, i) ← name b i
  let (t, i) ← u16 b i
  let (c, i) ← u16 b i
  pure ({ name := n, type := t.toUInt16, cls := c.toUInt16 }, i)

def record (i : Nat) : Option (Record × Nat) := do
  let (n, i) ← name b i
  let (t, i) ← u16 b i
  let (c, i) ← u16 b i
  let (ttl, i) ← u32 b i
  let (len, i) ← u16 b i
  if i + len ≤ b.size then
    let d ← rdata b t i (i + len)
    pure ({ name := n, cls := c.toUInt16, ttl := ttl.toUInt32, data := d }, i + len)
  else none

/-- `k` of `p` in a row. -/
def many {α} (p : Nat → Option (α × Nat)) : Nat → Nat → Option (List α × Nat)
  | 0, i => some ([], i)
  | k + 1, i => do
    let (x, i) ← p i
    let (xs, i) ← many p k i
    pure (x :: xs, i)

def msgAt : Option Msg := do
  let (id, i) ← u16 b 0
  let (flags, i) ← u16 b i
  let (nq, i) ← u16 b i
  let (na, i) ← u16 b i
  let (ns, i) ← u16 b i
  let (nr, i) ← u16 b i
  let (qs, i) ← many (question b) nq i
  let (an, i) ← many (record b) na i
  let (au, i) ← many (record b) ns i
  let (ad, i) ← many (record b) nr i
  if i = b.size then
    some { id := id.toUInt16, flags := flags.toUInt16, questions := qs,
           answers := an, authority := au, additional := ad }
  else none

/-- The message in a packet: `none` unless the bytes are one well-formed
message and nothing after it. -/
def decode (p : ByteArray) : Option Msg := msgAt p.data

end Mdns
