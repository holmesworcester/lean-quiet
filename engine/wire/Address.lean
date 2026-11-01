/- Bounded IPv4 endpoint inputs shared by invites, signed advertisements and
DNS-SD. Reachability is learned by a successful authenticated handshake. -/
import Std.Net.Addr

namespace Hints

def cap : Nat := 8
def dialCap : Nat := 3 * cap
/-- A publication's longest life: a day. The newest supersedes, so a changed
address never waits for it; an unchanged one is reissued at half of it. -/
def maxAge : Nat := 86400000

def parse (b : ByteArray) : Option (Std.Net.IPv4Addr × UInt16) := do
  if b.size > 64 then none else do
    let s ← String.fromUTF8? b
    let [host, port] := s.splitOn ":" | none
    let ip ← Std.Net.IPv4Addr.ofString host
    let p ← port.toNat?
    if p = 0 || p > 65535 then none else
    let first := ip.octets[0]!.toNat
    if first = 0 || first ≥ 224 then none else some (ip, p.toUInt16)

def bounded (xs : List ByteArray) : List ByteArray :=
  ((xs.take 32).filter (fun b => (parse b).isSome)).eraseDups.take cap

def valid (xs : List ByteArray) : Bool :=
  xs.length ≤ cap && xs.all (fun b => (parse b).isSome)

def fresh (now issued expires : Nat) : Bool :=
  issued ≤ now && now < expires && expires ≤ issued + maxAge

/-- Retries cannot be accelerated by replacing endpoint advertisements. -/
def delay (attempts : Nat) : Nat := min 60000 (1000 * 2 ^ min attempts 6)

def due (now last attempts : Nat) : Bool := last + delay attempts ≤ now

/-- At most one of a peer's addresses per attempt, rotating through the cap. -/
def pick (xs : List ByteArray) (attempt : Nat) : Option ByteArray :=
  (xs.take dialCap)[attempt % (xs.take dialCap).length]?

theorem bounded_cap (xs : List ByteArray) : (bounded xs).length ≤ cap := by
  simp only [bounded, List.length_take]; omega

theorem delay_bounded (n : Nat) : delay n ≤ 60000 := Nat.min_le_left ..

theorem fresh_expires (now issued expires : Nat) (h : fresh now issued expires = true) :
    now < expires ∧ expires ≤ issued + maxAge := by
  simp only [fresh, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

end Hints
