/-
What Add members shows: the invite link's dial hints (this device's LAN
addresses, as "ip:port") and the link as a QR code.

The addresses come from `Std.Net.interfaceAddresses` (libuv, on Android
and iOS alike); `hints` keeps the private IPv4 ones, which are what a
phone on the same Wi-Fi can dial. `port` is the one the node listens on
(the app hands it to the runner).

The QR is drawn whole pixels per module (`qr`): a module that straddles
pixels aliases into grey and stops scanning. Laws: `hints_fit` (every hint
fits the link's limits, so the invite stays valid) and `qr_fits` (the
symbol and its quiet zone fit the side asked for).
-/
import Qr
import Std.Net.Addr
import Quiet.Paint

namespace Link
open Paint

/-- The port the node listens on (the app's default). -/
def port : Nat := 47100

/-- A private IPv4 address (10/8, 172.16/12, 192.168/16). -/
def isPrivate (o : List Nat) : Bool :=
  match o with
  | [10, _, _, _] => true
  | [172, b, _, _] => 16 ≤ b && b < 32
  | [192, 168, _, _] => true
  | _ => false

def hintOf (o : List Nat) (port : Nat) : String :=
  String.intercalate "." (o.map toString) ++ ":" ++ toString port

/-- An interface's rank: Wi-Fi first (Android's wlan*, Apple's en*), then
wired, then the rest (a phone's cellular rmnet* is private too, and a
joiner dials the first hint). -/
def rank (name : String) : Nat :=
  if name.startsWith "wlan" || name.startsWith "en" then 0
  else if name.startsWith "eth" then 1 else 2

/-- The dial hints for these addresses (interface, octets, loopback or
not) and port: the private IPv4 ones, Wi-Fi first, at most 8. -/
def hints (addrs : List (String × List Nat × Bool)) (port : Nat := port) : List ByteArray :=
  let ok := (addrs.filter fun (_, o, lo) => !lo && isPrivate o).mergeSort fun a b => rank a.1 ≤ rank b.1
  ((ok.map fun (_, o, _) => (hintOf o port).toUTF8).filter (·.size ≤ 255)).take 8

/-- **Every hint fits the link** (`Invite.Valid`'s hint clause). -/
theorem hints_fit (a : List (String × List Nat × Bool)) (port : Nat) :
    (hints a port).length ≤ 8 ∧ ∀ h ∈ hints a port, h.size ≤ 255 := by
  refine ⟨by simp only [hints, List.length_take]; omega, fun h hm => ?_⟩
  have := (List.mem_filter.1 (List.mem_of_mem_take hm)).2
  simpa using this

/-- This device's addresses, as `hints` takes them. -/
def local? : IO (List (String × List Nat × Bool)) := do
  let as ← Std.Net.interfaceAddresses
  return as.toList.filterMap fun a => match a.address with
    | .v4 v => some (a.name, v.octets.toList.map (·.toNat), a.isLoopback)
    | .v6 _ => none

/-- Pixels a module, for a symbol of n modules (and a 4-module quiet zone
each side) in a square `side` pixels across: whole pixels, at least 1. -/
def scale (n side : Nat) : Nat := max 1 (side / (n + 8))

theorem qr_fits (n side : Nat) (h : n + 8 ≤ side) : scale n side * (n + 8) ≤ side := by
  unfold scale
  have : 1 ≤ side / (n + 8) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  rw [Nat.max_eq_right this]
  exact Nat.div_mul_le_self side (n + 8)

/-- The link as a QR code, black on white, at most `side` pixels square. -/
def qr (text : String) (side : Nat) : Option Bitmap := do
  let s ← Qr.encode text.toUTF8 .M
  let img := Qr.render s (scale s.size side) 4
  let rows := (List.range img.h).toArray.map fun y => Id.run do
    let mut row := solid (Palette.color .light .white) img.w
    for x in [0:img.w] do
      if img.px[y * img.stride + x]! == 0 then row := setPx row x (Palette.color .light .black)
    return row
  return { w := img.w, rows := rows }

end Link
