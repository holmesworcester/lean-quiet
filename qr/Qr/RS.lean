/-
Reed–Solomon codes over GF(256) as QR uses them: the field's polynomial is
x⁸ + x⁴ + x³ + x² + 1 (0x11D), α = 2, and a block of `n` codewords with `k`
error-correction codewords is a multiple of g(x) = (x − α⁰)…(x − α^(k−1)).
The first codeword is the highest-degree coefficient.

`correct` is the decoder: syndromes, Berlekamp–Massey for the error
locator, a Chien search for the error positions and Forney's formula for
their values. Whatever it returns it has checked (`correct_sound`): the
syndromes are zero, so the block is a codeword, and it differs from the
received block in at most ⌊k/2⌋ places. A block whose syndromes are
already zero comes back unchanged (`correct_clean`).

Every array read is `a[i]?` (with a default), and every loop is a
`for` over a range.
-/
namespace Qr.RS

/-- αⁱ for i < 255, then 1 again at 255. -/
def expTable : Array UInt8 := Id.run do
  let mut a : Array UInt8 := Array.mkEmpty 256
  let mut x : Nat := 1
  for _ in [0:256] do
    a := a.push x.toUInt8
    x := x * 2
    if x ≥ 256 then x := x ^^^ 0x11D
  return a

/-- log_α x for x ≠ 0 (and 0 at 0). -/
def logTable : Array Nat := Id.run do
  let mut a : Array Nat := Array.replicate 256 0
  for i in [0:255] do
    a := a.setIfInBounds (expTable[i]?.getD 0).toNat i
  return a

@[inline] def exp (i : Nat) : UInt8 := expTable[i % 255]?.getD 1
@[inline] def log (x : UInt8) : Nat := logTable[x.toNat]?.getD 0

@[inline] def mul (a b : UInt8) : UInt8 :=
  if a == 0 || b == 0 then 0 else exp (log a + log b)

/-- a / b, for b ≠ 0. -/
@[inline] def div (a b : UInt8) : UInt8 :=
  if a == 0 then 0 else exp (log a + 255 - log b % 255)

/-- The value of the polynomial with coefficients `p` (highest degree
first) at `x`. -/
def eval (p : Array UInt8) (x : UInt8) : UInt8 :=
  p.foldl (fun s c => mul s x ^^^ c) 0

/-- Syndromes S_j = r(αʲ) for j < k. -/
def syndromes (k : Nat) (r : Array UInt8) : Array UInt8 :=
  (Array.range k).map fun j => eval r (exp j)

def allZero (s : Array UInt8) : Bool := s.all (· == 0)

/-- Places where two blocks differ (and the difference in length). -/
def dist (a b : Array UInt8) : Nat :=
  (List.range (max a.size b.size)).countP fun i => a[i]? != b[i]?

/-- The generator polynomial of `k` error-correction codewords, highest
degree first (its leading coefficient 1). -/
def generator (k : Nat) : Array UInt8 := Id.run do
  let mut g : Array UInt8 := #[1]
  for i in [0:k] do
    -- g · (x − αⁱ)
    let a := exp i
    let mut h : Array UInt8 := Array.replicate (g.size + 1) 0
    for j in [0:g.size] do
      let c := g[j]?.getD 0
      h := h.setIfInBounds j ((h[j]?.getD 0) ^^^ c)
      h := h.setIfInBounds (j + 1) ((h[j + 1]?.getD 0) ^^^ mul c a)
    g := h
  return g

/-- The `k` error-correction codewords of `data`: the remainder of
data(x)·xᵏ divided by the generator. -/
def encode (k : Nat) (data : Array UInt8) : Array UInt8 := Id.run do
  let g := generator k
  let mut r : Array UInt8 := Array.replicate k 0
  for d in data do
    let f := d ^^^ (r[0]?.getD 0)
    let mut s : Array UInt8 := Array.mkEmpty k
    for j in [0:k] do
      s := s.push ((r[j + 1]?.getD 0) ^^^ mul (g[j + 1]?.getD 0) f)
    r := s
  return r

/-- Berlekamp–Massey: the error locator Λ(x) of the syndromes, lowest
degree first (Λ₀ = 1), and its degree L. -/
def locator (s : Array UInt8) : Array UInt8 × Nat := Id.run do
  let n := s.size
  let mut c : Array UInt8 := Array.replicate (n + 1) 0
  c := c.setIfInBounds 0 1
  let mut b : Array UInt8 := c
  let mut l := 0
  let mut m := 1
  let mut bb : UInt8 := 1
  for i in [0:n] do
    let mut d := s[i]?.getD 0
    for j in [1:l + 1] do
      d := d ^^^ mul (c[j]?.getD 0) (s[i - j]?.getD 0)
    if d == 0 then
      m := m + 1
    else
      let coef := div d bb
      let t := c
      for j in [0:n + 1 - m] do
        c := c.setIfInBounds (j + m) ((c[j + m]?.getD 0) ^^^ mul coef (b[j]?.getD 0))
      if 2 * l ≤ i then
        l := i + 1 - l
        b := t
        bb := d
        m := 1
      else
        m := m + 1
  return (c, l)

/-- The value at `x` of a polynomial given lowest degree first. -/
def evalLow (p : Array UInt8) (x : UInt8) : UInt8 :=
  p.foldr (fun c s => mul s x ^^^ c) 0

/-- Corrects the errors the syndromes point to: positions from the roots
of Λ, values by Forney's formula. `none` when Λ's roots are not all
inside the block. -/
def fix (k : Nat) (r : Array UInt8) : Option (Array UInt8) := Id.run do
  let s := syndromes k r
  let (lam, l) := locator s
  if 2 * l > k then return none
  let n := r.size
  -- Ω(x) = S(x)Λ(x) mod xᵏ, lowest degree first
  let mut om : Array UInt8 := Array.replicate k 0
  for i in [0:k] do
    let mut acc : UInt8 := 0
    for j in [0:i + 1] do
      acc := acc ^^^ mul (s[i - j]?.getD 0) (lam[j]?.getD 0)
    om := om.setIfInBounds i acc
  -- Λ'(x): the odd terms, lowered by one degree
  let mut dl : Array UInt8 := Array.replicate (l + 1) 0
  for j in [1:l + 1] do
    if j % 2 == 1 then dl := dl.setIfInBounds (j - 1) (lam[j]?.getD 0)
  let lamL := lam.extract 0 (l + 1)
  let mut out := r
  let mut found := 0
  for i in [0:n] do
    -- position i has degree n-1-i, locator X = α^(n-1-i), and Λ(X⁻¹) = 0 there
    let e := n - 1 - i
    let xinv := exp (255 - e % 255)
    if evalLow lamL xinv == 0 then
      found := found + 1
      let den := evalLow dl xinv
      if den == 0 then return none
      let v := mul (exp e) (div (evalLow om xinv) den)
      out := out.setIfInBounds i ((out[i]?.getD 0) ^^^ v)
  if found != l then return none
  return some out

/-- The block corrected, if it has at most ⌊k/2⌋ errors; checked: what it
returns has zero syndromes and is within ⌊k/2⌋ of `r`. -/
def correct (k : Nat) (r : Array UInt8) : Option (Array UInt8) :=
  if allZero (syndromes k r) then some r
  else
    match fix k r with
    | none => none
    | some c =>
      if allZero (syndromes k c) && c.size == r.size && decide (dist r c ≤ k / 2) then some c
      else none

end Qr.RS
