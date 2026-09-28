import Erdos993Lean.Analytic.TailCert.Compute.Ival

/-!
# O2 certificate checker (lane A18): dual numbers over the fixed-point interval core

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  This module imports only Lean's core and lane A10's
fixed-point interval core (`Erdos993Lean/Analytic/TailCert/Compute/Ival.lean`), so that it can be precompiled
(library `Erdos993LeanO2CertCompute`).  Its exact Python mirror is `LEAN/lanes/A18/scratch/mirror.py`; the
arithmetic follows Pro's `ad_tight.py` (`SOUL/O2_FINAL/R2_PACKET/`), with lane A10's logarithm.

A *dual number* `DN` over a box of the two coordinates `(λ, x)` carries an interval `v` for the value, intervals
`d0`, `d1` for the slopes (divided differences) in `λ` and in `x`, and a flag `ok` that records every side
condition of the operations used (positive divisors, positive logarithm arguments, ...).  The soundness of every
operation is proved in `Erdos993Lean/Analytic/O2/Cert/DualSound.lean`.

* interval helpers `sqI` (signed square), `imax`, `imin`, `hull`;
* `DN.cst`, `dadd`, `daddI`, `dneg`, `dsub`, `dsubI`, `drsubI`, `dmul`, `dmulI`, `ddiv`, `ddivI`, `dsq`, `dlog`;
* maxima and minima with value shortcuts: `dmax`, `dmin` (strict), `mx`, `mn` (non-strict), `dhull`;
* `kernel e λ`: the removable kernel `k(e, λ) = (log(1 + λe) − log(1 − e))/e` by its power series.

Every definition is plain structural recursion; there is no `partial`, `unsafe`, `implemented_by` or `extern`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Compute

open Erdos993Lean.Analytic.TailCert.Compute

/-! ## Interval helpers -/

/-- The point interval `0`. -/
def zI : Ival := ⟨0, 0⟩

/-- The point interval `1`. -/
def oneI : Ival := pt one

/-- The point interval `2`. -/
def twoI : Ival := pt (2 * one)

/-- The point interval `4`. -/
def fourI : Ival := pt (4 * one)

/-- The point interval `8`. -/
def eightI : Ival := pt (8 * one)

/-- `2 ^ 61`, the fixed-point number `1/8`. -/
def eighth : Int := 2305843009213693952

/-- The point interval of the knot `j/8`. -/
def knotI (j : Nat) : Ival := pt (j * eighth)

/-- The square of an interval of either sign. -/
def sqI (A : Ival) : Ival :=
  if 0 ≤ A.lo then sqr A
  else if A.hi ≤ 0 then sqr (neg A)
  else ⟨0, cdivP (max (A.lo * A.lo) (A.hi * A.hi))⟩

/-- An enclosure of `max x y` for `x ∈ A`, `y ∈ B`. -/
def imax (A B : Ival) : Ival := ⟨max A.lo B.lo, max A.hi B.hi⟩

/-- An enclosure of `min x y` for `x ∈ A`, `y ∈ B`. -/
def imin (A B : Ival) : Ival := ⟨min A.lo B.lo, min A.hi B.hi⟩

/-- The hull of two intervals. -/
def hull (A B : Ival) : Ival := ⟨min A.lo B.lo, max A.hi B.hi⟩

/-! ## Dual numbers -/

/-- A dual number on a box of `(λ, x)`: value, slope in `λ`, slope in `x`, side conditions. -/
structure DN where
  /-- the value interval -/
  v : Ival
  /-- the slope interval in `λ` -/
  d0 : Ival
  /-- the slope interval in `x` -/
  d1 : Ival
  /-- all side conditions hold -/
  ok : Bool

/-- A constant. -/
def DN.cst (c : Ival) : DN := ⟨c, zI, zI, true⟩

/-- The constant `0`. -/
def zeroDN : DN := DN.cst zI

/-- The constant `1`. -/
def oneDN : DN := DN.cst oneI

/-- Sum. -/
def dadd (a b : DN) : DN := ⟨add a.v b.v, add a.d0 b.d0, add a.d1 b.d1, a.ok && b.ok⟩

/-- Sum with a constant interval. -/
def daddI (a : DN) (c : Ival) : DN := ⟨add a.v c, a.d0, a.d1, a.ok⟩

/-- Negation. -/
def dneg (a : DN) : DN := ⟨neg a.v, neg a.d0, neg a.d1, a.ok⟩

/-- Difference. -/
def dsub (a b : DN) : DN := dadd a (dneg b)

/-- `a − c` for a constant interval `c`. -/
def dsubI (a : DN) (c : Ival) : DN := daddI a (neg c)

/-- `c − a` for a constant interval `c`. -/
def drsubI (c : Ival) (a : DN) : DN := daddI (dneg a) c

/-- Product (the product rule for slopes). -/
def dmul (a b : DN) : DN :=
  ⟨mul a.v b.v, add (mul a.d0 b.v) (mul a.v b.d0), add (mul a.d1 b.v) (mul a.v b.d1), a.ok && b.ok⟩

/-- Product with a constant interval. -/
def dmulI (a : DN) (c : Ival) : DN := ⟨mul a.v c, mul a.d0 c, mul a.d1 c, a.ok⟩

/-- Quotient (divisor value interval positive). -/
def ddiv (a b : DN) : DN :=
  let v := div a.v b.v
  ⟨v, div (sub a.d0 (mul v b.d0)) b.v, div (sub a.d1 (mul v b.d1)) b.v,
    a.ok && b.ok && decide (0 < b.v.lo)⟩

/-- Quotient by a positive constant interval. -/
def ddivI (a : DN) (c : Ival) : DN := ⟨div a.v c, div a.d0 c, div a.d1 c, a.ok && decide (0 < c.lo)⟩

/-- Square. -/
def dsq (a : DN) : DN :=
  let t := mul twoI a.v
  ⟨sqI a.v, mul t a.d0, mul t a.d1, a.ok⟩

/-- Logarithm (argument value interval positive). -/
def dlog (a : DN) : DN := ⟨logI a.v, div a.d0 a.v, div a.d1 a.v, a.ok && decide (0 < a.v.lo)⟩

/-- The hull of two dual numbers. -/
def dhull (a b : DN) : DN := ⟨hull a.v b.v, hull a.d0 b.d0, hull a.d1 b.d1, a.ok && b.ok⟩

/-- Maximum with strict value shortcuts (Pro's `ad.maximum`). -/
def dmax (a b : DN) : DN :=
  if b.v.hi < a.v.lo then { a with ok := a.ok && b.ok }
  else if a.v.hi < b.v.lo then { b with ok := a.ok && b.ok }
  else ⟨imax a.v b.v, hull a.d0 b.d0, hull a.d1 b.d1, a.ok && b.ok⟩

/-- Minimum with strict value shortcuts (Pro's `ad.minimum`). -/
def dmin (a b : DN) : DN :=
  if a.v.hi < b.v.lo then { a with ok := a.ok && b.ok }
  else if b.v.hi < a.v.lo then { b with ok := a.ok && b.ok }
  else ⟨imin a.v b.v, hull a.d0 b.d0, hull a.d1 b.d1, a.ok && b.ok⟩

/-- Maximum with non-strict value shortcuts (Pro's `ypoly` `mx`). -/
def mx (a b : DN) : DN :=
  if b.v.hi ≤ a.v.lo then { a with ok := a.ok && b.ok }
  else if a.v.hi ≤ b.v.lo then { b with ok := a.ok && b.ok }
  else ⟨imax a.v b.v, hull a.d0 b.d0, hull a.d1 b.d1, a.ok && b.ok⟩

/-- Minimum with non-strict value shortcuts (Pro's `ypoly` `mn`). -/
def mn (a b : DN) : DN :=
  if a.v.hi ≤ b.v.lo then { a with ok := a.ok && b.ok }
  else if b.v.hi ≤ a.v.lo then { b with ok := a.ok && b.ok }
  else ⟨imin a.v b.v, hull a.d0 b.d0, hull a.d1 b.d1, a.ok && b.ok⟩

/-- The dual number of the coordinate `λ` over an interval. -/
def lamDN (A : Ival) : DN := ⟨A, oneI, zI, true⟩

/-- The dual number of the coordinate `x` over an interval. -/
def xDN (A : Ival) : DN := ⟨A, zI, oneI, true⟩

/-! ## The removable kernel `k(e, λ) = (log(1 + λe) − log(1 − e))/e = ∑ₙ cₙ eⁿ`,
`cₙ = ((−1)ⁿ λⁿ⁺¹ + 1)/(n + 1)` -/

/-- `(∑_{n<k} cₙ eⁿ, λᵏ⁺¹, eᵏ)` for `λ ∈ lv`, `e ∈ ev`. -/
def kvalLoop (lv ev : Ival) : Nat → Ival × Ival × Ival
  | 0 => (zI, lv, oneI)
  | n + 1 =>
    let t := kvalLoop lv ev n
    let c := add (mulInt t.2.1 (if n % 2 = 0 then 1 else -1)) oneI
    (add t.1 (divNat (mul c t.2.2) (n + 1)), mul t.2.1 lv, mul t.2.2 ev)

/-- `(∑_{m=1}^{k} cₘ m eᵐ⁻¹, λᵏ⁺², eᵏ)`, the partial sums of the `e`-slope. -/
def kpartLoop (lv ev : Ival) : Nat → Ival × Ival × Ival
  | 0 => (zI, mul lv lv, oneI)
  | n + 1 =>
    let t := kpartLoop lv ev n
    let c := add (mulInt t.2.1 (if (n + 1) % 2 = 1 then -1 else 1)) oneI
    (add t.1 (divNat (mulNat (mul c t.2.2) (n + 1)) (n + 2)), mul t.2.1 lv, mul t.2.2 ev)

/-- The power `Aᵏ` of an interval (repeated products). -/
def ipow (A : Ival) : Nat → Ival
  | 0 => oneI
  | k + 1 => mul (ipow A k) A

/-- The number of terms of the kernel value. -/
def nK : Nat := 32

/-- The number of terms of the kernel slope. -/
def mK : Nat := 16

/-- **The kernel** `k(e, λ)` as a dual number: value by `nK` terms and the geometric tail
`λ^(nK+1) e^nK/(1 − λe) + e^nK/(1 − e)`; `e`-slope by `mK` terms and the tail
`λ²(λe)^mK/(1 − λe) + e^mK/(1 − e)`; `λ`-slope `1/(1 + λe)`. -/
def kernel (e lam : DN) : DN :=
  let ev := e.v
  let lv := lam.v
  let t := kvalLoop lv ev nK
  let le := mul lv ev
  let tail := add (div (mul t.2.1 t.2.2) (sub oneI le)) (div t.2.2 (sub oneI ev))
  let val : Ival := ⟨t.1.lo - tail.hi, t.1.hi + tail.hi⟩
  let ps := (kpartLoop lv ev mK).1
  let er := add (div (mul (mul lv lv) (ipow le mK)) (sub oneI le)) (div (ipow ev mK) (sub oneI ev))
  let part : Ival := ⟨ps.lo - er.hi, ps.hi + er.hi⟩
  let partlam := div oneI (add oneI le)
  ⟨val, add (mul part e.d0) (mul partlam lam.d0), add (mul part e.d1) (mul partlam lam.d1),
    e.ok && lam.ok && decide (0 ≤ ev.lo) && decide (0 < lv.lo) && decide (0 < (sub oneI le).lo) &&
      decide (0 < (sub oneI ev).lo) && decide (0 < (add oneI le).lo)⟩

end Erdos993Lean.Analytic.O2.Cert.Compute
