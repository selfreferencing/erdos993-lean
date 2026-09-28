import Erdos993Lean.Analytic.TailCert.Compute.Ival

/-!
# The cell checker of O1's finite box (lane A12): computational core

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  Sources: Astra's O1 cell certificates
(`LEAN/referee/astra_o1/snapshot_0730/`: `replay_sharp_v4.py`, `replay_certify_lower_alternate_reserve.py`) and the
referee's independent replay (`LEAN/referee/REVIEW_ASTRA_O1_REPLAY.md`, `review_replay/o1core.py`: the normalized
forms and the monotone enclosures used here).  This module imports only Lean's core and lane A10's fixed-point
interval core `Erdos993Lean/Analytic/TailCert/Compute/Ival.lean`, so that it can be precompiled (library
`Erdos993LeanReserveCertCompute`).  The soundness theorems (standard axioms) are in
`Erdos993Lean/Analytic/Reserve/Cert/CellSound.lean` and `Erdos993Lean/Analytic/Reserve/Cert/Sound.lean`.

A cell is a box `[a0, a1] × [t0, t1] × [r0, r1]` of `(λ, T, r)` with fixed-point end points (`Cell`); the point
`(λ, T, r)` stands for `(λ, T, Y)` with `Y = y + (4 − y) r`, `y = log(1 + λ e^{−T})`.

* **Cell values** (`mkVals`), with `v = λ e^{−T}`, `s = v/(1 + v)`, `R = λ e^{−Y}`, `p = R/(1 + R)`,
  `y₀ = log(1 + R)`: `q = 1 − 1/(1 + λ)`, `α`, `γ`; `y`, `s`; `σ = s/y ∈ [φ(y_hi), φ(y_lo)]` and
  `ρ = p/y₀ ∈ [φ(y₀_hi), φ(y₀_lo)]` (`φ(t) = (1 − e^{−t})/t` decreases, `phiPt`); `Y ∈ [Y(y_lo, r0), Y(y_hi, r1)]`
  (`yFun`); `R` between its values at the corners `(a0, t0, r1)` and `(a1, t1, r0)` (`R` increases in `λ` and `T`
  and decreases in `r`); `h = 1 − p + γρ`, `J = sσT`, `L/p = γ/R − hY`, `L` (two enclosures, `meet`),
  `Z̄ = Z/p = γ + J·L/p`; the direct enclosure of `E = 1 − p + pT/y − y₀/Y` (no floor of `E` is needed: every
  cell passes without `EntropyOK`); `B = αE + p[(q(D − 1) + p − γρ)/Y − h²J/Z̄]`, `C = αE + γLσ²/Z̄`.
* **The cell check** (`cellOK`): side conditions (`sideOK`), `Z̄ > 0`, `B ≥ 0`, and `L ≥ 0` or `C ≥ 0`.
* **The cover**: `walk` follows a preorder trie string (`'0'`, `'1'`, `'2'`: split that axis at the midpoint, lower
  half first; `'L'`: a leaf), checking each leaf with `bisectOK` (the cell, or its halves along the axes in turn, at
  most `fallbackDepth` more levels); `checkBand lo hi D aCoef gDen s` walks `s` from the root box
  `[lo, hi] × [0, 6] × [0, 1]`.
* **The selected-leaf base** (`leafCellOK`, `leafCover`, `checkLeaf`): `aCoef ℓ/q + γ/ℓ ≤ D` with
  `ℓ = log(1 + λ)`, by bisection in `λ`.

Every definition is plain structural recursion; there is no `partial`, `unsafe`, `implemented_by` or `extern`.
The only compiler hints are `@[noinline]` on `checkBand` and `checkLeaf`.
-/

namespace Erdos993Lean.Analytic.Reserve.Cert.Compute

open Erdos993Lean.Analytic.TailCert.Compute

/-! ## Constants, cells and helpers -/

/-- The band constants of the checker: enclosures of `D − 1`, `aCoef` and `1/gDen`. -/
structure Consts where
  /-- enclosure of `D − 1` -/
  Dm1 : Ival
  /-- enclosure of `aCoef` -/
  AC : Ival
  /-- enclosure of `1/gDen` -/
  GI : Ival

/-- The band constants of `D`, `aCoef`, `gDen`. -/
def mkConsts (D aCoef gDen : Rat) : Consts := ⟨ofRat (D - 1), ofRat aCoef, ofRat (1 / gDen)⟩

/-- A cell `[a0, a1] × [t0, t1] × [r0, r1]` of `(λ, T, r)` (fixed-point end points). -/
structure Cell where
  /-- lower end of `λ` -/
  a0 : Int
  /-- upper end of `λ` -/
  a1 : Int
  /-- lower end of `T` -/
  t0 : Int
  /-- upper end of `T` -/
  t1 : Int
  /-- lower end of `r` -/
  r0 : Int
  /-- upper end of `r` -/
  r1 : Int

/-- The point interval `1`. -/
def oneI : Ival := pt one

/-- The point interval `3`. -/
def threeI : Ival := pt (3 * one)

/-- The point interval `4`. -/
def fourI : Ival := pt (4 * one)

/-- An enclosure of `φ(t) = (1 − e^{−t})/t` at a point `t > 0`. -/
def phiPt (t : Int) : Ival := div (sub oneI (expPt (-t))) (pt t)

/-- `y + (4 − y) r`. -/
def yFun (Yv Rv : Ival) : Ival := add Yv (mul (sub fourI Yv) Rv)

/-- The square of an interval of either sign. -/
def sqI (A : Ival) : Ival :=
  if 0 ≤ A.lo then sqr A
  else if A.hi ≤ 0 then sqr (neg A)
  else ⟨0, cdivP (max (A.lo * A.lo) (A.hi * A.hi))⟩

/-- The intersection of two enclosures of one number. -/
def meet (A B : Ival) : Ival := ⟨max A.lo B.lo, min A.hi B.hi⟩

/-! ## The values of a cell -/

/-- The enclosures of a cell. -/
structure Vals where
  /-- `q = 1 − 1/(1 + λ)` -/
  q : Ival
  /-- `α = aCoef q` -/
  al : Ival
  /-- `γ = λ(3 + λ)/gDen` -/
  gam : Ival
  /-- `e^{−t0}` -/
  E0 : Ival
  /-- `e^{−t1}` -/
  E1 : Ival
  /-- `v = λ e^{−T}` -/
  v : Ival
  /-- `y = log(1 + v)` -/
  y : Ival
  /-- `s = 1 − 1/(1 + v)` -/
  s : Ival
  /-- `σ = s/y` -/
  sig : Ival
  /-- `Y = y + (4 − y) r` -/
  Y : Ival
  /-- `y` at the corner `(a0, t0)` -/
  yc0 : Ival
  /-- `y` at the corner `(a1, t1)` -/
  yc1 : Ival
  /-- `R = λ e^{−Y}` -/
  R : Ival
  /-- `1 − p = 1/(1 + R)` -/
  omp : Ival
  /-- `p = 1 − 1/(1 + R)` -/
  p : Ival
  /-- `y₀ = log(1 + R)` -/
  y0 : Ival
  /-- `ρ = p/y₀` -/
  rho : Ival
  /-- `h = 1 − p + γρ` -/
  h : Ival
  /-- `J = s σ T` -/
  J : Ival
  /-- `L/p = γ/R − h Y` -/
  Lp : Ival
  /-- `L = γ(1 − p) − p h Y` -/
  L : Ival
  /-- `Z̄ = Z/p = γ + J L/p` -/
  Zb : Ival
  /-- the enclosure of `E = 1 − p + p T/y − y₀/Y` -/
  Ed : Ival
  /-- `α E` -/
  aE : Ival
  /-- `(q(D − 1) + p − γρ)/Y − h² J/Z̄` -/
  Kq : Ival
  /-- the lower bound of `B` -/
  B : Ival
  /-- the lower bound of `C` -/
  C : Ival

/-- The enclosures of the cell `c`. -/
def mkVals (K : Consts) (c : Cell) : Vals :=
  let lam : Ival := ⟨c.a0, c.a1⟩
  let T : Ival := ⟨c.t0, c.t1⟩
  let q := sub oneI (div oneI (add oneI lam))
  let al := mul K.AC q
  let gam := mul (mul lam (add threeI lam)) K.GI
  let E0 := expPt (-c.t0)
  let E1 := expPt (-c.t1)
  let v := mul lam ⟨E1.lo, E0.hi⟩
  let y := logI (add oneI v)
  let s := sub oneI (div oneI (add oneI v))
  let sig : Ival := ⟨(phiPt y.hi).lo, (phiPt y.lo).hi⟩
  let Y : Ival := ⟨(yFun (pt y.lo) (pt c.r0)).lo, (yFun (pt y.hi) (pt c.r1)).hi⟩
  let yc0 := logI (add oneI (mul (pt c.a0) E0))
  let yc1 := logI (add oneI (mul (pt c.a1) E1))
  let R : Ival := ⟨(mul (pt c.a0) (expPt (-(yFun yc0 (pt c.r1)).hi))).lo,
    (mul (pt c.a1) (expPt (-(yFun yc1 (pt c.r0)).lo))).hi⟩
  let omp := div oneI (add oneI R)
  let p := sub oneI omp
  let y0 := logI (add oneI R)
  let rho : Ival := ⟨(phiPt y0.hi).lo, (phiPt y0.lo).hi⟩
  let h := add omp (mul gam rho)
  let J := mul (mul s sig) T
  let Lp := sub (div gam R) (mul h Y)
  let L := meet (sub (mul gam omp) (mul (mul p h) Y)) (mul p Lp)
  let Zb := add gam (mul J Lp)
  let Ed := sub (add omp (mul p (div T y))) (div y0 Y)
  let aE := mul al Ed
  let Kq := sub (div (sub (add (mul q K.Dm1) p) (mul gam rho)) Y) (div (mul (sqI h) J) Zb)
  let B := add aE (mul p Kq)
  let C := add aE (div (mul (mul gam L) (sqI sig)) Zb)
  { q := q, al := al, gam := gam, E0 := E0, E1 := E1, v := v, y := y, s := s, sig := sig, Y := Y,
    yc0 := yc0, yc1 := yc1, R := R, omp := omp, p := p, y0 := y0, rho := rho, h := h, J := J, Lp := Lp,
    L := L, Zb := Zb, Ed := Ed, aE := aE, Kq := Kq, B := B, C := C }

/-- The side conditions of a cell: `λ > 0`, `λ ≤ 4`, `T ≥ 0`, `0 ≤ r ≤ 1`, positive arguments of `log`, positive
divisors, and `Z̄ > 0`. -/
def sideOK (c : Cell) (V : Vals) : Bool :=
  decide (0 < c.a0) && decide (c.a1 ≤ 4 * one) && decide (0 ≤ c.t0) && decide (0 ≤ c.r0) &&
    decide (c.r1 ≤ one) && decide (0 < (add oneI V.v).lo) && decide (0 < V.y.lo) &&
    decide (0 < (add oneI (mul (pt c.a0) V.E0)).lo) && decide (0 < (add oneI (mul (pt c.a1) V.E1)).lo) &&
    decide (0 < V.R.lo) && decide (0 < V.y0.lo) && decide (0 < V.Y.lo) && decide (0 < V.Zb.lo)

/-- **The cell check**: the side conditions (with `(Q0)` `Z̄ > 0`), `(QB)` `B ≥ 0`, and `(QC)` `L ≥ 0` or
`C ≥ 0`. -/
def cellOK (K : Consts) (c : Cell) : Bool :=
  let V := mkVals K c
  sideOK c V && decide (0 ≤ V.B.lo) &&
    (decide (0 ≤ V.L.lo) || decide (0 ≤ V.Lp.lo) || decide (0 ≤ V.C.lo))

/-! ## The cover -/

/-- The midpoint `⌊(a + b)/2⌋`. -/
def midI (a b : Int) : Int := (a + b) / 2

/-- The lower half of a cell along axis `j` (`0`: `λ`, `1`: `T`, otherwise `r`). -/
def lowHalf (c : Cell) : Nat → Cell
  | 0 => { c with a1 := midI c.a0 c.a1 }
  | 1 => { c with t1 := midI c.t0 c.t1 }
  | _ => { c with r1 := midI c.r0 c.r1 }

/-- The upper half of a cell along axis `j` (`0`: `λ`, `1`: `T`, otherwise `r`). -/
def highHalf (c : Cell) : Nat → Cell
  | 0 => { c with a0 := midI c.a0 c.a1 }
  | 1 => { c with t0 := midI c.t0 c.t1 }
  | _ => { c with r0 := midI c.r0 c.r1 }

/-- The adaptive fallback: the cell passes, or both halves along axis `j` pass (the next level splits the
next axis), at most `f` more levels. -/
def bisectOK (K : Consts) : Nat → Nat → Cell → Bool
  | 0, _, c => cellOK K c
  | f + 1, j, c => cellOK K c ||
      (bisectOK K f ((j + 1) % 3) (lowHalf c j) && bisectOK K f ((j + 1) % 3) (highHalf c j))

/-- The depth of the adaptive fallback at a leaf of the trie. -/
def fallbackDepth : Nat := 6

/-- The trie walk from byte `i` of `s` over the cell `c`: the success flag and the next byte. -/
def walk (K : Consts) (s : String) : Nat → Nat → Cell → Bool × Nat
  | 0, i, _ => (false, i)
  | f + 1, i, c =>
    let ch := String.Pos.Raw.get s ⟨i⟩
    if ch = 'L' then (bisectOK K fallbackDepth 0 c, i + 1)
    else
      let j := ch.toNat - 48
      let r := walk K s f (i + 1) (lowHalf c j)
      if r.1 then walk K s f r.2 (highHalf c j) else (false, r.2)

/-- The root box `[lo, hi] × [0, 6] × [0, 1]` (the end points of `λ` rounded outward). -/
def rootCell (lo hi : Rat) : Cell := ⟨(ofRat lo).lo, (ofRat hi).hi, 0, 6 * one, 0, one⟩

/-- The depth bound of the trie walk. -/
def walkFuel : Nat := 100

/-- **The band check**: the trie `s` covers the root box `[lo, hi] × [0, 6] × [0, 1]` with passing cells
(`Cert.boxOK_of_check`). -/
@[noinline] def checkBand (lo hi D aCoef gDen : Rat) (s : String) : Bool :=
  decide (0 < lo) && decide (hi < 4) && (walk (mkConsts D aCoef gDen) s walkFuel 0 (rootCell lo hi)).1

/-! ## The selected-leaf base -/

/-- The leaf base on `λ ∈ [a0, a1]`: `aCoef ℓ/q + γ/ℓ ≤ D`, `ℓ = log(1 + λ)`, `q = 1 − 1/(1 + λ)`. -/
def leafCellOK (D aCoef gDen : Rat) (a0 a1 : Int) : Bool :=
  let lam : Ival := ⟨a0, a1⟩
  let q := sub oneI (div oneI (add oneI lam))
  let gam := mul (mul lam (add threeI lam)) (ofRat (1 / gDen))
  let ell := logI (add oneI lam)
  let lhs := add (mul (ofRat aCoef) (div ell q)) (div gam ell)
  decide (0 < a0) && decide (0 < q.lo) && decide (0 < ell.lo) && decide (lhs.hi ≤ (ofRat D).lo)

/-- The leaf base on `[a0, a1]` by bisection (at most `f` levels). -/
def leafCover (D aCoef gDen : Rat) : Nat → Int → Int → Bool
  | 0, a0, a1 => leafCellOK D aCoef gDen a0 a1
  | f + 1, a0, a1 => leafCellOK D aCoef gDen a0 a1 ||
      (leafCover D aCoef gDen f a0 (midI a0 a1) && leafCover D aCoef gDen f (midI a0 a1) a1)

/-- **The leaf-base check** on `[lo, hi]` (`Cert.leafOK_of_check`). -/
@[noinline] def checkLeaf (lo hi D aCoef gDen : Rat) : Bool :=
  leafCover D aCoef gDen 30 (ofRat lo).lo (ofRat hi).hi

end Erdos993Lean.Analytic.Reserve.Cert.Compute
