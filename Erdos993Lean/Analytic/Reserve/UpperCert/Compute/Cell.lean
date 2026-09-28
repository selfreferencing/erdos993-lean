import Erdos993Lean.Analytic.TailCert.Compute.Ival
import Erdos993Lean.Analytic.Reserve.Cert.Compute.Cell

/-!
# The cell checker of O1's upper finite box (lane A15): computational core

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  Sources: Astra's upper-band certificate
(`LEAN/referee/astra_o1/snapshot_0845/upper_centered_derivative_certificate.json`, 617,294 cells) and the referee's
independent replay (`LEAN/referee/REVIEW_ASTRA_O1_UPPER_REPLAY.md`, `review_upper_replay/upcore.py`: the normalized
forms and monotone enclosures used here); lane A12's checker of the four lower bands (`Reserve/Cert/Compute/Cell.lean`,
whose cells, halves, `yFun`, `sqI`, `meet` are reused).  This module imports only Lean's core, lane A10's fixed-point
interval core `Erdos993Lean/Analytic/TailCert/Compute/Ival.lean` and lane A12's compute core, so that it can be
precompiled (library `Erdos993LeanUpperCertCompute`).  The soundness theorems (standard axioms) are in
`Erdos993Lean/Analytic/Reserve/UpperCert/CellSound.lean` and `Erdos993Lean/Analytic/Reserve/UpperCert/Sound.lean`.

A cell is a box `[a0, a1] × [t0, t1] × [r0, r1]` of `(λ, T, r)` (lane A12's `Cell`); the point `(λ, T, r)` stands for
`(λ, T, Y)` with `Y = y + (4 − y) r`, `y = log(1 + λ e^{−T})`.  The upper band's coefficients are `α = q/2`,
`β = (λ − 1)/27`, `γ = 31λ/100`, `A = 1 + 3q/5` (`Reserve/UpperDefs.lean`).

* **Cell values** (`mkValsU`), with `v = λ e^{−T}`, `s = v/(1 + v)`, `R = λ e^{−Y}`, `p = R/(1 + R)`,
  `y₀ = log(1 + R)`, `δ = s − p`: `v ∈ [a0 e^{−t1}, a1 e^{−t0}]` (two point values `vlo`, `vhi`); `y`, `s` from the
  point values at `vlo`, `vhi` (`s` increases in `v`, `msgPt`); `σ = s/y = φ(y)` between `s/y` at `vhi` and at `vlo`
  (`φ(t) = (1 − e^{−t})/t` decreases; no further exponential); `Y ∈ [Y(y_lo, r0), Y(y_hi, r1)]`; `R` between its values
  at the corners `(a0, t0, r1)` and `(a1, t1, r0)`, each from one side of one logarithm; `ρ = p/y₀ = φ(y₀)` likewise;
  `h = 1 − p + γρ`, `J = sσT`, `L/p = γ/R − hY`, `L` (two enclosures, `meet`), `Z̄ = Z/p = γ + J·L/p`;
  `K = 2αpZ̄ − β²T/4` (`8αZ − β²T = 4K`); a floor of `E = 1 − p + pT/y − y₀/Y`: `max(0, E_direct, E_f)` with
  `E_f = [2δ² + (Y − y)(p + y₀/Y)]/y` (both floors from `EntropyOK`); `Q = β²δ²T/(4yZ)`;
  `X = σ[βγ + Lσ(γ + βT)]/Z̄`; `W = p(3q/5 − β + p − γρ)/Y`; the regrouped BC
  `α(1 − p − y₀/Y) + W + (T/y)[p(αZ̄ − h²s²) − hβδs]/Z̄`.
* **The cell check** (`cellOKU`): side conditions (`sideOKU`, with `Z̄ > 0`), `K ≥ 0`, `αE_floor − Q + X ≥ 0` (CB) and
  `BC_regrouped − Q ≥ 0` (BC).
* **The cover**: `walkU` follows a preorder trie string (`'0'`, `'1'`, `'2'`: split that axis at the midpoint, lower
  half first; `'L'`: a leaf), checking each leaf with `bisectOKU` (the cell, or its halves along the axes in turn, at
  most `fallbackDepthU` more levels); `checkAt c s` walks `s` from the cell `c`; `checkUpper s` from the root box
  `rootU = [8/5, 7/3] × [0, 6] × [0, 1]`.

Every definition is plain structural recursion; there is no `partial`, `unsafe`, `implemented_by` or `extern`.
The only compiler hints are `@[noinline]` on `checkAt` and `checkUpper`.
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert.Compute

open Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.Reserve.Cert.Compute

/-- An enclosure of `1 − 1/(1 + w)` at a point `w` (for `1 + w > 0`). -/
def msgPt (w : Int) : Ival := sub oneI (div oneI (pt (one + w)))

/-! ## The values of a cell -/

/-- The enclosures of a cell of the upper band. -/
structure ValsU where
  /-- `q = 1 − 1/(1 + λ)` -/
  q : Ival
  /-- `α = q/2` -/
  al : Ival
  /-- `β = (λ − 1)/27` -/
  be : Ival
  /-- `γ = 31λ/100` -/
  gam : Ival
  /-- `e^{−t0}` -/
  E0 : Ival
  /-- `e^{−t1}` -/
  E1 : Ival
  /-- a lower bound of `v = λ e^{−T}` -/
  vlo : Int
  /-- an upper bound of `v = λ e^{−T}` -/
  vhi : Int
  /-- `log(1 + vlo)` -/
  yl : Ival
  /-- `log(1 + vhi)` -/
  yh : Ival
  /-- `y = log(1 + v)` -/
  y : Ival
  /-- `1 − 1/(1 + vlo)` -/
  sl : Ival
  /-- `1 − 1/(1 + vhi)` -/
  sh : Ival
  /-- `s = 1 − 1/(1 + v)` -/
  s : Ival
  /-- `σ = s/y` -/
  sig : Ival
  /-- `Y = y + (4 − y) r` -/
  Y : Ival
  /-- an upper bound of `v` at the corner `(a0, t0)` -/
  w0 : Int
  /-- a lower bound of `v` at the corner `(a1, t1)` -/
  w1 : Int
  /-- an upper bound of `y` at the corner `(a0, t0)` -/
  yc0 : Int
  /-- a lower bound of `y` at the corner `(a1, t1)` -/
  yc1 : Int
  /-- `R = λ e^{−Y}` -/
  R : Ival
  /-- `1 − p = 1/(1 + R)` -/
  omp : Ival
  /-- `p = 1 − 1/(1 + R)` -/
  p : Ival
  /-- `log(1 + R_lo)` -/
  y0l : Ival
  /-- `log(1 + R_hi)` -/
  y0h : Ival
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
  /-- `Z = p Z̄` -/
  pZb : Ival
  /-- `y Z` -/
  yZ : Ival
  /-- `β²` -/
  be2 : Ival
  /-- `K = 2 α Z − β² T/4` -/
  K : Ival
  /-- `δ = s − p` -/
  d : Ival
  /-- `δ²` -/
  d2 : Ival
  /-- `y₀/Y` -/
  y0Y : Ival
  /-- `u = T/y` -/
  u : Ival
  /-- the direct enclosure of `E = 1 − p + p T/y − y₀/Y` -/
  Ed : Ival
  /-- `E_f = [2δ² + (Y − y)(p + y₀/Y)]/y` (a lower bound of `E`, `EntropyOK`) -/
  Ef : Ival
  /-- the floor of `E` -/
  Elo : Int
  /-- a lower bound of `α E` -/
  aE : Int
  /-- `Q = β² δ² T/(4 y Z)` -/
  Qt : Ival
  /-- `X = σ[βγ + Lσ(γ + βT)]/Z̄` -/
  X : Ival
  /-- `W = p(3q/5 − β + p − γρ)/Y` -/
  W : Ival
  /-- `p(α Z̄ − h² s²) − h β δ s` -/
  br : Ival
  /-- `α(1 − p − y₀/Y) + W + u · br/Z̄` (BC + Q) -/
  BC : Ival

/-- The enclosures of the cell `c`. -/
def mkValsU (c : Cell) : ValsU :=
  let lam : Ival := ⟨c.a0, c.a1⟩
  let T : Ival := ⟨c.t0, c.t1⟩
  let q := sub oneI (div oneI (add oneI lam))
  let al := divNat q 2
  let be := divNat (sub lam oneI) 27
  let gam := divNat (mulNat lam 31) 100
  let E0 := expPt (-c.t0)
  let E1 := expPt (-c.t1)
  let vlo := (mul (pt c.a0) E1).lo
  let vhi := (mul (pt c.a1) E0).hi
  let yl := logPt (one + vlo)
  let yh := logPt (one + vhi)
  let y : Ival := ⟨yl.lo, yh.hi⟩
  let sl := msgPt vlo
  let sh := msgPt vhi
  let s : Ival := ⟨sl.lo, sh.hi⟩
  let sig : Ival := ⟨(div sh yh).lo, (div sl yl).hi⟩
  let Y : Ival := ⟨(yFun (pt yl.lo) (pt c.r0)).lo, (yFun (pt yh.hi) (pt c.r1)).hi⟩
  let w0 := (mul (pt c.a0) E0).hi
  let w1 := (mul (pt c.a1) E1).lo
  let yc0 := (logPt (one + w0)).hi
  let yc1 := (logPt (one + w1)).lo
  let R : Ival := ⟨(mul (pt c.a0) (expPt (-(yFun (pt yc0) (pt c.r1)).hi))).lo,
    (mul (pt c.a1) (expPt (-(yFun (pt yc1) (pt c.r0)).lo))).hi⟩
  let omp := div oneI (add oneI R)
  let p := sub oneI omp
  let y0l := logPt (one + R.lo)
  let y0h := logPt (one + R.hi)
  let y0 : Ival := ⟨y0l.lo, y0h.hi⟩
  let rho : Ival := ⟨(div (msgPt R.hi) y0h).lo, (div (msgPt R.lo) y0l).hi⟩
  let h := add omp (mul gam rho)
  let J := mul (mul s sig) T
  let Lp := sub (div gam R) (mul h Y)
  let L := meet (sub (mul gam omp) (mul (mul p h) Y)) (mul p Lp)
  let Zb := add gam (mul J Lp)
  let pZb := mul p Zb
  let yZ := mul y pZb
  let be2 := sqI be
  let K := sub (mulNat (mul al pZb) 2) (divNat (mul be2 T) 4)
  let d := sub s p
  let d2 := sqI d
  let y0Y := div y0 Y
  let u := div T y
  let Ed := sub (add omp (mul p u)) y0Y
  let Ef := div (add (mulNat d2 2) (mul (mul (sub fourI y) ⟨c.r0, c.r1⟩) (add p y0Y))) y
  let Elo := max 0 (max Ed.lo Ef.lo)
  let aE := (mul al (pt Elo)).lo
  let Qt := div (mul (mul be2 d2) T) (mulNat yZ 4)
  let X := div (mul sig (add (mul be gam) (mul (mul L sig) (add gam (mul be T))))) Zb
  let W := div (mul p (sub (add (sub (divNat (mulNat q 3) 5) be) p) (mul gam rho))) Y
  let br := sub (mul p (sub (mul al Zb) (sqI (mul h s)))) (mul (mul h be) (mul d s))
  let BC := add (add (mul al (sub omp y0Y)) W) (div (mul u br) Zb)
  { q := q, al := al, be := be, gam := gam, E0 := E0, E1 := E1, vlo := vlo, vhi := vhi, yl := yl, yh := yh,
    y := y, sl := sl, sh := sh, s := s, sig := sig, Y := Y, w0 := w0, w1 := w1, yc0 := yc0, yc1 := yc1, R := R,
    omp := omp, p := p, y0l := y0l, y0h := y0h, y0 := y0, rho := rho, h := h, J := J, Lp := Lp, L := L, Zb := Zb,
    pZb := pZb, yZ := yZ, be2 := be2, K := K, d := d, d2 := d2, y0Y := y0Y, u := u, Ed := Ed, Ef := Ef,
    Elo := Elo, aE := aE, Qt := Qt, X := X, W := W, br := br, BC := BC }

/-- The side conditions of a cell: `λ > 0`, `λ ≤ 4`, `T ≥ 0`, `0 ≤ r ≤ 1`, positive arguments of `log`, positive
divisors, and `Z̄ > 0`. -/
def sideOKU (c : Cell) (V : ValsU) : Bool :=
  decide (0 < c.a0) && decide (c.a1 ≤ 4 * one) && decide (0 ≤ c.t0) && decide (0 ≤ c.r0) &&
    decide (c.r1 ≤ one) && decide (0 < one + V.vlo) && decide (0 < one + V.vhi) && decide (0 < one + V.w0) &&
    decide (0 < one + V.w1) && decide (0 < V.yl.lo) && decide (0 < V.yh.lo) && decide (0 < V.R.lo) &&
    decide (0 < V.y0l.lo) && decide (0 < V.y0h.lo) && decide (0 < V.Y.lo) && decide (0 < V.Zb.lo) &&
    decide (0 < V.yZ.lo)

/-- **The cell check**: the side conditions (with `Z̄ > 0`), `K ≥ 0` (`β² T ≤ 8 α Z`), the lower bound of CB and
the lower bound of BC. -/
def cellOKU (c : Cell) : Bool :=
  let V := mkValsU c
  sideOKU c V && decide (0 ≤ V.K.lo) && decide (0 ≤ V.aE - V.Qt.hi + V.X.lo) &&
    decide (0 ≤ V.BC.lo - V.Qt.hi)

/-! ## The cover -/

/-- The adaptive fallback: the cell passes, or both halves along axis `j` pass (the next level splits the
next axis), at most `f` more levels. -/
def bisectOKU : Nat → Nat → Cell → Bool
  | 0, _, c => cellOKU c
  | f + 1, j, c => cellOKU c ||
      (bisectOKU f ((j + 1) % 3) (lowHalf c j) && bisectOKU f ((j + 1) % 3) (highHalf c j))

/-- The depth of the adaptive fallback at a leaf of the trie. -/
def fallbackDepthU : Nat := 6

/-- The trie walk from byte `i` of `s` over the cell `c`: the success flag and the next byte. -/
def walkU (s : String) : Nat → Nat → Cell → Bool × Nat
  | 0, i, _ => (false, i)
  | f + 1, i, c =>
    let ch := String.Pos.Raw.get s ⟨i⟩
    if ch = 'L' then (bisectOKU fallbackDepthU 0 c, i + 1)
    else
      let j := ch.toNat - 48
      let r := walkU s f (i + 1) (lowHalf c j)
      if r.1 then walkU s f r.2 (highHalf c j) else (false, r.2)

/-- The root box `[8/5, 7/3] × [0, 6] × [0, 1]` of the upper band (the end points of `λ` rounded outward). -/
def rootU : Cell := rootCell (8/5) (7/3)

/-- **The check of a sub-box**: the trie `s` covers the cell `c` with passing cells (`UpperCert.covered_of_checkAt`). -/
@[noinline] def checkAt (c : Cell) (s : String) : Bool := (walkU s walkFuel 0 c).1

/-- **The check of the upper box**: the trie `s` covers the root box `[8/5, 7/3] × [0, 6] × [0, 1]` with passing
cells (`UpperCert.upperBoxOK_of_check`). -/
@[noinline] def checkUpper (s : String) : Bool := checkAt rootU s

end Erdos993Lean.Analytic.Reserve.UpperCert.Compute
