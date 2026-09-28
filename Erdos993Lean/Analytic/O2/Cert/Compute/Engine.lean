import Erdos993Lean.Analytic.O2.Cert.Compute.Arith

/-!
# O2 certificate checker (lane A18): the cell evaluator, the cover walk and the band check

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  Sources: Pro's R2 "tight" engine
(`SOUL/O2_FINAL/R2_PACKET/ypoly_tight.py`, `common_tight.py`, `ad_tight.py`, `interval_tight.py`,
`bernstein_tight.py`; the mathematics in `SOUL/O2_FINAL/ASSEMBLY/PRO_R2_PROOF.md` §6–§9).  Exact Python mirror:
`LEAN/lanes/A18/scratch/mirror.py`.  Lean core and lane A10's interval core only (precompiled library
`Erdos993LeanO2CertCompute`); the soundness proofs are in `Erdos993Lean/Analytic/O2/Cert/*Sound*.lean`.

A cell is a box `[l0, l1] × [x0, x1]` of the activity `λ` and of `x = p/q`.  For every parent case (`lab`) the
normalized parent marginal `Y = (1 − r)/q ∈ [0, P]`, `P = (1 − p)/(1 − qp)`, is cut into pieces on which the
retained source and the parent fields are affine in `Y`; on a piece the three response quadratics of the payment
(`PRO_R2_PROOF.md` (13)) have coefficients of degree `≤ 2` in the piece coordinate, and their degree-2 Bernstein
controls are checked with the centered (mean-value) form in `(λ, x)` (anchors are re-evaluations of the same
functions at a corner or the midpoint), with de Casteljau subdivision up to three levels.

Deviations from Pro's engine (each makes the soundness proof simpler and is mirrored exactly in `mirror.py`):
lane A10's logarithm; a field is evaluated by one segment formula `c_j + (c_{j+1} − c_j)(8X − j)` at a point
provably inside segment `j` (per-segment pieces for the parent case `Y`, the parent point `P` clamped to its
segment); cuts are inserted into sorted lists (`insertL`) instead of a bubble sort; the box-level branch
choices (kernel branch, low mode, the formula of the crossover cut, the piece recipes) are reused at the anchors.

Every definition is plain structural recursion; there is no `partial`, `unsafe`, `implemented_by` or `extern`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Compute

open Erdos993Lean.Analytic.TailCert.Compute

/-! ## Band data -/

/-- The rational data of one band (the tables at `λ = lo` (`L…`) and `λ = hi` (`R…`), nine knots each). -/
structure SegData where
  /-- left activity edge -/
  lo : Rat
  /-- right activity edge -/
  hi : Rat
  /-- the price `γ` -/
  gamma : Rat
  /-- knots of `u` at `lo` -/
  Lu : Array Rat
  /-- knots of `v` at `lo` -/
  Lv : Array Rat
  /-- knots of `s` at `lo` -/
  Ls : Array Rat
  /-- knots of `τ` at `lo` -/
  Ltau : Array Rat
  /-- `w` at `lo` -/
  Lw : Rat
  /-- `ℓ` at `lo` -/
  Lell : Rat
  /-- knots of `u` at `hi` -/
  Ru : Array Rat
  /-- knots of `v` at `hi` -/
  Rv : Array Rat
  /-- knots of `s` at `hi` -/
  Rs : Array Rat
  /-- knots of `τ` at `hi` -/
  Rtau : Array Rat
  /-- `w` at `hi` -/
  Rw : Rat
  /-- `ℓ` at `hi` -/
  Rell : Rat

/-- The coefficient fields at the activity dual number `λ` (knot values linear in `λ`). -/
structure Coeffs where
  /-- knots of `u` -/
  u : Array DN
  /-- knots of `v` -/
  v : Array DN
  /-- knots of `s` -/
  s : Array DN
  /-- knots of `τ` -/
  tau : Array DN
  /-- `w` -/
  w : DN
  /-- `ℓ` -/
  ell : DN
  /-- the price `c = γ/(1 + λ)` -/
  C : DN

/-- One knot value `l + ww (r − l)` (`ww = (λ − lo)/(hi − lo)`). -/
def knotDN (ww : DN) (l r : Rat) : DN := daddI (dmulI ww (sub (ofRat r) (ofRat l))) (ofRat l)

/-- The nine knot values of one table pair. -/
def knotTab (ww : DN) (L R : Array Rat) : Array DN := (Array.range 9).map (fun j => knotDN ww L[j]! R[j]!)

/-- The coefficient fields at `λ`. -/
def coefficients (sd : SegData) (lam : DN) : Coeffs :=
  let ww := ddivI (dsubI lam (ofRat sd.lo)) (ofRat (sd.hi - sd.lo))
  { u := knotTab ww sd.Lu sd.Ru
    v := knotTab ww sd.Lv sd.Rv
    s := knotTab ww sd.Ls sd.Rs
    tau := knotTab ww sd.Ltau sd.Rtau
    w := knotDN ww sd.Lw sd.Rw
    ell := knotDN ww sd.Lell sd.Rell
    C := dmulI (ddiv oneDN (daddI lam oneI)) (ofRat sd.gamma) }

/-! ## One segment of the piecewise-linear fields -/

/-- `F_j(X) = c_j + (c_{j+1} − c_j)(8X − j)`, the field on segment `j`. -/
def interpSeg (vals : Array DN) (X : DN) (j : Nat) : DN :=
  dadd (vals.getD j zeroDN)
    (dmul (dsub (vals.getD (j + 1) zeroDN) (vals.getD j zeroDN)) (dsubI (dmulI X eightI) (pt (j * one))))

/-- The segment `j` with `j/8 ≤ X.lo` and `X.hi ≤ (j+1)/8`, if any. -/
def segOf (X : Ival) : Option Nat :=
  let j := (max 0 (min 7 (fdivP (8 * X.lo)))).toNat
  if decide ((j : Int) * eighth ≤ X.lo) && decide (X.hi ≤ ((j : Int) + 1) * eighth) then some j
  else if decide (1 ≤ j) && decide (((j : Int) - 1) * eighth ≤ X.lo) && decide (X.hi ≤ (j : Int) * eighth) then
    some (j - 1)
  else none

/-- The field at the box coordinate `x` (whose box lies in one segment). -/
def interpX (vals : Array DN) (X : DN) : DN :=
  match segOf X.v with
  | some j => interpSeg vals X j
  | none => ⟨zI, zI, zI, false⟩

/-- `clamp(Y, s/8, (s+1)/8)`. -/
def clampSeg (Y : DN) (s : Nat) : DN := mx (DN.cst (knotI s)) (mn (DN.cst (knotI (s + 1))) Y)

/-! ## The context of a cell -/

/-- The box-level branch choices, reused at the anchors: the kernel branch (`x ≥ 7/8`), the low mode (the source
is the first affine piece), and the formula of the crossover cut (`0`, `1`, `2`; `3` = decide). -/
structure Flags where
  /-- kernel branch -/
  kern : Bool
  /-- low mode -/
  low : Bool
  /-- formula of the crossover cut `Y_o` -/
  y0b : Nat

/-- The values of a cell (or of an anchor point). -/
structure Ctx where
  /-- the coefficient fields -/
  co : Coeffs
  /-- `λ` -/
  lam : DN
  /-- `x = p/q` -/
  x : DN
  /-- `q = λ/(1+λ)` -/
  q : DN
  /-- `p = qx` -/
  p : DN
  /-- `e = 1 − x` -/
  e : DN
  /-- `P = (1 − p)/(1 − qp)` -/
  upper : DN
  /-- `h = p/(−log(1 − p))` -/
  hp : DN
  /-- `G = log((1+λ)x/(1+λe)²)` -/
  G : DN
  /-- `τ(x)` -/
  tau : DN
  /-- `A_u = u(x)/(pT)` -/
  au : DN
  /-- `A_v = v(x)/(pT)` -/
  av : DN
  /-- `s(x)/H` -/
  so : DN
  /-- `φ` -/
  phi : DN
  /-- `H_c/q` -/
  hn : DN
  /-- the source cuts `[Y_f, Y_M, Y_o]` (empty in low mode) -/
  cuts : List DN
  /-- low mode -/
  low : Bool
  /-- the formula used for `Y_o` -/
  y0b : Nat

/-- `(jm, bb^jm)`: iterate `b ↦ b·bb` while `(b·bb).hi ≤ aa.lo`. -/
def jLow (aa bb : DN) : Nat → Nat → DN → Nat × DN
  | 0, j, b => (j, b)
  | f + 1, j, b =>
    let nb := dmul b bb
    if nb.v.hi ≤ aa.v.lo then jLow aa bb f (j + 1) nb else (j, b)

/-- `(jM, stopped)`: iterate `b ↦ b·bb` while `(b·bb).lo < aa.hi`; `stopped` if the loop ended by its test. -/
def jHigh (aa bb : DN) : Nat → Nat → DN → Nat × Bool
  | 0, j, _ => (j, false)
  | f + 1, j, b =>
    let nb := dmul b bb
    if nb.v.lo < aa.v.hi then jHigh aa bb f (j + 1) nb else (j, true)

/-- `bb^j` by repeated products. -/
def dpow (bb : DN) : Nat → DN
  | 0 => oneDN
  | j + 1 => dmul (dpow bb j) bb

/-- The packing values `H_j = jλ + aa/bb^j − 1` and `φ_j = jq + 1 − bb^j/aa`. -/
def packHV (lam q aa bb : DN) (j : Nat) : DN × DN :=
  let bj := dpow bb j
  (dsubI (dadd (dmulI lam (pt (j * one))) (ddiv aa bj)) oneI,
    dsub (daddI (dmulI q (pt (j * one))) oneI) (ddiv bj aa))

/-- The hulls of `H_j`, `φ_j` over `j = j0, …, j0 + k`. -/
def packHull (lam q aa bb : DN) (j0 : Nat) : Nat → DN × DN
  | 0 => packHV lam q aa bb j0
  | k + 1 =>
    let t := packHull lam q aa bb j0 k
    let n := packHV lam q aa bb (j0 + k + 1)
    (dhull t.1 n.1, dhull t.2 n.2)

/-- The packed child masses `(H, φ)` (`aa = λ(1−p)/p`, `bb = 1 + λ`), hulls over every possible `j`. -/
def packing (lam q aa bb : DN) : DN × DN :=
  let lo := jLow aa bb 64 0 oneDN
  let hi := jHigh aa bb 64 lo.1 lo.2
  let t := packHull lam q aa bb lo.1 (hi.1 - lo.1)
  ({ t.1 with ok := t.1.ok && hi.2 }, { t.2 with ok := t.2.ok && hi.2 })

/-- **The context** at the dual numbers `λ`, `x` with the branch choices `fl`. -/
def context (sd : SegData) (lam x : DN) (fl : Flags) : Ctx :=
  let co := coefficients sd lam
  let lam1 := daddI lam oneI
  let q := ddiv lam lam1
  let p := dmul q x
  let e := drsubI oneI x
  let omp := drsubI oneI p
  let upper := ddiv omp (drsubI oneI (dmul q p))
  let hp := ddiv p (dneg (dlog omp))
  let le1 := daddI (dmul lam e) oneI
  let G := dlog (ddiv (dmul lam1 x) (dmul le1 le1))
  let tau := interpX co.tau x
  let own : DN × DN × DN × DN :=
    if fl.kern then
      let pte := dmul p (kernel e lam)
      (ddiv (dmulI (co.u.getD 7 zeroDN) eightI) pte, ddiv (dmulI (co.v.getD 7 zeroDN) eightI) pte,
        ddiv (dmul (dmulI (co.s.getD 7 zeroDN) eightI) x) lam1, ddiv (dmul lam1 e) le1)
    else
      let aa := ddiv le1 x
      let pT := dmul p (dlog aa)
      let pk := packing lam q aa lam1
      (ddiv (interpX co.u x) pT, ddiv (interpX co.v x) pT, ddiv (interpX co.s x) pk.1, pk.2)
  let hn := mn oneDN (ddiv (dmul (dmul lam1 lam1) e) (dmul lam le1))
  let hc := dmul hn q
  let kap := ddiv oneDN (daddI q oneI)
  let y0b := if fl.y0b ≤ 2 then fl.y0b
    else if kap.v.hi ≤ x.v.lo then 0 else if x.v.hi ≤ kap.v.lo then 1 else 2
  let cuts : List DN :=
    if fl.low then []
    else
      let nn := mx zeroDN (dsub x kap)
      let yfa := ddiv nn p
      let yM := ddiv (dmul kap nn) (mx nn (dmul (dmul (dmul kap p) q) hc))
      let y0 :=
        if y0b = 0 then ddiv e (dmul q (drsubI oneI (dmul p hc)))
        else if y0b = 1 then upper
        else ddiv (dmul hn omp) (drsubI oneI (dmul p hc))
      [yfa, yM, y0]
  { co := co, lam := lam, x := x, q := q, p := p, e := e, upper := upper, hp := hp, G := G, tau := tau,
    au := own.1, av := own.2.1, so := own.2.2.1, phi := own.2.2.2, hn := hn, cuts := cuts, low := fl.low,
    y0b := y0b }

/-! ## The retained source -/

/-- `f(a) = max(αa, a − β(1 − a))`, `α = 1 − 1/(2(1+λ))`, `β = 1/(2λ)` (so `f(a) = f_q(qa)`). -/
def fnorm (a lam : DN) : DN :=
  let alpha := drsubI oneI (ddiv oneDN (dmulI (daddI lam oneI) twoI))
  let beta := ddiv oneDN (dmulI lam twoI)
  dmax (dmul alpha a) (dsub a (dmul beta (drsubI oneI a)))

/-- The retained-source lower bound at `Y` (`r = 1 − qY`): `αxr` in low mode, else
`(1 + f(xr) − f(max(Y, (1 − pr) H_c/q)))/2`. -/
def source (c : Ctx) (Y : DN) : DN :=
  let r := drsubI oneI (dmul c.q Y)
  if c.low then
    dmul (dmul c.x r) (drsubI oneI (ddiv oneDN (dmulI (daddI c.lam oneI) twoI)))
  else
    let fa := fnorm (dmul c.x r) c.lam
    let M := mx Y (dmul (drsubI oneI (dmul c.p r)) c.hn)
    ddivI (dsub (daddI fa oneI) (fnorm M c.lam)) twoI

/-! ## Pieces -/

/-- The middle of the insertion of `c` into a sorted list: `max(lᵢ₋₁, min(lᵢ, c))`. -/
def insMid (c : DN) : List DN → List DN
  | a :: b :: rest => mx a (mn b c) :: insMid c (b :: rest)
  | _ => []

/-- The last element (or `0`). -/
def lastD : List DN → DN
  | [] => zeroDN
  | [a] => a
  | _ :: b :: rest => lastD (b :: rest)

/-- Insert `c` (already clipped to `[l₀, lₙ]`) into the sorted list `Ls`. -/
def insertL (Ls : List DN) (c : DN) : List DN :=
  match Ls with
  | [] => []
  | l0 :: _ => l0 :: (insMid c Ls ++ [lastD Ls])

/-- The cut `z` possibly lies strictly inside `[a, b]`. -/
def overlaps (z a b : DN) : Bool := !(decide (z.v.hi ≤ a.v.lo) || decide (b.v.hi ≤ z.v.lo))

/-- The indices (from `ci`) of the cuts that possibly lie strictly inside `[a, b]`. -/
def usedCuts (a b : DN) : List DN → Nat → List Nat
  | [], _ => []
  | z :: zs, ci => if overlaps z a b then ci :: usedCuts a b zs (ci + 1) else usedCuts a b zs (ci + 1)

/-- Insert the cuts whose indices are listed in `used` into the sorted list `Ls` (clipped to `[a, b]`). -/
def insertCuts (a b : DN) (used : List Nat) : List DN → Nat → List DN → List DN
  | [], _, Ls => Ls
  | z :: zs, ci, Ls =>
    insertCuts a b used zs (ci + 1) (if used.contains ci then insertL Ls (mx a (mn b z)) else Ls)

/-- The recipe of the pieces of one parent case (decided at the cell, reused at the anchors). -/
inductive Recipe where
  /-- parent `Y`: the segments used and the cuts inserted in each -/
  | low (segs : List Nat) (used : List (List Nat))
  /-- parent knot or `P`: the cuts inserted -/
  | other (used : List Nat)

/-- The segment-`s` portion `[min(s/8, P), min((s+1)/8, P)]`. -/
def portion (c : Ctx) (s : Nat) : DN × DN := (mn (DN.cst (knotI s)) c.upper, mn (DN.cst (knotI (s + 1))) c.upper)

/-- The upper end of the `Y` range of a parent knot or `P` case: `min(P, j/8)` or `min(P, (j+1)/8)`. -/
def highOf (c : Ctx) (lab : Nat × Nat) : DN :=
  if lab.1 = 1 then mn c.upper (DN.cst (knotI lab.2)) else mn c.upper (DN.cst (knotI (lab.2 + 1)))

/-- The recipe of the parent case `lab` at the cell. -/
def recipeOf (c : Ctx) (lab : Nat × Nat) : Recipe :=
  if lab.1 = 0 then
    let segs := (List.range 8).filter (fun (s : Nat) => decide ((s : Int) * eighth < c.upper.v.hi))
    .low segs (segs.map (fun s => usedCuts (portion c s).1 (portion c s).2 c.cuts 0))
  else .other (usedCuts zeroDN (highOf c lab) c.cuts 0)

/-- The pieces of the parent case `lab = (kind, j)` by the recipe `rec` (`kind` `0`: `t/q = Y`; `1`: `t/q = j/8`,
`Y ≤ min(P, j/8)`; `2`: `t/q = P` clamped to segment `j`, `Y ≤ min(P, (j+1)/8)`): the sorted lists of piece ends,
with their segment. -/
def listsOf (c : Ctx) (lab : Nat × Nat) (rec : Recipe) : List (Nat × List DN) :=
  match rec with
  | .low segs used =>
    segs.zipIdx.map (fun sn =>
      let ab := portion c sn.1
      (sn.1, insertCuts ab.1 ab.2 (used.getD sn.2 []) c.cuts 0 [ab.1, ab.2]))
  | .other used => [(0, insertCuts zeroDN (highOf c lab) used c.cuts 0 [zeroDN, highOf c lab])]

/-- The parent cases of a cell: `Y`; `P` in each segment it may meet; the knots `j/8 ≤ P`. -/
def labelsOf (c : Ctx) : List (Nat × Nat) :=
  let lo := (max 0 (min 7 (fdivP (8 * c.upper.v.lo)))).toNat
  let hi := (max 0 (min 7 (fdivP (8 * c.upper.v.hi)))).toNat
  [(0, 0)] ++ (List.range' lo (hi + 1 - lo)).map (fun s => (2, s)) ++
    ((List.range' 1 7).filter (fun (j : Nat) => decide ((j : Int) * eighth ≤ c.upper.v.hi))).map (fun j => (1, j))

/-! ## Bernstein polynomials in the piece coordinate (coefficient lists of degree ≤ 2) -/

/-- The interval `1/2`. -/
def halfI : Ival := ofRat (1 / 2)

/-- Degree elevation to degree `n` (`n ≤ 2`). -/
def belev (c : List DN) (n : Nat) : List DN :=
  match c with
  | [a] => if n = 0 then [a] else if n = 1 then [a, a] else [a, dadd (dmulI a halfI) (dmulI a halfI), a]
  | [a, b] => if n ≤ 1 then [a, b] else [a, dadd (dmulI a halfI) (dmulI b halfI), b]
  | l => l

/-- Sum. -/
def badd (a b : List DN) : List DN :=
  let n := max a.length b.length - 1
  List.zipWith dadd (belev a n) (belev b n)

/-- Negation. -/
def bneg (a : List DN) : List DN := a.map dneg

/-- Difference. -/
def bsub (a b : List DN) : List DN := badd a (bneg b)

/-- Product (degree `0` by anything, or `1` by `1`). -/
def bmul (a b : List DN) : List DN :=
  match a, b with
  | a, [b0] => a.map (fun v => dmul v b0)
  | [a0], b => b.map (fun v => dmul a0 v)
  | [a0, a1], [b0, b1] => [dmul a0 b0, ddivI (dadd (dmul a0 b1) (dmul a1 b0)) twoI, dmul a1 b1]
  | _, _ => []

/-- One Bernstein control of a response quadratic: the coefficients `(A, B, E)` of `Aη² + Bη + E`. -/
structure Tri where
  /-- leading coefficient -/
  A : DN
  /-- linear coefficient -/
  B : DN
  /-- constant coefficient -/
  E : DN

/-- The three controls of a triple of degree-2 lists. -/
def controls (A B E : List DN) : List Tri :=
  let a := belev A 2
  let b := belev B 2
  let e := belev E 2
  [⟨a.getD 0 zeroDN, b.getD 0 zeroDN, e.getD 0 zeroDN⟩, ⟨a.getD 1 zeroDN, b.getD 1 zeroDN, e.getD 1 zeroDN⟩,
    ⟨a.getD 2 zeroDN, b.getD 2 zeroDN, e.getD 2 zeroDN⟩]

/-- The degree-1 list `[f(ya), f(yb)]`. -/
def lin (a b : DN) : List DN := [a, b]

/-- **The controls of the three response quadratics** on the piece `[ya, yb]` of the parent case `lab`
(segment `s` for `lab = (0, _)`): parts `0` (`z ≤ 0`), `1` (`0 ≤ z ≤ 1`), `2` (`z ≥ 1`). -/
def triples (c : Ctx) (lab : Nat × Nat) (s : Nat) (ya yb : DN) : List (List Tri) :=
  let co := c.co
  let r := lin (drsubI oneI (dmul c.q ya)) (drsubI oneI (dmul c.q yb))
  let gs := lin (source c ya) (source c yb)
  let par : Array DN → List DN := fun f =>
    if lab.1 = 1 then [f.getD lab.2 zeroDN]
    else if lab.1 = 2 then [interpSeg f (clampSeg c.upper lab.2) lab.2]
    else lin (interpSeg f (clampSeg ya s) s) (interpSeg f (clampSeg yb s) s)
  let ut := par co.u
  let vt := par co.v
  let st := par co.s
  let tt := par co.tau
  let omp := [drsubI oneI c.p]
  let omr := bsub [oneDN] r
  let nu := badd (badd (bmul r omp) (bmul ut [c.hp])) (bmul (bmul omr st) omp)
  let nv := badd (badd (bmul r omp) (bmul vt [c.hp])) (bmul (bmul omr st) omp)
  let beta := badd (badd (bmul r [c.tau]) (bmul omr tt)) [co.w]
  let ss := bmul r [c.so]
  let elG := [ddiv (dmul co.ell c.G) c.p]
  let rgC := bmul (bmul r gs) [co.C]
  let rphw := bmul (bmul r [c.phi]) [co.w]
  let d1 := bsub (badd (badd (bsub rgC nv) (bmul omr tt)) rphw) elG
  let d0 := badd (badd (bsub (badd (bsub (bsub rgC (bmul r [c.tau])) [co.w]) rphw) elG) [c.av]) ss
  let ssav := badd ss [c.av]
  let two := [DN.cst twoI]
  [controls (bsub ssav nu) (bsub (bmul ssav two) beta) d0,
    controls (bsub ssav nv) (bsub (bmul nv two) beta) d1,
    controls (bsub (badd ss [c.au]) nv) (bsub beta (bmul nv two)) d1]

/-! ## de Casteljau subdivision of the controls -/

/-- The midpoint of two controls. -/
def halfT (a b : Tri) : Tri :=
  ⟨ddivI (dadd a.A b.A) twoI, ddivI (dadd a.B b.B) twoI, ddivI (dadd a.E b.E) twoI⟩

/-- de Casteljau at `1/2`: the controls of the two halves. -/
def splitP (poly : List Tri) : List Tri × List Tri :=
  match poly with
  | [c0, c1, c2] =>
    let ab := halfT c0 c1
    let bc := halfT c1 c2
    let mid := halfT ab bc
    ([c0, ab, mid], [mid, bc, c2])
  | _ => (poly, poly)

/-- The controls after the subdivision path (`false` = left half). -/
def subP (poly : List Tri) : List Bool → List Tri
  | [] => poly
  | d :: ds => subP (if d then (splitP poly).2 else (splitP poly).1) ds

/-! ## The quadratic tests with centered lower bounds -/

/-- The derived quantities of a control (`0` `A`, `1` `B`, `2` `E`, `3` `A+B+E`, `4` `2A+B`, `5` `E+B/2`,
`6` `4AE − B²`, `7` `E − B²/(4A)` for `A > 0`). -/
def derive (t : Tri) (k : Nat) : DN :=
  match k with
  | 0 => t.A
  | 1 => t.B
  | 2 => t.E
  | 3 => dadd (dadd t.A t.B) t.E
  | 4 => dadd (dmulI t.A twoI) t.B
  | 5 => dadd t.E (ddivI t.B twoI)
  | 6 => dsub (dmul (dmulI t.A fourI) t.E) (dsq t.B)
  | _ =>
    let eta := div (neg t.B.v) (mul twoI t.A.v)
    let s2 := sqI eta
    ⟨sub t.E.v (div (sqI t.B.v) (mul fourI t.A.v)),
      add (add t.E.d0 (mul eta t.B.d0)) (mul s2 t.A.d0),
      add (add t.E.d1 (mul eta t.B.d1)) (mul s2 t.A.d1),
      t.A.ok && t.B.ok && t.E.ok && decide (0 < t.A.v.lo)⟩

/-- The box of a cell and its anchors. -/
structure BoxCtx where
  /-- the `λ` interval -/
  lamI : Ival
  /-- the `x` interval -/
  xI : Ival
  /-- `⌈(λ₁ − λ₀)/2⌉` (fixed point) -/
  radL : Int
  /-- `⌈(x₁ − x₀)/2⌉` (fixed point) -/
  radX : Int

/-- The anchor code of one coordinate and its remainder: `−1` (slope `≥ 0`: the lower end), `1` (slope `≤ 0`:
the upper end), `0` (the midpoint, remainder `⌈max|slope| · rad⌉`). -/
def codeOf (d : Ival) (rad : Int) : Int × Int :=
  if rad = 0 then (0, 0)
  else if 0 ≤ d.lo then (-1, 0)
  else if d.hi ≤ 0 then (1, 0)
  else (0, cdivP (((max d.lo.natAbs d.hi.natAbs : Nat) : Int) * rad))

/-- **The centered lower bound** of the derived quantity `k` of the control `t` (negated if `neg`) over the box;
`anchor code` is the same control re-evaluated at the anchor point `code`.  Returns `-1` on a failed side
condition. -/
def lowerB (bx : BoxCtx) (anchor : Nat → Tri) (t : Tri) (k : Nat) (neg : Bool) : Int :=
  let e0 := derive t k
  let expr := if neg then dneg e0 else e0
  if !expr.ok then -1
  else if 0 ≤ expr.v.lo then expr.v.lo
  else
    let c0 := codeOf expr.d0 bx.radL
    let c1 := codeOf expr.d1 bx.radX
    let e1 := derive (anchor ((c0.1 + 1) * 3 + (c1.1 + 1)).toNat) k
    let ec := if neg then dneg e1 else e1
    if !ec.ok then expr.v.lo else max expr.v.lo (ec.v.lo - (c0.2 + c1.2))

/-- **The quadratic test** of one control on the response range of `part` (`0`, `2`: a half-line; `1`: `[0, 1]`). -/
def quad (bx : BoxCtx) (anchor : Nat → Tri) (t : Tri) (part : Nat) : Bool :=
  let lb := fun k => lowerB bx anchor t k false
  let ub := fun k => -lowerB bx anchor t k true
  if lb 2 < 0 then false
  else if part ≠ 1 then
    if lb 0 < 0 then false
    else if 0 ≤ lb 1 then true
    else (decide (0 < t.A.v.lo) && decide (0 ≤ lb 7)) || decide (0 ≤ lb 6)
  else if lb 3 < 0 then false
  else if ub 0 ≤ 0 then true
  else if 0 ≤ lb 5 then true
  else if decide (0 ≤ lb 1) && decide (0 ≤ lb 4) then true
  else if decide (ub 1 ≤ 0) && decide (ub 4 ≤ 0) then true
  else decide (0 < lb 0) && ((decide (0 < t.A.v.lo) && decide (0 ≤ lb 7)) || decide (0 ≤ lb 6))

/-- All controls of `poly` pass (`anch path j code`: control `j` after `path` at the anchor `code`). -/
def allQuad (bx : BoxCtx) (anch : List Bool → Nat → Nat → Tri) (path : List Bool) (part : Nat) :
    List Tri → Nat → Bool
  | [], _ => true
  | t :: ts, j => quad bx (anch path j) t part && allQuad bx anch path part ts (j + 1)

/-- The first control of a list (or a default). -/
def headT (poly : List Tri) : Tri := poly.headD ⟨zeroDN, zeroDN, zeroDN⟩

/-- **The part check** with de Casteljau subdivision (at most `lvl` more levels). -/
def partcheck (bx : BoxCtx) (anch : List Bool → Nat → Nat → Tri) (part : Nat) :
    Nat → List Bool → List Tri → Bool
  | 0, path, poly => allQuad bx anch path part poly 0
  | lvl + 1, path, poly =>
    allQuad bx anch path part poly 0 ||
      (quad bx (anch path 0) (headT poly) part && quad bx (anch path 2) (headT (poly.drop 2)) part &&
        partcheck bx anch part lvl (path ++ [false]) (splitP poly).1 &&
        partcheck bx anch part lvl (path ++ [true]) (splitP poly).2)

/-! ## The cell -/

/-- The anchor point of code `code` (`code / 3`: `λ`, `code % 3`: `x`; `0` lower end, `1` midpoint, `2` upper end). -/
def anchorPt (A : Ival) (c : Nat) : Int := if c = 0 then A.lo else if c = 2 then A.hi else (A.lo + A.hi) / 2

/-- A point coordinate with zero slope seeds (at an anchor point the slopes are not used, and zero intervals keep
their arithmetic in small integers). -/
def ptDN (a : Int) : DN := ⟨pt a, zI, zI, true⟩

/-- The anchor context of code `code` (values only: the slope seeds are zero). -/
def anchorCtx (sd : SegData) (bx : BoxCtx) (fl : Flags) (code : Nat) : Ctx :=
  context sd (ptDN (anchorPt bx.lamI (code / 3))) (ptDN (anchorPt bx.xI (code % 3))) fl

/-- The `k`-th piece `[Ls[k], Ls[k+1]]` of a list. -/
def pieceAt (Ls : List DN) (k : Nat) : DN × DN := (Ls.getD k zeroDN, Ls.getD (k + 1) zeroDN)

/-- The anchor context of code `code`, from the memo array `anc` (the default is the same value). -/
def ancGet (sd : SegData) (bx : BoxCtx) (fl : Flags) (anc : Array (Thunk Ctx)) (code : Nat) : Ctx :=
  (anc.getD code (Thunk.mk (fun _ => anchorCtx sd bx fl code))).get

/-- The piece lists of the parent case `lab` at the anchor `code` (the cell's recipe is reused). -/
def anchorLists (sd : SegData) (bx : BoxCtx) (fl : Flags) (anc : Array (Thunk Ctx)) (lab : Nat × Nat)
    (rec : Recipe) (code : Nat) : List (Nat × List DN) :=
  listsOf (ancGet sd bx fl anc code) lab rec

/-- The anchor piece lists of `lab`, from the memo array `al` (the default is the same value). -/
def alGet (sd : SegData) (bx : BoxCtx) (fl : Flags) (anc : Array (Thunk Ctx)) (lab : Nat × Nat) (rec : Recipe)
    (al : Array (Thunk (List (Nat × List DN)))) (code : Nat) : List (Nat × List DN) :=
  (al.getD code (Thunk.mk (fun _ => anchorLists sd bx fl anc lab rec code))).get

/-- The controls of the piece `(lab, n, k)` at the anchor `code`. -/
def anchorTriples (sd : SegData) (bx : BoxCtx) (fl : Flags) (anc : Array (Thunk Ctx)) (lab : Nat × Nat)
    (rec : Recipe) (al : Array (Thunk (List (Nat × List DN)))) (n k code : Nat) : List (List Tri) :=
  let sL := (alGet sd bx fl anc lab rec al code).getD n (0, [])
  let pc := pieceAt sL.2 k
  triples (ancGet sd bx fl anc code) lab sL.1 pc.1 pc.2

/-- One piece: all three parts pass (`n`: list index, `k`: piece index). -/
def pieceOK (sd : SegData) (bx : BoxCtx) (fl : Flags) (anc : Array (Thunk Ctx)) (lab : Nat × Nat)
    (rec : Recipe) (al : Array (Thunk (List (Nat × List DN)))) (n k : Nat) (poly : List (List Tri)) : Bool :=
  let anchT : Array (Thunk (List (List Tri))) :=
    (Array.range 9).map (fun code => Thunk.mk (fun _ => anchorTriples sd bx fl anc lab rec al n k code))
  let anch : Nat → List Bool → Nat → Nat → Tri := fun part path j code =>
    (subP (((anchT.getD code (Thunk.mk (fun _ => anchorTriples sd bx fl anc lab rec al n k code))).get).getD
      part []) path).getD j ⟨zeroDN, zeroDN, zeroDN⟩
  (List.range 3).all (fun part => partcheck bx (anch part) part 3 [] (poly.getD part []))

/-- **The cell check** on the box `[l0, l1] × [x0, x1]`. -/
def boxOK (sd : SegData) (l0 l1 x0 x1 : Rat) : Bool :=
  let lamI : Ival := ⟨(ofRat l0).lo, (ofRat l1).hi⟩
  let xI : Ival := ⟨(ofRat x0).lo, (ofRat x1).hi⟩
  let bx : BoxCtx := ⟨lamI, xI, (lamI.hi - lamI.lo + 1) / 2, (xI.hi - xI.lo + 1) / 2⟩
  let kern := decide (7 * eighth ≤ xI.lo)
  let thr := div (add oneI lamI) (add oneI (mul twoI lamI))
  let low := decide (xI.hi ≤ thr.lo)
  let c := context sd (lamDN lamI) (xDN xI) ⟨kern, low, 3⟩
  let fl : Flags := ⟨kern, low, c.y0b⟩
  let anc : Array (Thunk Ctx) := (Array.range 9).map (fun code => Thunk.mk (fun _ => anchorCtx sd bx fl code))
  decide (0 < lamI.lo) && decide (lamI.lo ≤ lamI.hi) && decide (0 < xI.lo) && decide (xI.lo ≤ xI.hi) &&
    decide (xI.hi ≤ one) && (kern || decide (xI.hi < one)) &&
  (labelsOf c).all (fun lab =>
    let rcp := recipeOf c lab
    let al : Array (Thunk (List (Nat × List DN))) :=
      (Array.range 9).map (fun code => Thunk.mk (fun _ => anchorLists sd bx fl anc lab rcp code))
    (listsOf c lab rcp).zipIdx.all (fun sLn =>
      (List.range (sLn.1.2.length - 1)).all (fun k =>
        let pc := pieceAt sLn.1.2 k
        pieceOK sd bx fl anc lab rcp al sLn.2 k (triples c lab sLn.1.1 pc.1 pc.2))))

/-- The cell check with a fallback bisection (the wider side in relative width, at most `f` levels). -/
def boxFB (sd : SegData) : Nat → Rat → Rat → Rat → Rat → Bool
  | 0, l0, l1, x0, x1 => boxOK sd l0 l1 x0 x1
  | f + 1, l0, l1, x0, x1 =>
    boxOK sd l0 l1 x0 x1 ||
      (if (x1 - x0) / (1 + x0) ≤ (l1 - l0) / (1 + l0) then
        boxFB sd f l0 ((l0 + l1) / 2) x0 x1 && boxFB sd f ((l0 + l1) / 2) l1 x0 x1
      else boxFB sd f l0 l1 x0 ((x0 + x1) / 2) && boxFB sd f l0 l1 ((x0 + x1) / 2) x1)

/-- The fallback depth of a leaf. -/
def fallbackDepth : Nat := 4

/-- **The cover walk**: the preorder token string `s` from byte `i` over the box (`'l'`: split `λ`, `'x'`: split
`x`, lower half first; `'r'`: a leaf, checked by `boxFB`).  Returns the success flag and the next byte. -/
def walk (sd : SegData) (s : String) : Nat → Nat → Rat → Rat → Rat → Rat → Bool × Nat
  | 0, i, _, _, _, _ => (false, i)
  | f + 1, i, l0, l1, x0, x1 =>
    let ch := String.Pos.Raw.get s ⟨i⟩
    if ch = 'r' then (boxFB sd fallbackDepth l0 l1 x0 x1, i + 1)
    else if ch = 'l' then
      let r := walk sd s f (i + 1) l0 ((l0 + l1) / 2) x0 x1
      if r.1 then walk sd s f r.2 ((l0 + l1) / 2) l1 x0 x1 else (false, r.2)
    else if ch = 'x' then
      let r := walk sd s f (i + 1) l0 l1 x0 ((x0 + x1) / 2)
      if r.1 then walk sd s f r.2 l0 l1 ((x0 + x1) / 2) x1 else (false, r.2)
    else (false, i)

/-- The `x` edges of the twelve root boxes. -/
def edges : List Rat := [1/65536, 1/4096, 1/1024, 1/256, 1/64, 1/8, 2/8, 3/8, 4/8, 5/8, 6/8, 7/8, 1]

/-- One root box `[lo, hi] × [edges[i], edges[i+1]]` is covered by the token string `s`. -/
def rootOK (sd : SegData) (i : Nat) (s : String) : Bool :=
  let w := walk sd s 64 0 sd.lo sd.hi (edges.getD i 0) (edges.getD (i + 1) 0)
  w.1 && decide (w.2 = s.length)

/-- The guards on the band data used by the soundness proof. -/
def guardOK (sd : SegData) : Bool :=
  decide (0 < sd.lo) && decide (sd.lo < sd.hi) && decide (sd.hi ≤ 7 / 3) && decide (0 < sd.gamma) &&
    decide (sd.Lu.size = 9) && decide (sd.Lv.size = 9) && decide (sd.Ls.size = 9) && decide (sd.Ltau.size = 9) &&
    decide (sd.Ru.size = 9) && decide (sd.Rv.size = 9) && decide (sd.Rs.size = 9) && decide (sd.Rtau.size = 9) &&
    decide (sd.Lu[8]! = 0) && decide (sd.Lv[8]! = 0) && decide (sd.Ls[8]! = 0) &&
    decide (sd.Ru[8]! = 0) && decide (sd.Rv[8]! = 0) && decide (sd.Rs[8]! = 0)

/-- **The band check**: the guards, and the twelve root boxes covered by the twelve token strings. -/
@[noinline] def checkBand (sd : SegData) (toks : List String) : Bool :=
  guardOK sd && decide (toks.length = 12) && (List.range 12).all (fun i => rootOK sd i (toks.getD i ""))

/-- The check of one root box only (used to split the band check into several modules). -/
@[noinline] def checkRoot (sd : SegData) (i : Nat) (s : String) : Bool := rootOK sd i s

end Erdos993Lean.Analytic.O2.Cert.Compute
