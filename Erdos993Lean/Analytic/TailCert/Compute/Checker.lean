import Erdos993Lean.Analytic.TailCert.Compute.Ival

/-!
# The cell checker for the repaired T3 potential (lane A10): computational core

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  Sources: `SOUL/O3/repaired_potential_proof.md`
§"Positive-domain interval checker" and §"Unbounded domains", `SOUL/O3/certify_repaired_potential.py`
(Soul's adaptive cover), `LEAN/referee/REVIEW_SOUL_ROUND2.md` item 3 (the monotonicity directions).
Imports only Lean's core; precompiled (library `Erdos993LeanTailCertCompute`).  The soundness
theorem (`checkBand_sound`, standard axioms) is in `Erdos993Lean/Analytic/TailCert/Sound.lean`.

`checkBand l0 l1 a ell z = true` certifies `Tail.T3UNonneg λ z a ℓ` for every `λ ∈ [l0, l1]`:
`U = A(Y_B, Y_C) + Y_B ψ_c(x) ≥ 0` on `Y_B > 0`, `Y_C ≥ 0`, `0 < x ≤ min(q, 1 − e^{−Y_B})`, where
`A = −log(p_c + (1 − p_c) e^{−ρ Y_B}) + (a − k) Y_C + [Y_C > 0] k That_+(Y_C) − a L(p_c)` and
`ψ_c(x) = (a T(x) + [x < q] k That_+(T(x)) − k L(x) − c x)/L(x)`.

* **Band constants** (`mkSetup`): enclosures of `l0`, `l1`, `a`; `q0lo ≤ q(l0)`, `q1hi ≥ q(l1)`;
  `k0 ≤ a r(l0)`, `k1 ≥ a r(l1)` (`r` increases); `rho ≤ ρ(l1, z)` (`ρ` decreases in `λ`);
  `cAll ≥ ℓ/q(l0)` (so `c ≤ cAll`).
* **The inner table**: the `p`-grid `xg` (`2^-46, 2^-45, …, 2^-14`, then steps of `2^-13` up to
  `q1hi`); per grid cell `[x_m, x_{m+1}]` a lower bound `alo m` of `(a T + [x < q] k That_+(T))/L − k`
  (with `T_λ(x) ≥ T_{l0}(x_{m+1})`, `That(T_λ(x)) ≥ log(l1 x_m/(l1(1 − x_m) − x_m))` for
  `x_{m+1} < q0`) and an upper bound `bhi m` of `x/L(x)` (`x/L(x)` decreases); for the c-grid
  `C_j = j dC` (`j ≤ 64`, `64 dC ≥ cAll`) the prefix minima
  `tbl j n = min(0, min_{m<n} (alo m − C_j bhi m))`.  `queryVal pm cf` interpolates concavely in `c`
  between `C_j ≤ cf ≤ C_{j+1}`: a lower bound of `ψ_c(x)` for `0 < x ≤ pm`, `0 ≤ c ≤ cf`.  Below
  `x_0 = 2^-46`, `ψ_c ≥ 0` (`tinyOK`).
* **Coordinates** (`mkCoord`): enclosures of `e^{−b}`, `e^{−ρ b}`, a lower bound of `That_{l0}(b)`,
  and `pm ≥ min(q, 1 − e^{−b})`.
* **Cells**: `lineVal` (`Y_C = 0`), `rectVal` (`Y_C ∈ [c0, c1]`, `Y_C > 0`), `stripVal` (`Y_C ≥ 30`):
  `gain + H + x-part` with the gain at `p ≤ W/(1+W)`, `W ≥ l1 e^{−(b0+c0)}` and `E ≥ e^{−ρ b0}`;
  `H = (a − k1) c0 + k0 That_{l0}(c1)_+`; `x-part = max(b1 I, a That_{l0}(b1)_+ − (k1 + cf) b1)` with
  `I = queryVal(pm(b1), cf)`, `cf ≥ c` from `h(λ, s) ≥ l0 u/(1 + l0 + l0 u)`, `u ≤ e^{−(b1+c1)}`.
  Each cell value comes with a Boolean of side conditions (`lineChk`, …: positive denominators and
  arguments of `log`, in-range table indices).
* **Cover** (`coverLine`, `coverRect`, `coverStrip`): adaptive bisection (fuel `60`) of
  `(0, 30] × {0}`, `(0, 30] × (0, 30]`, `(0, 30] × [30, ∞)`; `tailBOK` covers `Y_B ≥ 30`.

Every definition is plain structural recursion on `Nat` or `List`; there is no `partial`,
`unsafe`, `implemented_by` or `extern`.  The only compiler hint is `@[noinline]` on `checkBand`.
-/

namespace Erdos993Lean.Analytic.TailCert.Compute

/-- `f i = true` for every `i < n`. -/
def allLt : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allLt n f && f n

/-! ## The p-grid -/

/-- The p-grid: `xg i = 2 ^ (18 + i)` for `i ≤ 32` (that is `2^-46 … 2^-14`), then
`xg i = (i − 32) 2 ^ 51` (steps of `2^-13`). -/
def xg (i : Nat) : Int :=
  if i ≤ 32 then ((1 <<< (18 + i) : Nat) : Int) else (((i - 32) <<< 51 : Nat) : Int)

/-- The number of grid cells: `xg N ≥ q1hi`. -/
def gridN (q1hi : Int) : Nat := 32 + (cdiv q1hi ((1 <<< 51 : Nat) : Int)).toNat

/-- The smallest `n` with `pm ≤ xg n` among `i, i + 1, …` (a candidate; `queryChk` checks it). -/
def nIdxGeo (pm : Int) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => if xg i < pm then nIdxGeo pm f (i + 1) else i

/-- The grid index of an upper bound `pm` of `x`: the smallest `n` with `pm ≤ xg n`. -/
def nIdx (pm : Int) : Nat :=
  if pm ≤ xg 32 then nIdxGeo pm 32 0 else 32 + (cdiv pm ((1 <<< 51 : Nat) : Int)).toNat

/-! ## Band constants and the inner table -/

/-- The size of the c-grid of the inner table. -/
def jC : Nat := 64

/-- An enclosure of `r(λ) = 1 − 2/(1 + √(1 + 4λ))`. -/
def rI (lam : Rat) : Ival :=
  sub (pt one) (div (pt (2 * one)) (add (pt one) (sqrtI (ofRat (1 + 4 * lam)))))

/-- `L(x_i) = −log(1 − x_i)`. -/
def LxAt (i : Nat) : Ival := neg (logI (sub (pt one) (pt (xg i))))

/-- The argument `l0 (1 − x)/x` of `T_{l0}(x)`. -/
def TArg (L0 : Ival) (x : Int) : Ival := div (mul L0 (sub (pt one) (pt x))) (pt x)

/-- A lower bound of `T_{l0}(x) = log(l0 (1 − x)/x)`. -/
def TloAt (L0 : Ival) (x : Int) : Int := (logI (TArg L0 x)).lo

/-- The denominator `l1 (1 − x) − x` of the composed `That`. -/
def denAt (L1 : Ival) (x : Int) : Ival := sub (mul L1 (sub (pt one) (pt x))) (pt x)

/-- The argument `l1 x/(l1 (1 − x) − x)` of the composed `That` at `λ = l1`. -/
def VArg (L1 : Ival) (x : Int) : Ival := div (mul L1 (pt x)) (denAt L1 x)

/-- A lower bound of `That(T_λ(x)) = log(λ x/(λ(1 − x) − x))` at `λ = l1`, `x = x_m`. -/
def VAt (L1 : Ival) (x : Int) : Int := (logI (VArg L1 x)).lo

/-- The That credit of grid cell `m`: `k0 max(V, 0)/L(x_{m+1})` when `x_{m+1} < q0`. -/
def kthAt (L1 : Ival) (q0lo k0 : Int) (Lx : Array Ival) (m : Nat) : Int :=
  if xg (m + 1) < q0lo then
    if 0 < VAt L1 (xg m) then
      (div (mul (pt k0) (pt (VAt L1 (xg m)))) (pt (Lx.getD (m + 1) default).hi)).lo
    else 0
  else 0

/-- The lower bound `alo m` of `(a T + [x < q] k That_+(T))/L − k` on grid cell `m`. -/
def aloAt (L0 L1 A : Ival) (q0lo k0 k1 : Int) (Lx : Array Ival) (m : Nat) : Int :=
  (div (mul A (pt (TloAt L0 (xg (m + 1)))))
      ⟨(Lx.getD m default).lo, (Lx.getD (m + 1) default).hi⟩).lo +
    kthAt L1 q0lo k0 Lx m - k1

/-- The upper bound `bhi m = x_m/L(x_m)` of `x/L(x)` on grid cell `m`. -/
def bhiAt (Lx : Array Ival) (m : Nat) : Int := (div (pt (xg m)) (Lx.getD m default)).hi

/-- The value of grid cell `m` at `c = C`: `alo m − C bhi m`, rounded down. -/
def cellV (alo bhi : Array Int) (C : Int) (m : Nat) : Int := alo.getD m 0 - cdivP (C * bhi.getD m 0)

/-- The running minima `[acc, min acc (f m), min acc (f m) (f (m+1)), …]` (`k + 1` entries). -/
def pmins (f : Nat → Int) : Nat → Nat → Int → List Int
  | 0, _, acc => [acc]
  | k + 1, m, acc => acc :: pmins f k (m + 1) (min acc (f m))

/-- Row `C` of the inner table: the prefix minima `min(0, min_{m<n} (alo m − C bhi m))`,
`n = 0, …, N`. -/
def tblRow (alo bhi : Array Int) (N : Nat) (C : Int) : Array Int :=
  (pmins (cellV alo bhi C) N 0 0).toArray

/-- The band constants and the inner table. -/
structure Setup where
  /-- the lower band edge -/
  l0 : Rat
  /-- the upper band edge -/
  l1 : Rat
  /-- the coefficient `a` of the potential -/
  a : Rat
  /-- the rate `ℓ` -/
  ell : Rat
  /-- the Laplace parameter `z` -/
  z : Rat
  /-- enclosure of `l0` -/
  L0 : Ival
  /-- enclosure of `l1` -/
  L1 : Ival
  /-- enclosure of `a` -/
  A : Ival
  /-- lower bound of `q(l0)` -/
  q0lo : Int
  /-- upper bound of `q(l1)` -/
  q1hi : Int
  /-- lower bound of `a r(l0)` -/
  k0 : Int
  /-- upper bound of `a r(l1)` -/
  k1 : Int
  /-- lower bound of `ρ(l1, z)` -/
  rho : Int
  /-- upper bound of `ℓ/q(l0)` -/
  cAll : Int
  /-- the step of the c-grid -/
  dC : Int
  /-- the number of grid cells -/
  N : Nat
  /-- enclosures of `L(x_i)` -/
  Lx : Array Ival
  /-- the lower bounds `alo m` -/
  alo : Array Int
  /-- the upper bounds `bhi m` -/
  bhi : Array Int
  /-- the inner table -/
  tbl : Array (Array Int)
  /-- enclosure of `e^{−30}` -/
  e30 : Ival
  /-- enclosure of `log(1 + l1)` -/
  log1l1 : Ival

/-- `ρ(l1, z) = log((1 + l1)/(1 + l1 z))/log(1 + l1)`, rounded down and clamped at `0`. -/
def rhoOf (l1 z : Rat) : Int :=
  max (div (logI (ofRat ((1 + l1) / (1 + l1 * z)))) (logI (ofRat (1 + l1)))).lo 0

/-- The band constants and the inner table of `[l0, l1]`, `a`, `ℓ`, `z`. -/
def mkSetup (l0 l1 a ell z : Rat) : Setup :=
  let L0 := ofRat l0
  let L1 := ofRat l1
  let A := ofRat a
  let q0lo := (ofRat (l0 / (1 + l0))).lo
  let q1hi := (ofRat (l1 / (1 + l1))).hi
  let k0 := (mul A (rI l0)).lo
  let k1 := (mul A (rI l1)).hi
  let cAll := (ofRat (ell * (1 + l0) / l0)).hi
  let dC := cdiv cAll jC
  let N := gridN q1hi
  let Lx := (List.range (N + 1)).toArray.map LxAt
  let alo := (List.range N).toArray.map (aloAt L0 L1 A q0lo k0 k1 Lx)
  let bhi := (List.range N).toArray.map (bhiAt Lx)
  let tbl := (List.range (jC + 1)).toArray.map (fun (j : Nat) => tblRow alo bhi N ((j : Int) * dC))
  { l0 := l0, l1 := l1, a := a, ell := ell, z := z, L0 := L0, L1 := L1, A := A, q0lo := q0lo,
    q1hi := q1hi, k0 := k0, k1 := k1, rho := rhoOf l1 z, cAll := cAll, dC := dC, N := N, Lx := Lx,
    alo := alo, bhi := bhi, tbl := tbl, e30 := expPt (-(30 * one)),
    log1l1 := logI (ofRat (1 + l1)) }

/-- The side conditions of grid cell `m`: `0 < x_{m+1} < 1`, a positive enclosure of `L(x_m)`, a
positive argument of `T_{l0}(x_{m+1})`, and (when the That credit is used) a positive denominator
and argument of the composed `That`. -/
def pcellOK (S : Setup) (m : Nat) : Bool :=
  decide (xg m < one) && decide (xg (m + 1) < one) && decide (0 < (S.Lx.getD m default).lo) &&
    decide (0 < (TArg S.L0 (xg (m + 1))).lo) &&
    (decide (S.q0lo ≤ xg (m + 1)) ||
      (decide (0 < (denAt S.L1 (xg m)).lo) && decide (0 < (VArg S.L1 (xg m)).lo)))

/-- The tiny region `x ≤ x_0 = 2^-46`: `a T_{l0}(x_0) − (k1 + C_64) L(x_0) ≥ 0`. -/
def tinyOK (S : Setup) : Bool :=
  decide (0 < (TArg S.L0 (xg 0)).lo) &&
    decide (0 ≤ (sub (mul S.A (pt (TloAt S.L0 (xg 0))))
      (mul (pt (S.k1 + (jC : Int) * S.dC)) (pt (S.Lx.getD 0 default).hi))).lo)

/-- The global side conditions of the band constants and the inner table. -/
def setupOK (S : Setup) : Bool :=
  decide (0 < S.l0) && decide (S.l0 ≤ S.l1) && decide (S.l1 ≤ 6) && decide (0 ≤ S.z) &&
    decide (S.z ≤ 1) && decide (0 ≤ S.a) && decide (0 ≤ S.ell) && decide (0 ≤ S.k0) &&
    decide (S.k1 ≤ S.A.lo) && decide (0 < S.dC) && decide (0 < (logI (ofRat (1 + S.l1))).lo) &&
    decide (0 < (ofRat (1 + S.l1)).lo) && decide (0 < (ofRat ((1 + S.l1) / (1 + S.l1 * S.z))).lo) &&
    decide (0 ≤ (ofRat (1 + 4 * S.l0)).lo) && decide (0 ≤ (ofRat (1 + 4 * S.l1)).lo) &&
    allLt S.N (pcellOK S) && tinyOK S

/-! ## The query of the inner table -/

/-- The c-grid index `j` with `C_j ≤ cf ≤ C_{j+1}` (clamped to `j ≤ 63`). -/
def qJ (dC cf : Int) : Nat := min ((max cf 0) / dC).toNat (jC - 1)

/-- `cf − C_j`. -/
def qRem (dC cf : Int) : Int := cf - (qJ dC cf : Int) * dC

/-- The table entry `tbl j n`. -/
def tget (tbl : Array (Array Int)) (j n : Nat) : Int := (tbl.getD j #[]).getD n 0

/-- The interpolated table value: a lower bound of `ψ_c(x)` for `0 < x ≤ pm`, `0 ≤ c ≤ cf`. -/
def queryVal (S : Setup) (pm cf : Int) : Int :=
  tget S.tbl (qJ S.dC cf) (nIdx pm) +
    fdiv (qRem S.dC cf * (tget S.tbl (qJ S.dC cf + 1) (nIdx pm) - tget S.tbl (qJ S.dC cf) (nIdx pm)))
      S.dC

/-- The side conditions of the query: `pm ≤ x_n ≤ x_N` and `0 ≤ cf − C_j ≤ dC`. -/
def queryChk (S : Setup) (pm cf : Int) : Bool :=
  decide (nIdx pm ≤ S.N) && decide (pm ≤ xg (nIdx pm)) && decide (0 ≤ qRem S.dC cf) &&
    decide (qRem S.dC cf ≤ S.dC)

/-! ## Coordinates -/

/-- A coordinate `b` (of `Y_B` or `Y_C`) with enclosures of the functions of `b` the cells use. -/
structure Coord where
  /-- the coordinate -/
  b : Int
  /-- enclosure of `e^{−b}` -/
  eb : Ival
  /-- enclosure of `e^{−ρ b}` -/
  er : Ival
  /-- upper bound of `min(q(l1), 1 − e^{−b})` -/
  pm : Int
  /-- lower bound of `That_{l0}(b)` (valid when `thok`) -/
  th : Int
  /-- validity of `th` -/
  thok : Bool

/-- `e^b − 1` from an enclosure of `e^{−b}`. -/
def thDen (eb : Ival) : Ival := sub (div (pt one) eb) (pt one)

/-- `l0/(e^b − 1)`. -/
def thArg (L0 eb : Ival) : Ival := div L0 (thDen eb)

/-- The data of the coordinate `b`. -/
def mkCoord (S : Setup) (b : Int) : Coord :=
  let eb := expPt (-b)
  { b := b, eb := eb, er := expI (neg (mul (pt S.rho) (pt b))), pm := min S.q1hi (one - eb.lo),
    th := (logI (thArg S.L0 eb)).lo,
    thok := decide (0 < b) && decide (0 < eb.lo) && decide (0 < (thDen eb).lo) &&
      decide (0 < (thArg S.L0 eb).lo) }

/-! ## The cells -/

/-- The upper bound of `p = W/(1 + W)`. -/
def pUp (W : Int) : Int := (div (pt W) (add (pt one) (pt W))).hi

/-- `p + (1 − p) E`. -/
def gainArg (Pp Er : Int) : Ival := add (pt Pp) (mul (sub (pt one) (pt Pp)) (pt Er))

/-- A lower bound of `−log(p + (1 − p) E) − a L(p)` for `p ≤ W/(1 + W)`, `E ≤ Er`. -/
def gainVal (A : Ival) (W Er : Int) : Int :=
  (neg (logI (gainArg (pUp W) Er))).lo + (mul A (logI (sub (pt one) (pt (pUp W))))).lo

/-- The side conditions of `gainVal`. -/
def gainChk (W Er : Int) : Bool :=
  decide (0 ≤ W) && decide (0 < (gainArg (pUp W) Er).lo) && decide (pUp W < one)

/-- The denominator `1 + l0 + l0 u` of the lower bound of `h`. -/
def hDen (L0 : Ival) (U1 : Int) : Ival := add (add (pt one) L0) (mul L0 (pt U1))

/-- A lower bound of `h(λ, s) = λ e^{−s}/(1 + λ + λ e^{−s})` from `u ≤ e^{−s}`: `l0 u/(1 + l0 + l0 u)`. -/
def hLo (L0 : Ival) (U1 : Int) : Int := (div (mul L0 (pt U1)) (hDen L0 U1)).lo

/-- The side conditions of `hLo`. -/
def hChk (L0 : Ival) (U1 : Int) : Bool := decide (0 ≤ U1) && decide (0 < (hDen L0 U1).lo)

/-- The upper bound `cAll (1 − h)` of `c = (ℓ/q)(1 − h)`. -/
def cfOf (cAll : Int) (L0 : Ival) (U1 : Int) : Int := (mul (pt cAll) (sub (pt one) (pt (hLo L0 U1)))).hi

/-- The near bound `a That_{l0}(b1)_+ − (k1 + cf) b1`. -/
def nearVal (S : Setup) (th b1 cf : Int) : Int :=
  (mul S.A (pt (max th 0))).lo - cdivP ((S.k1 + cf) * b1)

/-- The lower bound of `Y_B ψ_c(x)`: `max(b1 I, near)`. -/
def xpartVal (S : Setup) (B1 : Coord) (cf : Int) : Int :=
  if B1.thok then max (fdivP (B1.b * queryVal S B1.pm cf)) (nearVal S B1.th B1.b cf)
  else fdivP (B1.b * queryVal S B1.pm cf)

/-- The line `Y_C = 0`, `Y_B ∈ [b0, b1]`: the lower bound of `U`. -/
def lineVal (S : Setup) (B0 B1 : Coord) : Int :=
  gainVal S.A (mul S.L1 B0.eb).hi B0.er.hi + xpartVal S B1 (cfOf S.cAll S.L0 B1.eb.lo)

/-- The side conditions of `lineVal`. -/
def lineChk (S : Setup) (B0 B1 : Coord) : Bool :=
  gainChk (mul S.L1 B0.eb).hi B0.er.hi && hChk S.L0 B1.eb.lo &&
    queryChk S B1.pm (cfOf S.cAll S.L0 B1.eb.lo) && decide (0 ≤ B0.b)

/-- The certified line cell. -/
def lineOK (S : Setup) (B0 B1 : Coord) : Bool := lineChk S B0 B1 && decide (0 ≤ lineVal S B0 B1)

/-- `H = (a − k1) c0 + k0 That_{l0}(c1)_+`. -/
def HVal (S : Setup) (C0 C1 : Coord) : Int :=
  (mul (sub S.A (pt S.k1)) (pt C0.b)).lo +
    (if C1.thok && decide (0 < C1.th) then (mul (pt S.k0) (pt C1.th)).lo else 0)

/-- The rectangle `Y_B ∈ [b0, b1]`, `Y_C ∈ [c0, c1]`, `Y_C > 0`: the lower bound of `U`. -/
def rectVal (S : Setup) (B0 B1 C0 C1 : Coord) : Int :=
  gainVal S.A (mul S.L1 (mul B0.eb C0.eb)).hi B0.er.hi + HVal S C0 C1 +
    xpartVal S B1 (cfOf S.cAll S.L0 (mul B1.eb C1.eb).lo)

/-- The side conditions of `rectVal`. -/
def rectChk (S : Setup) (B0 B1 C0 C1 : Coord) : Bool :=
  gainChk (mul S.L1 (mul B0.eb C0.eb)).hi B0.er.hi && hChk S.L0 (mul B1.eb C1.eb).lo &&
    queryChk S B1.pm (cfOf S.cAll S.L0 (mul B1.eb C1.eb).lo) && decide (0 ≤ B0.b) &&
    decide (0 ≤ C0.b)

/-- The certified rectangle. -/
def rectOK (S : Setup) (B0 B1 C0 C1 : Coord) : Bool :=
  rectChk S B0 B1 C0 C1 && decide (0 ≤ rectVal S B0 B1 C0 C1)

/-- The strip `Y_B ∈ [b0, b1]`, `Y_C ≥ 30`: the lower bound of `U`. -/
def stripVal (S : Setup) (B0 B1 : Coord) : Int :=
  gainVal S.A (mul S.L1 (mul B0.eb S.e30)).hi B0.er.hi + (mul (sub S.A (pt S.k1)) (pt (30 * one))).lo +
    xpartVal S B1 S.cAll

/-- The side conditions of `stripVal`. -/
def stripChk (S : Setup) (B0 B1 : Coord) : Bool :=
  gainChk (mul S.L1 (mul B0.eb S.e30)).hi B0.er.hi && queryChk S B1.pm S.cAll && decide (0 ≤ B0.b)

/-- The certified strip. -/
def stripOK (S : Setup) (B0 B1 : Coord) : Bool := stripChk S B0 B1 && decide (0 ≤ stripVal S B0 B1)

/-! ## The adaptive cover -/

/-- The midpoint of two coordinates. -/
def mid (S : Setup) (B0 B1 : Coord) : Coord := mkCoord S ((B0.b + B1.b) >>> 1)

/-- The line `Y_C = 0` over `Y_B ∈ [b0, b1]`, by bisection. -/
def coverLine (S : Setup) : Nat → Coord → Coord → Bool
  | 0, B0, B1 => lineOK S B0 B1
  | f + 1, B0, B1 => lineOK S B0 B1 ||
      (let M := mid S B0 B1
       coverLine S f B0 M && coverLine S f M B1)

/-- The strip `Y_C ≥ 30` over `Y_B ∈ [b0, b1]`, by bisection. -/
def coverStrip (S : Setup) : Nat → Coord → Coord → Bool
  | 0, B0, B1 => stripOK S B0 B1
  | f + 1, B0, B1 => stripOK S B0 B1 ||
      (let M := mid S B0 B1
       coverStrip S f B0 M && coverStrip S f M B1)

/-- The rectangle `[b0, b1] × [c0, c1]`, by quadrisection. -/
def coverRect (S : Setup) : Nat → Coord → Coord → Coord → Coord → Bool
  | 0, B0, B1, C0, C1 => rectOK S B0 B1 C0 C1
  | f + 1, B0, B1, C0, C1 => rectOK S B0 B1 C0 C1 ||
      (let MB := mid S B0 B1
       let MC := mid S C0 C1
       coverRect S f B0 MB C0 MC && coverRect S f MB B1 C0 MC &&
         coverRect S f B0 MB MC C1 && coverRect S f MB B1 MC C1)

/-- The tail `Y_B ≥ 30`: `ρ + I > 0` and `30 (ρ + I) − log(1 + l1) − a log(1 + l1 e^{−30}) ≥ 0`,
with `I` the table value at `pm = q1hi`, `cf = cAll`. -/
def tailBOK (S : Setup) : Bool :=
  queryChk S S.q1hi S.cAll && decide (0 < S.rho + queryVal S S.q1hi S.cAll) &&
    decide (0 < (add (pt one) (mul S.L1 S.e30)).lo) &&
    decide (0 ≤ (sub (sub (mul (pt (30 * one)) (pt (S.rho + queryVal S S.q1hi S.cAll))) S.log1l1)
      (mul S.A (logI (add (pt one) (mul S.L1 S.e30))))).lo)

/-- The fuel of the bisections. -/
def fuel : Nat := 60

/-- **The band check**: `Tail.T3UNonneg λ z a ℓ` for every `λ ∈ [l0, l1]` (`checkBand_sound`). -/
@[noinline] def checkBand (l0 l1 a ell z : Rat) : Bool :=
  let S := mkSetup l0 l1 a ell z
  let B0 := mkCoord S 0
  let B1 := mkCoord S (30 * one)
  setupOK S && coverLine S fuel B0 B1 && coverRect S fuel B0 B1 B0 B1 && coverStrip S fuel B0 B1 &&
    tailBOK S

end Erdos993Lean.Analytic.TailCert.Compute
