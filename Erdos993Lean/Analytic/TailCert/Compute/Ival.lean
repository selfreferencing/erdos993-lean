/-!
# Fixed-point interval arithmetic for the T3 cell checker (lane A10): computational core

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  This module holds **only** computable
definitions; it imports nothing beyond Lean's core (`Init`), so that Lake can precompile it (library
`Erdos993LeanTailCertCompute`, `precompileModules = true`).  The proofs about these definitions
(real semantics, soundness of every operation) are in `Erdos993Lean/Analytic/TailCert/IvalSound.lean`
and `Erdos993Lean/Analytic/TailCert/ExpLog.lean`.

A fixed-point number is an integer `n`, standing for the real number `n / 2 ^ prec` (`prec = 64`).
An interval `⟨lo, hi⟩ : Ival` stands for `[lo / 2 ^ prec, hi / 2 ^ prec]`.  Every operation rounds
its lower end down and its upper end up (`fdivP`, `cdivP`, `fdiv`, `cdiv`), so an interval computed
from intervals containing `x`, `y` contains the exact result.

* `add`, `sub`, `neg`, `mul`, `div` (for a divisor interval with `0 < lo`), `divNat`, `mulNat`,
  `mulInt`, `sqr` (for `0 ≤ lo`), `ofRat` (the enclosure of a rational number);
* `expPt n` (an enclosure of `exp (n / 2 ^ prec)`): `K` halvings bring the argument into
  `[-1/2, 1/2]`, the Taylor polynomial of degree `17` with the remainder bound of `Real.exp_bound`,
  then `K` squarings;
* `logPt n` (an enclosure of `log (n / 2 ^ prec)`, `n > 0`): `n = 2 ^ b m`, `m ∈ [1, 2)`,
  `log m = 2 atanh u` with `u = (m - 1)/(m + 1) ∈ [0, 1/3)`, twenty terms of the series and the
  geometric tail bound; `log 2 = 2 atanh (1/3)` (`log2I`);
* `sqrtPt n` (an enclosure of `√(n / 2 ^ prec)`): a Newton candidate, checked (`s² ≤ N ≤ (s+1)²`).

Every definition is plain structural recursion; there is no `partial`, `unsafe`, `implemented_by`
or `extern` here.
-/

namespace Erdos993Lean.Analytic.TailCert.Compute

/-! ## Fixed-point numbers -/

/-- The number of fractional bits. -/
def prec : Nat := 64

/-- `2 ^ prec`. -/
def one : Int := 18446744073709551616

/-- `⌊a / 2 ^ prec⌋`. -/
def fdivP (a : Int) : Int := a >>> prec

/-- `⌈a / 2 ^ prec⌉`. -/
def cdivP (a : Int) : Int := -((-a) >>> prec)

/-- `⌊a / b⌋` (for `b > 0`). -/
def fdiv (a b : Int) : Int := a / b

/-- `⌈a / b⌉` (for `b > 0`). -/
def cdiv (a b : Int) : Int := -((-a) / b)

/-- A closed interval with fixed-point end points. -/
structure Ival where
  /-- the lower end point -/
  lo : Int
  /-- the upper end point -/
  hi : Int
deriving Repr, Inhabited

/-- The point interval. -/
def pt (n : Int) : Ival := ⟨n, n⟩

/-- The enclosure of a rational number. -/
def ofRat (q : Rat) : Ival := ⟨fdiv (q.num * one) q.den, cdiv (q.num * one) q.den⟩

/-- Sum. -/
def add (A B : Ival) : Ival := ⟨A.lo + B.lo, A.hi + B.hi⟩

/-- Difference. -/
def sub (A B : Ival) : Ival := ⟨A.lo - B.hi, A.hi - B.lo⟩

/-- Negation. -/
def neg (A : Ival) : Ival := ⟨-A.hi, -A.lo⟩

/-- Product (the four corner products). -/
def mul (A B : Ival) : Ival :=
  let p1 := A.lo * B.lo
  let p2 := A.lo * B.hi
  let p3 := A.hi * B.lo
  let p4 := A.hi * B.hi
  ⟨fdivP (min (min p1 p2) (min p3 p4)), cdivP (max (max p1 p2) (max p3 p4))⟩

/-- Quotient, for a divisor interval with `0 < B.lo`. -/
def div (A B : Ival) : Ival :=
  ⟨min (fdiv (A.lo * one) B.lo) (fdiv (A.lo * one) B.hi),
    max (cdiv (A.hi * one) B.lo) (cdiv (A.hi * one) B.hi)⟩

/-- Quotient by a positive natural number. -/
def divNat (A : Ival) (k : Nat) : Ival := ⟨fdiv A.lo k, cdiv A.hi k⟩

/-- Product with a natural number. -/
def mulNat (A : Ival) (k : Nat) : Ival := ⟨A.lo * k, A.hi * k⟩

/-- Product with an integer. -/
def mulInt (A : Ival) (e : Int) : Ival :=
  if 0 ≤ e then ⟨A.lo * e, A.hi * e⟩ else ⟨A.hi * e, A.lo * e⟩

/-- Square, for `0 ≤ A.lo`. -/
def sqr (A : Ival) : Ival := ⟨fdivP (A.lo * A.lo), cdivP (A.hi * A.hi)⟩

/-! ## The exponential -/

/-- `n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The number of Taylor terms of `exp`. -/
def nExp : Nat := 18

/-- `⌈2 ^ prec (nExp + 1) / (2 ^ nExp nExp! nExp)⌉`, a bound for the Taylor remainder on
`[-1/2, 1/2]`. -/
def rExp : Int := cdiv (((nExp + 1 : Nat) : Int) * one) ((2 ^ nExp * fact nExp * nExp : Nat) : Int)

/-- `(T_i, S_i)`: enclosures of `y ^ i / i!` and `∑_{k ≤ i} y ^ k / k!` for `y ∈ Y`. -/
def expLoop (Y : Ival) : Nat → Ival × Ival
  | 0 => (pt one, pt one)
  | i + 1 =>
    let p := expLoop Y i
    let T := divNat (mul p.1 Y) (i + 1)
    (T, add p.2 T)

/-- The number of halvings: `|n| < 2 ^ (prec - 1 + K)`. -/
def expShift (n : Int) : Nat := Nat.log2 n.natAbs + 2 - prec

/-- `K` squarings. -/
def sqrIter : Nat → Ival → Ival
  | 0, E => E
  | k + 1, E => sqrIter k (sqr E)

/-- An enclosure of `exp (n / 2 ^ prec)`. -/
def expPt (n : Int) : Ival :=
  let K := expShift n
  let Y : Ival := ⟨n >>> K, -((-n) >>> K)⟩
  let S := (expLoop Y (nExp - 1)).2
  sqrIter K ⟨max (S.lo - rExp) 0, S.hi + rExp⟩

/-- An enclosure of `exp x` for `x ∈ A` (`exp` is increasing). -/
def expI (A : Ival) : Ival := ⟨(expPt A.lo).lo, (expPt A.hi).hi⟩

/-! ## The logarithm -/

/-- The number of terms of the `atanh` series. -/
def nLog : Nat := 20

/-- `⌈2 ^ prec · 2 (1/3) ^ (2 nLog + 1) / ((2 nLog + 1)(8/9))⌉`, a bound for the tail of
`2 atanh u` after `nLog` terms, for `0 ≤ u ≤ 1/3`. -/
def rLog : Int := cdiv (18 * one) ((3 ^ (2 * nLog + 1) * (2 * nLog + 1) * 8 : Nat) : Int)

/-- `(T_k, S_k)`: enclosures of `u ^ (2k+1)` and `∑_{i < k} 2 u ^ (2i+1)/(2i+1)`. -/
def atanhLoop (U U2 : Ival) : Nat → Ival × Ival
  | 0 => (U, pt 0)
  | k + 1 =>
    let p := atanhLoop U U2 k
    (mul p.1 U2, add p.2 (divNat (mulNat p.1 2) (2 * k + 1)))

/-- An enclosure of `2 atanh u = log ((1 + u)/(1 − u))` for `u ∈ U`, `0 ≤ u ≤ 1/3`. -/
def atanh2 (U : Ival) : Ival :=
  let S := (atanhLoop U (mul U U) nLog).2
  ⟨S.lo, S.hi + rLog⟩

/-- An enclosure of `log 2`. -/
def log2I : Ival := atanh2 (ofRat (1 / 3))

/-- An enclosure of `log (n / 2 ^ prec)`, for `n > 0`. -/
def logPt (n : Int) : Ival :=
  let b := Nat.log2 n.toNat
  let D : Int := ((1 <<< b : Nat) : Int)
  let e : Int := (b : Int) - (prec : Int)
  let U : Ival := ⟨fdiv ((n - D) * one) (n + D), cdiv ((n - D) * one) (n + D)⟩
  add (mulInt log2I e) (atanh2 U)

/-- An enclosure of `log x` for `x ∈ A` (`0 < A.lo`). -/
def logI (A : Ival) : Ival := ⟨(logPt A.lo).lo, (logPt A.hi).hi⟩

/-! ## The square root -/

/-- Newton's iteration for `⌊√N⌋` (a candidate only; `sqrtPt` checks it). -/
def isqrtNewton : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | f + 1, N, x =>
    let y := (x + N / x) / 2
    if y < x then isqrtNewton f N y else x

/-- An enclosure of `√(n / 2 ^ prec)`, for `n ≥ 0`. -/
def sqrtPt (n : Int) : Ival :=
  let N := n.toNat * one.toNat
  let s := isqrtNewton 400 N N
  ⟨if s * s ≤ N then (s : Int) else 0, if N ≤ (s + 1) * (s + 1) then ((s + 1 : Nat) : Int)
    else ((N + 1 : Nat) : Int)⟩

/-- An enclosure of `√x` for `x ∈ A` (`0 ≤ A.lo`). -/
def sqrtI (A : Ival) : Ival := ⟨(sqrtPt A.lo).lo, (sqrtPt A.hi).hi⟩

end Erdos993Lean.Analytic.TailCert.Compute
