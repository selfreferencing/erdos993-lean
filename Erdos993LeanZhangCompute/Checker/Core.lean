/-!
# Zhang's finite-part certificates: computational core

This module holds **only** the computable definitions behind the certificate checks of T. Zhang's
finite part (every forest with at most 60 vertices is unimodal; *Exact Certificates for Unimodality
of Forest Independence Polynomials*, v1.1, Sections 2.7–2.10).  It imports nothing beyond Lean's
core (`Init`), so that Lake can precompile it into a native shared library (library
`Erdos993LeanZhangCompute` in `lakefile.toml`, `precompileModules = true`).  All the proofs about
these definitions are in `Erdos993Lean/ZhangCert/Bridge.lean`, which connects them to the
statement layer `Erdos993Lean/Zhang/Relaxation.lean` (namespace `Erdos993Lean.Zhang.Cert`).

**Integer mirrors of the statement layer.**  Every row of `Relaxation.lean` has integer
coefficients and right side (over `ℚ` there).  The functions below compute them over `Int`,
following the definitions of `Relaxation.lean` term by term (same case splits, same natural-number
subtractions), with the binomial `binomN` (a table of `C(i, j)`, `i, j < 64`, filled by the
falling-factorial formula `binomF`) in place of `Nat.choose`:
`binomZ` (`Cert.binom`), `posZ` (`Cert.pos`), `BZ` (`Cert.B`), `hallCZ`, `bStepZ`, `sExtZ`, `UZ`,
`VtZ`, `βZ`, `C0Z`, `GrZ`; `coefZ n a ℓ j m` and `rhsZ n a ℓ` are the coefficient `a^ℓ_{j,m}` and
the right side `b^ℓ` of the row `ℓ` (a `CLabel`: the eleven families of `Cert.Label` and the row
`assumption(k)`).

**Generic certificate.**  A generic certificate for a triple `(n, a, k)` is a kind (`pos`: prove
`Δ_k > 0`; `neg`: prove `Δ_{k+1} ≤ 0`; `cond`: prove `Δ_{k+1} ≤ 0` from `Δ_k ≤ 0`), a target
scale `σ > 0` and a list of rows with natural weights `w`.  With the target `q = σ·(−B(k))` or
`q = σ·B(k+1)` (`tgtZ`, `tgt0Z`), the residual of the variable `(j, m)` is
`W_j (q_{j,m} − Σ w a_{j,m}) − [j = 1] η` (`preZ`), `M_j = max(0, max_m residual)` (`layerMax`),
and the bound (`boundWith`) is `q_0 + Σ w b + η + Σ_{j=1}^{v} M_j`: Zhang's certificate principle
(40) in the form `Cert.certificate_bound` with all row scales `1` and multipliers `w`.  The free
constant `η` is taken as the largest layer-1 residual without `η` (`autoEta`), which makes
`M_1 = 0`; any value is sound, and this one is never worse than a stored `η`.
`genericOK` checks `v ≥ 1`, `σ > 0`, that every row is on its domain (`rowOKB`; `assumption(k')`
only with `k' = k` in a conditional certificate), and the sign of the bound (`< 0` for `pos`,
`≤ 0` otherwise).

**The stored data** (`Checker/Data*.lean`, one string of numbers per order `n`) is parsed by
`tokens`, `parseRows`, `parseEntries`.  A separator `t = p/q` becomes the conditional certificate
with target scale `q` and the single row `assumption(k)` of weight `p`.  A linear certificate
(`kind`, `D`, rows with multipliers `mult`) becomes a generic one with the author's normalization
(39) reproduced exactly (`scaleTarget`, `scaleRow`, `linearToGeneric`): with `N_Q`, `N_ρ` the
scales and `L = lcm(N_Q, N_ρ, …)`, `σ = D·L/N_Q` and `w_ρ = mult_ρ·L/N_ρ`.  A triple without a
stored certificate is tried with the direct criteria of (36)–(37), each a generic certificate:
the path row `path(k)` with weight `1` (the path-vs-matching comparison, `k ≥ 2`), no rows with
kind `pos` (the lower layer rule), no rows with kind `neg` (the upper layer rule).  None of the
parsing, normalization or choice of certificate matters for soundness: the bridge proves that
`genericOK n a k kind σ rows = true` implies `Cert.NoRecovery n a k` for **every** kind, `σ` and
row list.

Every definition is plain structural recursion on `Nat` or `List` (or a fold); there is no
`partial`, `unsafe`, `implemented_by` or `extern` here.
-/

namespace Erdos993Lean

namespace ZhangCertX

/-! ### Binomial coefficients -/

/-- The falling factorial `n (n − 1) ⋯ (n − k + 1)`. -/
def descF (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n - k) * descF n k

/-- The factorial. -/
def factN : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factN k

/-- `C(n, k)` by the falling factorial formula. -/
def binomF (n k : Nat) : Nat := descF n k / factN k

/-- The table of `C(i, j)` for `i, j < 64`. -/
def binomTab : Array (Array Nat) :=
  Array.ofFn (n := 64) fun i => Array.ofFn (n := 64) fun j => binomF i.val j.val

/-- `C(n, k)`: a table lookup for `n, k < 64`, the formula otherwise. -/
def binomN (n k : Nat) : Nat :=
  if n < 64 ∧ k < 64 then (binomTab.getD n #[]).getD k 0 else binomF n k

/-- The paper's binomial over the integers: `C(b, r)` if `0 ≤ r ≤ b`, else `0`
(the integer mirror of `Cert.binom`). -/
def binomZ (b r : Int) : Int :=
  if 0 ≤ r ∧ r ≤ b then (binomN b.toNat r.toNat : Int) else 0

/-- `x_+ = max(x, 0)` (the mirror of `Cert.pos`). -/
def posZ (x : Int) : Int := max x 0

/-! ### Parameters (the mirrors of `Cert.v`, `Cert.δ`, `Cert.E`, `Cert.D0`) -/

/-- `v = n − a`. -/
def vP (n a : Nat) : Nat := n - a

/-- `δ = a − v`. -/
def δP (n a : Nat) : Nat := a - vP n a

/-- `E = max(0, δ − 1)`. -/
def EP (n a : Nat) : Nat := δP n a - 1

/-- `D_0 = min(E, v − 1)`. -/
def D0P (n a : Nat) : Nat := min (EP n a) (vP n a - 1)

/-! ### The auxiliary functions of the rows (mirrors of `Relaxation.lean`) -/

/-- `B_{m,j}(k) = C(m, k − j) − C(m, k − j − 1)`. -/
def BZ (m j k : Nat) : Int := binomZ m ((k : Int) - j) - binomZ m ((k : Int) - j - 1)

/-- The factor `c = v − r − max(0, l − δ)` of `hall(r, l)`. -/
def hallCZ (n a r l : Nat) : Int := (vP n a : Int) - r - max 0 ((l : Int) - δP n a)

/-- `b_{r,h}(m)` (14). -/
def bStepZ (a r h m : Nat) : Int :=
  if h ≤ m then (r : Int) else if r * h ≤ a + (r - 1) * m then 1 else 0

/-- `s_r = max(0, v − r + 1 − E)` (16). -/
def sExtZ (n a r : Nat) : Int := posZ ((vP n a : Int) - r + 1 - EP n a)

/-- `U_{r,h}(m)` (17). -/
def UZ (a r h m : Nat) : Int :=
  let d : Nat := a - m
  let L : Nat := d + 1 - r
  let q : Nat := d / L
  let ρ : Nat := d % L
  (q : Int) * posZ ((m : Int) + L - h) +
    (if q < r then posZ ((m : Int) + ρ - h) + ((r - q - 1 : Nat) : Int) * posZ ((m : Int) - h)
      else 0)

/-- `V_{r,h}(m)` (18). -/
def VtZ (a r h m : Nat) : Int :=
  let d : Nat := a - m
  let L : Nat := d + 1 - r
  if h ≤ m then (r : Int) else if h ≤ m + L then ((min r (d / (h - m)) : Nat) : Int) else 0

/-- `β_r = C(v−2, r−1) − (a−2) C(v−2, r−2)` (22). -/
def βZ (n a r : Nat) : Int :=
  binomZ ((vP n a : Int) - 2) ((r : Int) - 1) -
    ((a : Int) - 2) * binomZ ((vP n a : Int) - 2) ((r : Int) - 2)

/-- `C_r^0 = a C(v−2, r) + (δ + 1) C(v−2, r−1)` (22). -/
def C0Z (n a r : Nat) : Int :=
  (a : Int) * binomZ ((vP n a : Int) - 2) r +
    ((δP n a : Int) + 1) * binomZ ((vP n a : Int) - 2) ((r : Int) - 1)

/-- `G_r = C(v−1, r−1) − C(v − D_0 − 1, r−1)` (27). -/
def GrZ (n a r : Nat) : Int :=
  binomZ ((vP n a : Int) - 1) ((r : Int) - 1) -
    binomZ ((vP n a : Int) - D0P n a - 1) ((r : Int) - 1)

/-! ### Row labels, coefficients, right sides, domains -/

/-- The row labels: the eleven families of `Cert.Label` (`priv` is the paper's `private`) and
the row `assumption(k)` of a conditional certificate. -/
inductive CLabel where
  | count (r : Nat)
  | path (r : Nat)
  | priv (r h : Nat)
  | hall (r l : Nat)
  | tail (r h : Nat)
  | releaseUpper (r h : Nat)
  | tailUpper (r h : Nat)
  | mean (r : Nat)
  | union (r : Nat)
  | edgeLower (r : Nat)
  | edgeUpper (r : Nat)
  | assumption (k : Nat)
  deriving Repr, Inhabited

/-- The coefficient `a^ℓ_{j,m}` of the row `ℓ` (the integer mirror of `Cert.Label.row` and
`Cert.assumptionRow`). -/
def coefZ (n a : Nat) : CLabel → Nat → Nat → Int
  | .count r, j, _ => if j = r then 1 else 0
  | .path r, j, m => -binomZ m ((r : Int) - j)
  | .priv r h, j, m =>
      (if j = r then posZ (((r : Int) - 1) * m + a - r + 1 - r * h) else 0) -
        (if j = r - 1 then ((vP n a : Int) - r + 1) * posZ ((m : Int) - h) else 0)
  | .hall r l, j, m =>
      ((if j = r + 1 then (r : Int) + 1 else 0) - (if j = r then hallCZ n a r l else 0)) *
        binomZ m l
  | .tail r h, j, m =>
      (if j = r then bStepZ a r h m else 0) -
        (if j = r - 1 ∧ h ≤ m then (vP n a : Int) - r + 1 else 0)
  | .releaseUpper r h, j, m =>
      (if j = r - 1 then sExtZ n a r * posZ ((m : Int) - h) else 0) -
        (if j = r then UZ a r h m else 0)
  | .tailUpper r h, j, m =>
      (if j = r - 1 ∧ h ≤ m then sExtZ n a r else 0) - (if j = r then VtZ a r h m else 0)
  | .mean r, j, m => -(if j = r then (m : Int) else 0) - (if j = 2 then βZ n a r else 0)
  | .union r, j, m => ((a : Int) - m) *
      ((if j = r then 1 else 0) -
        (if j = 1 then binomZ ((vP n a : Int) - 1) ((r : Int) - 1) else 0))
  | .edgeLower r, j, _ =>
      -(if j = r then 1 else 0) + (if j = 2 then binomZ ((vP n a : Int) - 2) ((r : Int) - 2) else 0)
  | .edgeUpper r, j, _ => (if j = r then (D0P n a : Int) else 0) - (if j = 2 then GrZ n a r else 0)
  | .assumption k, j, m => BZ m j k

/-- The right side `b^ℓ` of the row `ℓ`. -/
def rhsZ (n a : Nat) : CLabel → Int
  | .count r => binomZ (vP n a) r
  | .path r => binomZ a r - binomZ ((n : Int) - r + 1) r
  | .priv _ _ => 0
  | .hall r l => if r = 0 then hallCZ n a r l * binomZ a l else 0
  | .tail _ _ => 0
  | .releaseUpper _ _ => 0
  | .tailUpper _ _ => 0
  | .mean r => -C0Z n a r - βZ n a r * binomZ (vP n a) 2
  | .union _ => 0
  | .edgeLower r =>
      -binomZ (vP n a) r + binomZ ((vP n a : Int) - 2) ((r : Int) - 2) * binomZ (vP n a) 2
  | .edgeUpper r => (D0P n a : Int) * binomZ (vP n a) r - GrZ n a r * binomZ (vP n a) 2
  | .assumption k => -BZ a 0 k

/-- The layers `j` on which the row `ℓ` may have a nonzero coefficient (`coefZ` vanishes on the
others; `path` and `assumption` are dense). -/
def touches : CLabel → Nat → Bool
  | .count r, j => j == r
  | .path _, _ => true
  | .priv r _, j => j == r || j == r - 1
  | .hall r _, j => j == r + 1 || j == r
  | .tail r _, j => j == r || j == r - 1
  | .releaseUpper r _, j => j == r - 1 || j == r
  | .tailUpper r _, j => j == r - 1 || j == r
  | .mean r, j => j == r || j == 2
  | .union r, j => j == r || j == 1
  | .edgeLower r, j => j == r || j == 2
  | .edgeUpper r, j => j == r || j == 2
  | .assumption _, _ => true

/-- The three kinds of linear certificates: `pos` proves `Δ_k > 0`, `neg` proves
`Δ_{k+1} ≤ 0`, `cond` proves `Δ_{k+1} ≤ 0` under `Δ_k ≤ 0`. -/
inductive Kind where
  | pos
  | neg
  | cond
  deriving DecidableEq, Repr, Inhabited

/-- The row `ℓ` may be used in a certificate of kind `kind` for `(n, a, k)`: a family row on its
parameter domain (the mirror of `Cert.Label.InDomain`), or `assumption(k)` itself in a
conditional certificate. -/
def rowOKB (n a k : Nat) (kind : Kind) : CLabel → Bool
  | .count r => decide (2 ≤ r ∧ r ≤ vP n a)
  | .path r => decide (2 ≤ r ∧ r ≤ a)
  | .priv r h => decide (2 ≤ r ∧ r ≤ vP n a ∧ h < a)
  | .hall r l =>
      decide (l ≤ a ∧ r < min (vP n a) (a - l) ∧ 0 ≤ hallCZ n a r l ∧ (l = 0 → 1 ≤ r))
  | .tail r h => decide (2 ≤ r ∧ r ≤ vP n a ∧ h ≤ a - r + 1)
  | .releaseUpper r h => decide (2 ≤ r ∧ r ≤ vP n a ∧ h ≤ a - r + 1)
  | .tailUpper r h => decide (2 ≤ r ∧ r ≤ vP n a ∧ h ≤ a - r + 1)
  | .mean r => decide (2 ≤ r ∧ r ≤ vP n a)
  | .union r => decide (2 ≤ r ∧ r ≤ vP n a)
  | .edgeLower r => decide (2 ≤ r ∧ r ≤ vP n a)
  | .edgeUpper r => decide (2 ≤ r ∧ r ≤ vP n a ∧ 0 < D0P n a)
  | .assumption k' => decide (kind = .cond ∧ k' = k)

/-! ### The generic certificate check -/

/-- The target coefficient: `−B_{m,j}(k)` for `pos`, `B_{m,j}(k + 1)` otherwise. -/
def tgtZ (kind : Kind) (k j m : Nat) : Int :=
  match kind with
  | .pos => -BZ m j k
  | .neg => BZ m j (k + 1)
  | .cond => BZ m j (k + 1)

/-- The target constant: `−B_{a,0}(k)` for `pos`, `B_{a,0}(k + 1)` otherwise. -/
def tgt0Z (kind : Kind) (a k : Nat) : Int :=
  match kind with
  | .pos => -BZ a 0 k
  | .neg => BZ a 0 (k + 1)
  | .cond => BZ a 0 (k + 1)

/-- `Σ_{(ℓ, w)} w · a^ℓ_{j,m}`. -/
def rowSum (n a : Nat) (rows : List (CLabel × Nat)) (j m : Nat) : Int :=
  rows.foldl (fun acc p => acc + (p.2 : Int) * coefZ n a p.1 j m) 0

/-- `Σ_{(ℓ, w)} w · b^ℓ`. -/
def rhsSum (n a : Nat) (rows : List (CLabel × Nat)) : Int :=
  rows.foldl (fun acc p => acc + (p.2 : Int) * rhsZ n a p.1) 0

/-- The residual of the variable `(j, m)` before `η`: `W_j (σ · tgt_{j,m} − Σ w a_{j,m})`. -/
def preZ (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat)) (j m : Nat) : Int :=
  (binomN (vP n a) j : Int) * ((σ : Int) * tgtZ kind k j m - rowSum n a rows j m)

/-- The rows that may touch layer `j`. -/
def layerRows (rows : List (CLabel × Nat)) (j : Nat) : List (CLabel × Nat) :=
  rows.filter fun p => touches p.1 j

/-- `M_j = max(0, max_{0 ≤ m ≤ a − j} (preZ j m − e))`. -/
def layerMax (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat)) (e : Int)
    (j : Nat) : Int :=
  let rs := layerRows rows j
  (List.range (a + 1 - j)).foldl (fun acc m => max acc (preZ n a k kind σ rs j m - e)) 0

/-- The free constant `η`: the largest layer-1 residual before `η`. -/
def autoEta (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat)) : Int :=
  let rs := layerRows rows 1
  (List.range a).foldl (fun acc m => max acc (preZ n a k kind σ rs 1 m)) (preZ n a k kind σ rs 1 0)

/-- The bound of the certificate principle: `σ tgt_0 + Σ w b + η + Σ_{j=1}^{v} M_j`. -/
def boundWith (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat)) (η : Int) :
    Int :=
  (σ : Int) * tgt0Z kind a k + rhsSum n a rows + η +
    (List.range' 1 (vP n a)).foldl
      (fun acc j => acc + layerMax n a k kind σ rows (if j = 1 then η else 0) j) 0

/-- The sign required of the bound: `< 0` for `pos`, `≤ 0` otherwise. -/
def signOK (kind : Kind) (b : Int) : Bool :=
  match kind with
  | .pos => decide (b < 0)
  | .neg => decide (b ≤ 0)
  | .cond => decide (b ≤ 0)

/-- **The generic certificate check** for the triple `(n, a, k)`. -/
def genericOK (n a k : Nat) (kind : Kind) (σ : Nat) (rows : List (CLabel × Nat)) : Bool :=
  decide (1 ≤ vP n a) && decide (0 < σ) && rows.all (fun p => rowOKB n a k kind p.1) &&
    signOK kind (boundWith n a k kind σ rows (autoEta n a k kind σ rows))

/-! ### The author's normalization (39) (not needed for soundness) -/

/-- `N_Q = max(1, |tgt_0|, max |tgt_{j,m}| W_j)` (for `σ = 1`). -/
def scaleTarget (n a k : Nat) (kind : Kind) : Nat :=
  (List.range' 1 (vP n a)).foldl (fun acc j =>
      (List.range (a + 1 - j)).foldl
        (fun acc m => max acc ((tgtZ kind k j m).natAbs * binomN (vP n a) j)) acc)
    (max 1 (tgt0Z kind a k).natAbs)

/-- `N_ρ = max(1, |b^ρ|, max |a^ρ_{j,m}| W_j)`. -/
def scaleRow (n a : Nat) (ℓ : CLabel) : Nat :=
  (List.range' 1 (vP n a)).foldl (fun acc j =>
      if touches ℓ j then
        (List.range (a + 1 - j)).foldl
          (fun acc m => max acc ((coefZ n a ℓ j m).natAbs * binomN (vP n a) j)) acc
      else acc)
    (max 1 (rhsZ n a ℓ).natAbs)

/-- A stored linear certificate (`D`, rows with multipliers) as a generic one:
`L = lcm(N_Q, N_ρ, …)`, `σ = D·L/N_Q`, `w_ρ = mult_ρ·L/N_ρ`. -/
def linearToGeneric (n a k : Nat) (kind : Kind) (D : Nat) (rows : List (CLabel × Nat)) :
    Nat × List (CLabel × Nat) :=
  let NQ := scaleTarget n a k kind
  let Ns := rows.map fun p => scaleRow n a p.1
  let L := Ns.foldl Nat.lcm NQ
  (D * (L / NQ), (rows.zip Ns).map fun x => (x.1.1, x.1.2 * (L / x.2)))

/-! ### Stored certificates and the triple check -/

/-- A stored certificate: a separator `t = p/q`, or a linear certificate (kind, `D`, rows with
integer multipliers). -/
inductive CertData where
  | sep (p q : Nat)
  | lin (kind : Kind) (D : Nat) (rows : List (CLabel × Nat))
  deriving Repr, Inhabited

/-- The check of a stored certificate. -/
def storedOK (n a k : Nat) : CertData → Bool
  | .sep p q => genericOK n a k .cond q [(.assumption k, p)]
  | .lin kind D rows =>
      let g := linearToGeneric n a k kind D rows
      genericOK n a k kind g.1 g.2

/-- The direct criteria (36)–(37) as generic certificates: path row `path(k)` against the
matching bound, the lower layer rule, the upper layer rule. -/
def directOK (n a k : Nat) : Bool :=
  genericOK n a k .pos 1 [(.path k, 1)] || genericOK n a k .pos 1 [] || genericOK n a k .neg 1 []

/-- The check of one triple: its stored certificate if there is one, else the direct criteria. -/
def tripleOK (n a k : Nat) : Option CertData → Bool
  | some c => storedOK n a k c
  | none => directOK n a k

/-! ### Parsing the stored data -/

/-- The decimal numbers of a string (maximal runs of digits). -/
def tokens (s : String) : List Nat :=
  let r := s.foldl (fun (p : List Nat × Nat × Bool) c =>
    if c.isDigit then (p.1, p.2.1 * 10 + (c.toNat - 48), true)
    else if p.2.2 then (p.2.1 :: p.1, 0, false) else p) ([], 0, false)
  (if r.2.2 then r.2.1 :: r.1 else r.1).reverse

/-- The kind code: `1` positive, `2` negative, `3` conditional. -/
def kindOf? : Nat → Option Kind
  | 1 => some .pos
  | 2 => some .neg
  | 3 => some .cond
  | _ => none

/-- Parse `c` rows `tag params… mult` (tags `0`–`11` in the order of `CLabel`). -/
def parseRows : Nat → List Nat → List (CLabel × Nat) → Option (List (CLabel × Nat) × List Nat)
  | 0, ts, acc => some (acc.reverse, ts)
  | c + 1, 0 :: r :: w :: ts, acc => parseRows c ts ((.count r, w) :: acc)
  | c + 1, 1 :: r :: w :: ts, acc => parseRows c ts ((.path r, w) :: acc)
  | c + 1, 2 :: r :: h :: w :: ts, acc => parseRows c ts ((.priv r h, w) :: acc)
  | c + 1, 3 :: r :: l :: w :: ts, acc => parseRows c ts ((.hall r l, w) :: acc)
  | c + 1, 4 :: r :: h :: w :: ts, acc => parseRows c ts ((.tail r h, w) :: acc)
  | c + 1, 5 :: r :: h :: w :: ts, acc => parseRows c ts ((.releaseUpper r h, w) :: acc)
  | c + 1, 6 :: r :: h :: w :: ts, acc => parseRows c ts ((.tailUpper r h, w) :: acc)
  | c + 1, 7 :: r :: w :: ts, acc => parseRows c ts ((.mean r, w) :: acc)
  | c + 1, 8 :: r :: w :: ts, acc => parseRows c ts ((.union r, w) :: acc)
  | c + 1, 9 :: r :: w :: ts, acc => parseRows c ts ((.edgeLower r, w) :: acc)
  | c + 1, 10 :: r :: w :: ts, acc => parseRows c ts ((.edgeUpper r, w) :: acc)
  | c + 1, 11 :: r :: w :: ts, acc => parseRows c ts ((.assumption r, w) :: acc)
  | _ + 1, _, _ => none

/-- Parse the entries `a k 0 p q` (separator) and `a k c D len rows…` (linear certificate). -/
def parseEntries : Nat → List Nat → List (Nat × Nat × CertData) →
    Option (List (Nat × Nat × CertData))
  | _, [], acc => some acc.reverse
  | 0, _ :: _, _ => none
  | f + 1, a :: k :: 0 :: p :: q :: ts, acc => parseEntries f ts ((a, k, .sep p q) :: acc)
  | f + 1, a :: k :: c :: D :: len :: ts, acc =>
      match kindOf? c, parseRows len ts [] with
      | some kind, some (rows, ts') => parseEntries f ts' ((a, k, .lin kind D rows) :: acc)
      | _, _ => none
  | _ + 1, _ :: _, _ => none

/-- The stored certificate of `(a, k)`, if any. -/
def lookup (a k : Nat) : List (Nat × Nat × CertData) → Option CertData
  | [] => none
  | e :: es => if e.1 = a ∧ e.2.1 = k then some e.2.2 else lookup a k es

/-- **The check of the order `n`** against the data string `s`: every `(a, k)` with
`⌈n/2⌉ ≤ a ≤ n − 1`, `1 ≤ k < ⌊(2a+1)/3⌋` passes `tripleOK` (the domain (35) at `n`). -/
def checkN (n : Nat) (s : String) : Bool :=
  let ts := tokens s
  match parseEntries ts.length ts [] with
  | none => false
  | some es =>
    (List.range' ((n + 1) / 2) (n - (n + 1) / 2)).all fun a =>
      (List.range' 1 ((2 * a + 1) / 3 - 1)).all fun k => tripleOK n a k (lookup a k es)

end ZhangCertX

end Erdos993Lean
