import Mathlib

/-!
# Zhang's finite part, 4: the relaxation, its row families, and the certificate principle

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Sections 2.1–2.9 (LaTeX `paper/finite60.tex`).  This file is the
**statement layer** of the certificate method: pure definitions over `ℚ`, indexed by the
parameters `(n, a)` alone (no graph), plus the certificate principle (40), proved.

* `binom b r`: the paper's binomial (`0` unless `0 ≤ r ≤ b`, integers `b, r`).
* Parameters: `v = n − a`, `δ = a − v`, `E = max(0, δ − 1)` (11), `D0 = min(E, v − 1)` (12),
  `W j = C(v, j)` (4).
* `vars n a`: the index set of the variables `t_{j,m}`, `1 ≤ j ≤ v`, `0 ≤ m ≤ a − j`.
* `Row`, `Row.Holds`: a linear row `Σ_{j,m} a_{j,m} t_{j,m} ≤ b` over `vars n a`.
* The auxiliary functions `bStep` (`b_{r,h}(m)`, (14)), `sExt` (`s_r`, (16)), `U` (`U_{r,h}(m)`,
  (17)), `Vt` (`V_{r,h}(m)`, (18)), `β`, `C0` ((22)), `Gr` (`G_r`, (27)), `B` (`B_{m,j}(k)`, (30)),
  `hallC` (the factor `c` of `hall(r, l)`).
* `Label`: the eleven row families of Section 2.9 (`count`, `path`, `private` (here `priv`),
  `hall`, `tail`, `release_upper`, `tail_upper`, `mean`, `union`, `edge_lower`, `edge_upper`);
  `Label.InDomain` their parameter domains; `Label.row` their coefficients and right sides,
  transcribed from Section 2.9; `assumptionRow` the row `assumption(k)`.
* `Basic` (the constraints (5)) and `Feasible` (the relaxation: (5) and every row on its domain).
* `delta n a t k` = `B_{a,0}(k) + Σ B_{m,j}(k) t_{j,m}`, the right side of (31).
* `InP60`, `P60` (the domain (35); `#eval P60.card` gives the paper's 17,100), `NoRecovery n a k`
  (`Δ_k ≤ 0 → Δ_{k+1} ≤ 0` for every feasible array; each alternative of (34) implies it),
  `CertificatesSound` (the certificate layer's claim on all of `P60`).
* `certificate_principle`: **(40)** in general form (variables grouped in layers of mass at most
  one, one layer of mass exactly one, valid rows with nonnegative weights, a free weight `η`).
* `certificate_bound`: **(40) for the relaxation**, with the normalization `x_{j,m} = t_{j,m}/W_j`
  and arbitrary positive row scales `N_ρ` (the paper's `N_ρ` of (39) is one admissible choice).

Grade: definitions, and PROVED IN LEAN (complete proofs, standard axioms only) for the stated
lemmas.  The validity of the row families for forests (Lemmas 2.3–2.10 with the choice of
Lemma 2.5) and the certificate data are **not** in this file; see `Zhang/Finite60.lean`.
-/

namespace Erdos993Lean
namespace Zhang
namespace Cert

open Finset

/-! ### Binomial coefficients with the paper's convention -/

/-- The paper's binomial coefficient: `C(b, r) = 0` unless `b, r` are integers with
`0 ≤ r ≤ b`. -/
def binom (b r : ℤ) : ℚ :=
  if 0 ≤ r ∧ r ≤ b then ((b.toNat.choose r.toNat : ℕ) : ℚ) else 0

theorem binom_natCast (b r : ℕ) : binom b r = (b.choose r : ℚ) := by
  unfold binom
  split_ifs with h
  · simp
  · push_neg at h
    have hbr : b < r := by exact_mod_cast h (Int.natCast_nonneg r)
    rw [Nat.choose_eq_zero_of_lt hbr, Nat.cast_zero]

theorem binom_sub_natCast (m r j : ℕ) :
    binom m ((r : ℤ) - j) = if j ≤ r then (m.choose (r - j) : ℚ) else 0 := by
  split_ifs with h
  · rw [show (r : ℤ) - j = ((r - j : ℕ) : ℤ) by omega, binom_natCast]
  · unfold binom
    rw [if_neg (by omega)]

theorem binom_nonneg (b r : ℤ) : 0 ≤ binom b r := by
  unfold binom
  split_ifs <;> positivity

/-! ### Parameters and variables -/

/-- `v = n − a` (the matching number of the forest, by König). -/
def v (n a : ℕ) : ℕ := n - a

/-- `δ = a − v`. -/
def δ (n a : ℕ) : ℕ := a - v n a

/-- `E = max(0, δ − 1)` (11). -/
def E (n a : ℕ) : ℕ := δ n a - 1

/-- `D_0 = min(E, v − 1)` (12). -/
def D0 (n a : ℕ) : ℕ := min (E n a) (v n a - 1)

/-- `W_j = C(v, j)` (4). -/
def W (n a j : ℕ) : ℚ := binom (v n a) j

/-- The index set of the variables `t_{j,m}`: `1 ≤ j ≤ v` and `0 ≤ m ≤ a − j`. -/
def vars (n a : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 (v n a) ×ˢ range (a + 1)).filter (fun p => p.1 + p.2 ≤ a)

theorem mem_vars {n a : ℕ} {p : ℕ × ℕ} :
    p ∈ vars n a ↔ p.1 ∈ Icc 1 (v n a) ∧ p.2 ∈ range (a + 1 - p.1) := by
  unfold vars
  simp only [mem_filter, mem_product, mem_Icc, mem_range]
  omega

/-- Summing over one layer of `vars`. -/
theorem sum_vars_layer {n a j : ℕ} (hj : j ∈ Icc 1 (v n a)) (f : ℕ → ℕ → ℚ) :
    ∑ p ∈ (vars n a).filter (fun p => p.1 = j), f p.1 p.2 = ∑ m ∈ range (a + 1 - j), f j m := by
  symm
  refine Finset.sum_nbij' (fun m => (j, m)) (fun p => p.2) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_filter, mem_vars]
    exact ⟨⟨hj, hm⟩, rfl⟩
  · intro p hp
    rw [mem_filter, mem_vars] at hp
    rw [← hp.2]
    exact hp.1.2
  · intro m _
    rfl
  · intro p hp
    rw [mem_filter] at hp
    rw [← hp.2]
  · intro m _
    rfl

/-- `Σ_{p ∈ vars} f p = Σ_{j=1}^{v} Σ_{m=0}^{a−j} f (j, m)`. -/
theorem sum_vars (n a : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ p ∈ vars n a, f p.1 p.2 = ∑ j ∈ Icc 1 (v n a), ∑ m ∈ range (a + 1 - j), f j m :=
  Finset.sum_finset_product' _ _ _ (fun _ => mem_vars)

theorem W_pos {n a j : ℕ} (hj : j ∈ Icc 1 (v n a)) : 0 < W n a j := by
  unfold W
  rw [binom_natCast]
  exact_mod_cast Nat.choose_pos (mem_Icc.mp hj).2

/-! ### Rows -/

/-- A linear row `Σ_{j,m} coef j m · t_{j,m} ≤ rhs`. -/
structure Row where
  coef : ℕ → ℕ → ℚ
  rhs : ℚ

/-- The row holds for the array `t` (the sum runs over the index set `vars n a`). -/
def Row.Holds (n a : ℕ) (ρ : Row) (t : ℕ → ℕ → ℚ) : Prop :=
  ∑ p ∈ vars n a, ρ.coef p.1 p.2 * t p.1 p.2 ≤ ρ.rhs

/-- `x_+ = max(x, 0)` for an integer `x`, as a rational. -/
def pos (x : ℤ) : ℚ := ((max x 0 : ℤ) : ℚ)

/-- `b_{r,h}(m)` (14). -/
def bStep (a r h m : ℕ) : ℚ :=
  if h ≤ m then r else if r * h ≤ a + (r - 1) * m then 1 else 0

/-- `s_r = max(0, v − r + 1 − E)` (16). -/
def sExt (n a r : ℕ) : ℚ := pos ((v n a : ℤ) - r + 1 - E n a)

/-- `U_{r,h}(m)` (17): with `d = a − m`, `L = d − r + 1` and `d = qL + ρ`, `0 ≤ ρ < L`,
`U = q (m + L − h)_+ + [(m + ρ − h)_+ + (r − q − 1)(m − h)_+ if q < r, 0 if q = r]`. -/
def U (a r h m : ℕ) : ℚ :=
  let d : ℕ := a - m
  let L : ℕ := d + 1 - r
  let q : ℕ := d / L
  let ρ : ℕ := d % L
  (q : ℚ) * pos ((m : ℤ) + L - h) +
    (if q < r then pos ((m : ℤ) + ρ - h) + ((r - q - 1 : ℕ) : ℚ) * pos ((m : ℤ) - h) else 0)

/-- `V_{r,h}(m)` (18): `r` if `h ≤ m`; `min(r, ⌊d/(h − m)⌋)` if `m < h ≤ m + L`; `0` if
`h > m + L` (with `d = a − m`, `L = d − r + 1`). -/
def Vt (a r h m : ℕ) : ℚ :=
  let d : ℕ := a - m
  let L : ℕ := d + 1 - r
  if h ≤ m then (r : ℚ) else if h ≤ m + L then ((min r (d / (h - m)) : ℕ) : ℚ) else 0

/-- `β_r = C(v−2, r−1) − (a−2) C(v−2, r−2)` (22). -/
def β (n a r : ℕ) : ℚ :=
  binom ((v n a : ℤ) - 2) ((r : ℤ) - 1) - ((a : ℚ) - 2) * binom ((v n a : ℤ) - 2) ((r : ℤ) - 2)

/-- `C_r^0 = a C(v−2, r) + (δ + 1) C(v−2, r−1)` (22). -/
def C0 (n a r : ℕ) : ℚ :=
  (a : ℚ) * binom ((v n a : ℤ) - 2) r + ((δ n a : ℚ) + 1) * binom ((v n a : ℤ) - 2) ((r : ℤ) - 1)

/-- `G_r = C(v−1, r−1) − C(v − D_0 − 1, r−1)` (27). -/
def Gr (n a r : ℕ) : ℚ :=
  binom ((v n a : ℤ) - 1) ((r : ℤ) - 1) - binom ((v n a : ℤ) - D0 n a - 1) ((r : ℤ) - 1)

/-- `B_{m,j}(k) = C(m, k − j) − C(m, k − j − 1)` (30). -/
def B (m j k : ℕ) : ℚ := binom m ((k : ℤ) - j) - binom m ((k : ℤ) - j - 1)

/-- The factor `c = v − r − max(0, l − δ)` of the row `hall(r, l)`. -/
def hallC (n a r l : ℕ) : ℤ := (v n a : ℤ) - r - max 0 ((l : ℤ) - δ n a)

/-- The eleven row families of Section 2.9 (`priv` is the paper's `private`). -/
inductive Label where
  | count (r : ℕ)
  | path (r : ℕ)
  | priv (r h : ℕ)
  | hall (r l : ℕ)
  | tail (r h : ℕ)
  | releaseUpper (r h : ℕ)
  | tailUpper (r h : ℕ)
  | mean (r : ℕ)
  | union (r : ℕ)
  | edgeLower (r : ℕ)
  | edgeUpper (r : ℕ)
  deriving DecidableEq, Repr

/-- The parameter domain of each row family (Section 2.9). -/
def Label.InDomain (n a : ℕ) : Label → Prop
  | .count r => 2 ≤ r ∧ r ≤ v n a
  | .path r => 2 ≤ r ∧ r ≤ a
  | .priv r h => 2 ≤ r ∧ r ≤ v n a ∧ h < a
  | .hall r l => l ≤ a ∧ r < min (v n a) (a - l) ∧ 0 ≤ hallC n a r l ∧ (l = 0 → 1 ≤ r)
  | .tail r h => 2 ≤ r ∧ r ≤ v n a ∧ h ≤ a - r + 1
  | .releaseUpper r h => 2 ≤ r ∧ r ≤ v n a ∧ h ≤ a - r + 1
  | .tailUpper r h => 2 ≤ r ∧ r ≤ v n a ∧ h ≤ a - r + 1
  | .mean r => 2 ≤ r ∧ r ≤ v n a
  | .union r => 2 ≤ r ∧ r ≤ v n a
  | .edgeLower r => 2 ≤ r ∧ r ≤ v n a
  | .edgeUpper r => 2 ≤ r ∧ r ≤ v n a ∧ 0 < D0 n a

instance (n a : ℕ) (ρ : Label) : Decidable (ρ.InDomain n a) := by
  cases ρ <;> unfold Label.InDomain <;> infer_instance

/-- The coefficients `a^ρ_{j,m}` and the right side `b^ρ` of each row family (Section 2.9). -/
def Label.row (n a : ℕ) : Label → Row
  | .count r => ⟨fun j _ => if j = r then 1 else 0, binom (v n a) r⟩
  | .path r => ⟨fun j m => -binom m ((r : ℤ) - j), binom a r - binom ((n : ℤ) - r + 1) r⟩
  | .priv r h => ⟨fun j m =>
      (if j = r then pos (((r : ℤ) - 1) * m + a - r + 1 - r * h) else 0) -
        (if j = r - 1 then ((v n a : ℚ) - r + 1) * pos ((m : ℤ) - h) else 0), 0⟩
  | .hall r l => ⟨fun j m =>
      ((if j = r + 1 then (r : ℚ) + 1 else 0) - (if j = r then (hallC n a r l : ℚ) else 0)) *
        binom m l,
      if r = 0 then (hallC n a r l : ℚ) * binom a l else 0⟩
  | .tail r h => ⟨fun j m =>
      (if j = r then bStep a r h m else 0) -
        (if j = r - 1 ∧ h ≤ m then (v n a : ℚ) - r + 1 else 0), 0⟩
  | .releaseUpper r h => ⟨fun j m =>
      (if j = r - 1 then sExt n a r * pos ((m : ℤ) - h) else 0) -
        (if j = r then U a r h m else 0), 0⟩
  | .tailUpper r h => ⟨fun j m =>
      (if j = r - 1 ∧ h ≤ m then sExt n a r else 0) - (if j = r then Vt a r h m else 0), 0⟩
  | .mean r => ⟨fun j m => -(if j = r then (m : ℚ) else 0) - (if j = 2 then β n a r else 0),
      -C0 n a r - β n a r * binom (v n a) 2⟩
  | .union r => ⟨fun j m => ((a : ℚ) - m) *
      ((if j = r then 1 else 0) - (if j = 1 then binom ((v n a : ℤ) - 1) ((r : ℤ) - 1) else 0)),
      0⟩
  | .edgeLower r => ⟨fun j _ =>
      -(if j = r then 1 else 0) + (if j = 2 then binom ((v n a : ℤ) - 2) ((r : ℤ) - 2) else 0),
      -binom (v n a) r + binom ((v n a : ℤ) - 2) ((r : ℤ) - 2) * binom (v n a) 2⟩
  | .edgeUpper r => ⟨fun j _ =>
      (if j = r then (D0 n a : ℚ) else 0) - (if j = 2 then Gr n a r else 0),
      (D0 n a : ℚ) * binom (v n a) r - Gr n a r * binom (v n a) 2⟩

/-- The row `assumption(k)` of a conditional certificate: `Σ B_{m,j}(k) t_{j,m} ≤ −B_{a,0}(k)`,
i.e. `Δ_k ≤ 0`. -/
def assumptionRow (a k : ℕ) : Row := ⟨fun j m => B m j k, -B a 0 k⟩

/-! ### The relaxation -/

/-- The layer mass `T_j = Σ_{m=0}^{a−j} t_{j,m}` (4). -/
def layerSum (a : ℕ) (t : ℕ → ℕ → ℚ) (j : ℕ) : ℚ := ∑ m ∈ range (a + 1 - j), t j m

/-- The basic constraints (5) on the index set: `t ≥ 0`, `T_1 = v`, `T_j ≤ W_j` (`2 ≤ j ≤ v`). -/
structure Basic (n a : ℕ) (t : ℕ → ℕ → ℚ) : Prop where
  nonneg : ∀ p ∈ vars n a, 0 ≤ t p.1 p.2
  layer_one : layerSum a t 1 = v n a
  layer_le : ∀ j ∈ Icc 2 (v n a), layerSum a t j ≤ W n a j

/-- The relaxation of Section 2.9: the basic constraints and every row family on its domain. -/
structure Feasible (n a : ℕ) (t : ℕ → ℕ → ℚ) : Prop extends Basic n a t where
  rows : ∀ ρ : Label, ρ.InDomain n a → (ρ.row n a).Holds n a t

/-- `Δ_k` as an affine function of the array: `B_{a,0}(k) + Σ_{j,m} B_{m,j}(k) t_{j,m}` (31). -/
def delta (n a : ℕ) (t : ℕ → ℕ → ℚ) (k : ℕ) : ℚ :=
  B a 0 k + ∑ p ∈ vars n a, B p.2 p.1 k * t p.1 p.2

theorem assumptionRow_holds {n a k : ℕ} {t : ℕ → ℕ → ℚ} (h : delta n a t k ≤ 0) :
    (assumptionRow a k).Holds n a t := by
  unfold Row.Holds assumptionRow
  unfold delta at h
  simp only
  linarith

/-- The parameter domain `P60` (35): `2 ≤ n ≤ 60`, `⌈n/2⌉ ≤ a ≤ n − 1`, `1 ≤ k < ⌊(2a+1)/3⌋`. -/
def InP60 (n a k : ℕ) : Prop :=
  2 ≤ n ∧ n ≤ 60 ∧ n ≤ 2 * a ∧ a ≤ n - 1 ∧ 1 ≤ k ∧ k < (2 * a + 1) / 3

instance (n a k : ℕ) : Decidable (InP60 n a k) := by
  unfold InP60
  infer_instance

/-- `P60` as a finite set of triples `(n, a, k)`. -/
def P60 : Finset (ℕ × ℕ × ℕ) :=
  (Icc 2 60 ×ˢ (range 61 ×ˢ range 61)).filter (fun p => InP60 p.1 p.2.1 p.2.2)

theorem mem_P60 {n a k : ℕ} : (n, a, k) ∈ P60 ↔ InP60 n a k := by
  unfold P60 InP60
  simp only [mem_filter, mem_product, mem_Icc, mem_range]
  omega

/-- No feasible array recovers after a nonpositive difference at `k`.  Each alternative of (34)
(`Δ_k > 0`, `Δ_{k+1} ≤ 0`, `Δ_k ≤ 0 ⇒ Δ_{k+1} ≤ 0`), established for all feasible arrays, implies
this. -/
def NoRecovery (n a k : ℕ) : Prop :=
  ∀ t, Feasible n a t → delta n a t k ≤ 0 → delta n a t (k + 1) ≤ 0

/-- The certificate layer's claim (Table 1): no recovery on every triple of `P60`. -/
def CertificatesSound : Prop :=
  ∀ n a k, InP60 n a k → NoRecovery n a k

/-! ### The certificate principle (40) -/

/-- **The certificate principle (Zhang (40)), general form.**  Variables `x_i ≥ 0` (`i ∈ vars`)
are grouped in layers (`layer i ∈ layers`) of mass at most one, the layer `first` of mass exactly
one; rows `Σ_i A_ρ(i) x_i ≤ b_ρ` hold; `λ_ρ ≥ 0`, `η` arbitrary.  If every residual
`R_i = q_i − Σ_ρ λ_ρ A_ρ(i) − η [layer i = first]` is at most `M (layer i)`, with `M ≥ 0` on the
layers, then `q_0 + Σ_i q_i x_i ≤ q_0 + Σ_ρ λ_ρ b_ρ + η + Σ_L M_L`.  (The paper takes
`M_L = max(0, max_m R_{L,m})`.) -/
theorem certificate_principle {ι κ ρ : Type*} [DecidableEq κ]
    (vars : Finset ι) (layer : ι → κ) (layers : Finset κ)
    (hlayer : ∀ i ∈ vars, layer i ∈ layers) (first : κ) (x : ι → ℚ)
    (hx : ∀ i ∈ vars, 0 ≤ x i)
    (hmass : ∀ L ∈ layers, ∑ i ∈ vars with layer i = L, x i ≤ 1)
    (hfirst : ∑ i ∈ vars with layer i = first, x i = 1)
    (rows : Finset ρ) (A : ρ → ι → ℚ) (b : ρ → ℚ)
    (hrows : ∀ p ∈ rows, ∑ i ∈ vars, A p i * x i ≤ b p)
    (lam : ρ → ℚ) (hlam : ∀ p ∈ rows, 0 ≤ lam p) (η q0 : ℚ) (q : ι → ℚ) (M : κ → ℚ)
    (hM0 : ∀ L ∈ layers, 0 ≤ M L)
    (hR : ∀ i ∈ vars,
      q i - ∑ p ∈ rows, lam p * A p i - (if layer i = first then η else 0) ≤ M (layer i)) :
    q0 + ∑ i ∈ vars, q i * x i ≤
      q0 + ∑ p ∈ rows, lam p * b p + η + ∑ L ∈ layers, M L := by
  set S : ι → ℚ := fun i => ∑ p ∈ rows, lam p * A p i with hS
  set e : ι → ℚ := fun i => if layer i = first then η else 0 with he
  set R : ι → ℚ := fun i => q i - S i - e i with hRdef
  -- split `q_i x_i = R_i x_i + S_i x_i + e_i x_i`
  have hsplit : ∑ i ∈ vars, q i * x i =
      ∑ i ∈ vars, R i * x i + ∑ i ∈ vars, S i * x i + ∑ i ∈ vars, e i * x i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hRdef]
    ring
  -- the row part
  have hSx : ∑ i ∈ vars, S i * x i = ∑ p ∈ rows, lam p * ∑ i ∈ vars, A p i * x i := by
    simp only [hS, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hSle : ∑ p ∈ rows, lam p * ∑ i ∈ vars, A p i * x i ≤ ∑ p ∈ rows, lam p * b p :=
    Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hrows p hp) (hlam p hp))
  -- the first-layer part
  have hex : ∑ i ∈ vars, e i * x i = η * ∑ i ∈ vars with layer i = first, x i := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he]
    split_ifs <;> ring
  -- the residual part
  have hRle : ∑ i ∈ vars, R i * x i ≤ ∑ L ∈ layers, M L := by
    calc ∑ i ∈ vars, R i * x i ≤ ∑ i ∈ vars, M (layer i) * x i :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hR i hi) (hx i hi))
      _ = ∑ L ∈ layers, ∑ i ∈ vars with layer i = L, M (layer i) * x i :=
          (Finset.sum_fiberwise_of_maps_to hlayer _).symm
      _ = ∑ L ∈ layers, M L * ∑ i ∈ vars with layer i = L, x i := by
          apply Finset.sum_congr rfl
          intro L _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
      _ ≤ ∑ L ∈ layers, M L * 1 :=
          Finset.sum_le_sum (fun L hL => mul_le_mul_of_nonneg_left (hmass L hL) (hM0 L hL))
      _ = ∑ L ∈ layers, M L := by simp
  rw [hsplit, hSx, hex, hfirst]
  linarith

/-- **The certificate principle (40) for the relaxation.**  For an array satisfying the basic
constraints (5) (with `v ≥ 1`), rows `row r` (`r ∈ rows`) that hold, positive scales `N r` and
weights `λ r ≥ 0`, the normalized variables `x_{j,m} = t_{j,m}/W_j` (layer masses `T_j/W_j ≤ 1`,
`T_1/W_1 = 1`) give: if every residual
`W_j q_{j,m} − Σ_r λ_r W_j a^r_{j,m}/N_r − η [j = 1]` is at most `M_j`, `M ≥ 0`, then
`q_0 + Σ q_{j,m} t_{j,m} ≤ q_0 + Σ_r λ_r b^r/N_r + η + Σ_{j=1}^{v} M_j`. -/
theorem certificate_bound {n a : ℕ} {t : ℕ → ℕ → ℚ} (ht : Basic n a t) (hv : 1 ≤ v n a)
    {ρ : Type*} (rows : Finset ρ) (row : ρ → Row) (hrows : ∀ r ∈ rows, (row r).Holds n a t)
    (N lam : ρ → ℚ) (hN : ∀ r ∈ rows, 0 < N r) (hlam : ∀ r ∈ rows, 0 ≤ lam r)
    (η q0 : ℚ) (q : ℕ → ℕ → ℚ) (M : ℕ → ℚ) (hM0 : ∀ j ∈ Icc 1 (v n a), 0 ≤ M j)
    (hR : ∀ p ∈ vars n a, W n a p.1 * q p.1 p.2 -
        ∑ r ∈ rows, lam r * (W n a p.1 * (row r).coef p.1 p.2 / N r) -
        (if p.1 = 1 then η else 0) ≤ M p.1) :
    q0 + ∑ p ∈ vars n a, q p.1 p.2 * t p.1 p.2 ≤
      q0 + ∑ r ∈ rows, lam r * ((row r).rhs / N r) + η + ∑ j ∈ Icc 1 (v n a), M j := by
  have hlayer : ∀ p ∈ vars n a, p.1 ∈ Icc 1 (v n a) := fun p hp => (mem_vars.mp hp).1
  have hx : ∀ p ∈ vars n a, 0 ≤ t p.1 p.2 / W n a p.1 := fun p hp =>
    div_nonneg (ht.nonneg p hp) (W_pos (hlayer p hp)).le
  have hmass_eq : ∀ j ∈ Icc 1 (v n a), ∑ p ∈ vars n a with p.1 = j, t p.1 p.2 / W n a p.1 =
      layerSum a t j / W n a j := by
    intro j hj
    rw [sum_vars_layer hj (fun j m => t j m / W n a j), layerSum, Finset.sum_div]
  have hW1 : W n a 1 = v n a := by
    unfold W
    rw [binom_natCast, Nat.choose_one_right]
  have hmass : ∀ j ∈ Icc 1 (v n a), ∑ p ∈ vars n a with p.1 = j, t p.1 p.2 / W n a p.1 ≤ 1 := by
    intro j hj
    rw [hmass_eq j hj]
    have hW := W_pos hj
    rw [div_le_one hW]
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1 : j = 1 := by
        rw [mem_Icc] at hj
        omega
      subst hj1
      rw [ht.layer_one, hW1]
    · exact ht.layer_le j (mem_Icc.mpr ⟨hj2, (mem_Icc.mp hj).2⟩)
  have h1 : (1 : ℕ) ∈ Icc 1 (v n a) := mem_Icc.mpr ⟨le_rfl, hv⟩
  have hfirst : ∑ p ∈ vars n a with p.1 = 1, t p.1 p.2 / W n a p.1 = 1 := by
    rw [hmass_eq 1 h1, ht.layer_one, hW1]
    have : (0 : ℚ) < v n a := by exact_mod_cast hv
    field_simp
  have hrows' : ∀ r ∈ rows, ∑ p ∈ vars n a, W n a p.1 * (row r).coef p.1 p.2 / N r *
      (t p.1 p.2 / W n a p.1) ≤ (row r).rhs / N r := by
    intro r hr
    have hNr := hN r hr
    have heq : ∑ p ∈ vars n a, W n a p.1 * (row r).coef p.1 p.2 / N r * (t p.1 p.2 / W n a p.1) =
        (∑ p ∈ vars n a, (row r).coef p.1 p.2 * t p.1 p.2) / N r := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      have hWp := (W_pos (hlayer p hp)).ne'
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (hrows r hr) hNr.le
  have key := certificate_principle (vars n a) (fun p => p.1) (Icc 1 (v n a)) hlayer 1
    (fun p => t p.1 p.2 / W n a p.1) hx hmass hfirst rows
    (fun r p => W n a p.1 * (row r).coef p.1 p.2 / N r) (fun r => (row r).rhs / N r) hrows'
    lam hlam η q0 (fun p => W n a p.1 * q p.1 p.2) M hM0 hR
  have hlhs : ∑ p ∈ vars n a, W n a p.1 * q p.1 p.2 * (t p.1 p.2 / W n a p.1) =
      ∑ p ∈ vars n a, q p.1 p.2 * t p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hWp := (W_pos (hlayer p hp)).ne'
    field_simp
  simp only at key
  rw [hlhs] at key
  exact key

end Cert
end Zhang
end Erdos993Lean
