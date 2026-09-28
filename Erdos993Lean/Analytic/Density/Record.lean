import Erdos993Lean.Analytic.Density.Paths

/-!
# Density records: the constants and their finite conditions

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Source: Soul's
`SOUL/RESULTS/O5.md` §2 (the record conditions) and `SOUL/O6_O5/density_certified.json` (the
constants), recomputed independently (lane notes `LEAN/lanes/A8/NOTES.md`).

A `Record` fixes an activity `x`, a density `r` and the boundaries `s0` (every nonempty tree),
`g` (every tree with at least three vertices), `B0` (every nonpath tree) and `h` (every forest with
at least eight vertices), plus the rational parameters `s_H, s_L, K, N₀` of the path tail
(`path_tail`).  `Record.Valid` collects the finite rational conditions, all decidable:

* the path conditions (`r ≤ ρ`, the exact values of `μ_j − r j` for `j + 2 < N₀`, the tail
  parameters); `Valid.pathBound` gives `S(P_j) ≥ (r j + c_j) Z(P_j)` for every `j ≥ 1`, with
  `c_j = s0, g, h` for `j ≤ 2`, `3 ≤ j ≤ 7`, `j ≥ 8` (`pathConst`);
* the orderings `s0 ≤ g ≤ h ≤ B0`, `h ≤ 2 s0`, `B0 + r ≤ 4 s0`;
* the five branch types `t = 0, …, 4` (one vertex; two vertices; three vertices with the base at an
  end; three vertices with the base in the middle; at least four vertices) with their lower
  boundaries `A t ≤ μ(C) − r|C|`, `B t ≤ μ(C − w) − r(|C| − 1)` and ratio bounds
  `lo t ≤ Z(C − w)/Z(C) ≤ hi t` (exact for `t ≤ 3`);
* `deg3`, `deg4`: the root-degree-3 and -4 tests `a + b ζ ≥ 0` at both ends `ζ = x Π lo`,
  `ζ = x Π hi` (`a = Σ A − r − B0`, `b = 1 − (d + 1) r + Σ B − B0`), over all `5³ + 5⁴` type
  tuples (Soul checks the 35 + 70 multisets; the tuples are their orderings);
* `big`: the branch-removal gains `A t ≥ 0`, `A t + x hi_t (B t − r) ≥ 0` (root degree `≥ 5`).

`check_step` turns `deg3`/`deg4` into the inequality consumed by the root identity.
-/

namespace Erdos993Lean.Analytic.Density

open Finset

/-- A density record (Soul's O5 §2 constants) with the parameters of the path tail. -/
structure Record where
  /-- the activity -/
  x : ℚ
  /-- the density -/
  r : ℚ
  /-- boundary of every nonempty tree -/
  s0 : ℚ
  /-- boundary of every tree with at least three vertices -/
  g : ℚ
  /-- boundary of every nonpath tree -/
  B0 : ℚ
  /-- boundary of every forest with at least eight vertices -/
  h : ℚ
  /-- rational upper bound of `√(1 + 4x)` -/
  sH : ℚ
  /-- rational lower bound of `√(1 + 4x)` -/
  sL : ℚ
  /-- the tail constant -/
  K : ℚ
  /-- the tail start (`j + 2 ≥ N₀`) -/
  N0 : ℕ

namespace Record

variable (R : Record)

/-- `μ_j = S(P_j)/Z(P_j)`, the mean of the path `P_j`. -/
def mu (j : ℕ) : ℚ := sP R.x j / zP R.x j

/-- The boundary `c_j` of the path `P_j`. -/
def pathConst (j : ℕ) : ℚ := if j ≤ 2 then R.s0 else if j ≤ 7 then R.g else R.h

/-- Lower boundary of `μ(C) − r|C|` for a branch of type `t`. -/
def A : Fin 5 → ℚ :=
  ![R.mu 1 - R.r, R.mu 2 - 2 * R.r, R.mu 3 - 3 * R.r, R.mu 3 - 3 * R.r, R.g]

/-- Lower boundary of `μ(C − w) − r(|C| − 1)` for a branch of type `t`. -/
def B : Fin 5 → ℚ :=
  ![R.mu 0 - 0 * R.r, R.mu 1 - R.r, R.mu 2 - 2 * R.r, 2 * R.mu 1 - 2 * R.r, R.g]

/-- Lower bound of the deletion ratio `Z(C − w)/Z(C)` for a branch of type `t`. -/
def lo : Fin 5 → ℚ :=
  ![zP R.x 0 / zP R.x 1, zP R.x 1 / zP R.x 2, zP R.x 2 / zP R.x 3, zP R.x 1 ^ 2 / zP R.x 3,
    1 / zP R.x 1]

/-- Upper bound of the deletion ratio `Z(C − w)/Z(C)` for a branch of type `t`. -/
def hi : Fin 5 → ℚ :=
  ![zP R.x 0 / zP R.x 1, zP R.x 1 / zP R.x 2, zP R.x 2 / zP R.x 3, zP R.x 1 ^ 2 / zP R.x 3, 1]

/-- The root-degree-3 test for the branch types `i, j, k`. -/
def check3 (i j k : Fin 5) : Prop :=
  0 ≤ (R.A i + R.A j + R.A k - R.r - R.B0) +
      (1 - 4 * R.r + R.B i + R.B j + R.B k - R.B0) * (R.x * (R.lo i * R.lo j * R.lo k)) ∧
  0 ≤ (R.A i + R.A j + R.A k - R.r - R.B0) +
      (1 - 4 * R.r + R.B i + R.B j + R.B k - R.B0) * (R.x * (R.hi i * R.hi j * R.hi k))

/-- The root-degree-4 test for the branch types `i, j, k, l`. -/
def check4 (i j k l : Fin 5) : Prop :=
  0 ≤ (R.A i + R.A j + R.A k + R.A l - R.r - R.B0) +
      (1 - 5 * R.r + R.B i + R.B j + R.B k + R.B l - R.B0) *
        (R.x * (R.lo i * R.lo j * R.lo k * R.lo l)) ∧
  0 ≤ (R.A i + R.A j + R.A k + R.A l - R.r - R.B0) +
      (1 - 5 * R.r + R.B i + R.B j + R.B k + R.B l - R.B0) *
        (R.x * (R.hi i * R.hi j * R.hi k * R.hi l))

instance (i j k : Fin 5) : Decidable (R.check3 i j k) := by unfold check3; infer_instance

instance (i j k l : Fin 5) : Decidable (R.check4 i j k l) := by unfold check4; infer_instance

/-- **The finite conditions of a density record** (all decidable; kernel `decide`). -/
structure Valid : Prop where
  x_pos : 0 < R.x
  x_le : R.x ≤ 2
  r_nonneg : 0 ≤ R.r
  two_r_lt : 2 * R.r < 1
  rho : 1 ≤ (1 - 2 * R.r) ^ 2 * (1 + 4 * R.x)
  s0_nonneg : 0 ≤ R.s0
  s0_le_g : R.s0 ≤ R.g
  g_le_h : R.g ≤ R.h
  h_le_B0 : R.h ≤ R.B0
  h_le_two_s0 : R.h ≤ 2 * R.s0
  B0_add_r_le : R.B0 + R.r ≤ 4 * R.s0
  sH_nonneg : 0 ≤ R.sH
  sH_sq : 1 + 4 * R.x ≤ R.sH ^ 2
  sL_nonneg : 0 ≤ R.sL
  sL_sq : R.sL ^ 2 ≤ 1 + 4 * R.x
  K_nonneg : 0 ≤ R.K
  K_c : 1 ≤ R.K * ((1 + 2 * R.x - R.sH) / (1 + 4 * R.x) - R.h) * R.sL
  N0_ge : 10 ≤ R.N0
  N0_pow : R.K * R.N0 + 1 ≤ 2 ^ R.N0
  path_small : ∀ j < R.N0, 1 ≤ j → j + 2 < R.N0 →
    (R.r * j + R.pathConst j) * zP R.x j ≤ sP R.x j
  lo_nonneg : ∀ t : Fin 5, 0 ≤ R.lo t
  big : ∀ t : Fin 5, 0 ≤ R.A t ∧ 0 ≤ R.A t + R.x * R.hi t * (R.B t - R.r)
  deg3 : ∀ i j k : Fin 5, R.check3 i j k
  deg4 : ∀ i j k l : Fin 5, R.check4 i j k l

variable {R}

/-- **The path bound**: `S(P_j) ≥ (r j + c_j) Z(P_j)` for every `j ≥ 1`. -/
theorem Valid.pathBound (hR : R.Valid) (j : ℕ) (hj : 1 ≤ j) :
    (R.r * j + R.pathConst j) * zP R.x j ≤ sP R.x j := by
  rcases Nat.lt_or_ge (j + 2) R.N0 with h | h
  · exact hR.path_small j (by omega) hj h
  · have hc : R.pathConst j = R.h := by
      have := hR.N0_ge
      unfold pathConst
      rw [if_neg (by omega), if_neg (by omega)]
    rw [hc]
    exact path_tail R.x R.r R.h R.sH R.sL R.K R.N0 hR.x_pos hR.x_le hR.two_r_lt
      hR.rho hR.sH_nonneg hR.sH_sq hR.sL_nonneg hR.sL_sq hR.K_nonneg hR.K_c
      (by have := hR.N0_ge; omega) hR.N0_pow j h

theorem Valid.s0_le_pathConst (hR : R.Valid) (j : ℕ) : R.s0 ≤ R.pathConst j := by
  have h1 := hR.s0_le_g
  have h2 := hR.g_le_h
  unfold pathConst
  split_ifs <;> linarith

theorem Valid.g_le_pathConst (hR : R.Valid) {j : ℕ} (hj : 3 ≤ j) : R.g ≤ R.pathConst j := by
  have h2 := hR.g_le_h
  unfold pathConst
  split_ifs <;> first | omega | linarith

theorem pathConst_eq_h (R : Record) {j : ℕ} (hj : 8 ≤ j) : R.pathConst j = R.h := by
  unfold pathConst
  rw [if_neg (by omega), if_neg (by omega)]

/-! ## The finite check at root degree 3 and 4 -/

/-- An affine function nonnegative at both ends of an interval is nonnegative inside. -/
theorem affine_nonneg {a b P P' l u : ℚ} (hP : 0 < P) (hl : l * P ≤ P') (hu : P' ≤ u * P)
    (h1 : 0 ≤ a + b * l) (h2 : 0 ≤ a + b * u) : 0 ≤ a * P + b * P' := by
  rcases le_total 0 b with hb | hb
  · have : b * (l * P) ≤ b * P' := mul_le_mul_of_nonneg_left hl hb
    nlinarith
  · have : b * (u * P) ≤ b * P' := mul_le_mul_of_nonpos_left hu hb
    nlinarith

theorem card_eq_four {V : Type*} [DecidableEq V] {s : Finset V} (h : s.card = 4) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ s = {a, b, c, d} := by
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp h
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hat
  exact ⟨a, b, c, d, hat.1, hat.2.1, hat.2.2, hbc, hbd, hcd, rfl⟩

/-- **The root-degree-3/4 step.**  For branches `w ∈ W` (`|W| ∈ {3, 4}`) of types `τ w`, with
`Z w > 0` and `lo Z w ≤ Z' w ≤ hi Z w`:
`(Σ A − r − B0) Π Z + x (1 − r − r|W| + Σ B − B0) Π Z' ≥ 0`. -/
theorem Valid.check_step (hR : R.Valid) {V : Type*} [DecidableEq V] {W : Finset V}
    (τ : V → Fin 5) (Z Z' : V → ℚ) (hZ : ∀ w ∈ W, 0 < Z w)
    (hlo : ∀ w ∈ W, R.lo (τ w) * Z w ≤ Z' w) (hhi : ∀ w ∈ W, Z' w ≤ R.hi (τ w) * Z w)
    (hd : W.card = 3 ∨ W.card = 4) :
    0 ≤ (∑ w ∈ W, R.A (τ w) - R.r - R.B0) * ∏ w ∈ W, Z w +
      R.x * (1 - R.r - R.r * W.card + ∑ w ∈ W, R.B (τ w) - R.B0) * ∏ w ∈ W, Z' w := by
  set a := ∑ w ∈ W, R.A (τ w) - R.r - R.B0 with ha
  set b := 1 - R.r - R.r * W.card + ∑ w ∈ W, R.B (τ w) - R.B0 with hb
  have hP : 0 < ∏ w ∈ W, Z w := Finset.prod_pos hZ
  have hloP : (∏ w ∈ W, R.lo (τ w)) * ∏ w ∈ W, Z w ≤ ∏ w ∈ W, Z' w := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun w hw => mul_nonneg (hR.lo_nonneg _) (hZ w hw).le) hlo
  have hhiP : ∏ w ∈ W, Z' w ≤ (∏ w ∈ W, R.hi (τ w)) * ∏ w ∈ W, Z w := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod
      (fun w hw => (mul_nonneg (hR.lo_nonneg _) (hZ w hw).le).trans (hlo w hw)) hhi
  have hx := hR.x_pos
  -- the two end tests
  have hends : 0 ≤ a + b * (R.x * ∏ w ∈ W, R.lo (τ w)) ∧
      0 ≤ a + b * (R.x * ∏ w ∈ W, R.hi (τ w)) := by
    rcases hd with h3 | h4
    · obtain ⟨w1, w2, w3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp h3
      obtain ⟨c1, c2⟩ := hR.deg3 (τ w1) (τ w2) (τ w3)
      have hn1 : w1 ∉ ({w2, w3} : Finset V) := by simp [h12, h13]
      have hn2 : w2 ∉ ({w3} : Finset V) := by simp [h23]
      rw [ha, hb, h3]
      simp only [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton,
        Finset.prod_insert hn1, Finset.prod_insert hn2, Finset.prod_singleton]
      constructor
      · push_cast
        linarith
      · push_cast
        linarith
    · obtain ⟨w1, w2, w3, w4, h12, h13, h14, h23, h24, h34, rfl⟩ := card_eq_four h4
      obtain ⟨c1, c2⟩ := hR.deg4 (τ w1) (τ w2) (τ w3) (τ w4)
      have hn1 : w1 ∉ ({w2, w3, w4} : Finset V) := by simp [h12, h13, h14]
      have hn2 : w2 ∉ ({w3, w4} : Finset V) := by simp [h23, h24]
      have hn3 : w3 ∉ ({w4} : Finset V) := by simp [h34]
      rw [ha, hb, h4]
      simp only [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3,
        Finset.sum_singleton, Finset.prod_insert hn1, Finset.prod_insert hn2,
        Finset.prod_insert hn3, Finset.prod_singleton]
      constructor
      · push_cast
        linarith
      · push_cast
        linarith
  have key := affine_nonneg (a := a) (b := b) hP
    (l := R.x * ∏ w ∈ W, R.lo (τ w)) (u := R.x * ∏ w ∈ W, R.hi (τ w))
    (P' := R.x * ∏ w ∈ W, Z' w)
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hloP hx.le)
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hhiP hx.le) hends.1 hends.2
  linarith

end Record

end Erdos993Lean.Analytic.Density
