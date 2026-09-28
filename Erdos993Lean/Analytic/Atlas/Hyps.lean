import Mathlib
import Erdos993Lean.Analytic.Atlas.Profile

/-!
# The O4 atlas (lane A9): the profile hypotheses of the O4 split

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  `thresholdNoValley_of_split`
(`Erdos993Lean/Analytic/Assembly.lean`) proves O4 (`ThresholdNoValley P`) from T1 on `m < 400` (`hsmall`,
the atlas) and the large-mean theorem on `m ≥ 400`, given three facts about the profile.  For the
certified profile `Profile30.P` (`Erdos993Lean/Analytic/Profile30.lean`) they are finite checks on its
data (`decide +kernel`) plus elementary estimates.

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* **`profile30_hD`**: `0 ≤ D(λ) ≤ 8/5`.
* **`profile30_hθ`**: `θ(λ) ≤ 7/10` when `q ∈ [3/8, 8/13]` (bands 7–25, `λ ∈ [3/5, 8/5]`), `θ(λ) ≤ 1`
  everywhere.
* `third_mean_rational`, **`profile30_htail`**: the third-mean tail (Soul's
  `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` §1, the referee's check in
  `LEAN/referee/REVIEW_SOUL_ROUND2.md` item 1): `e^{3ℓ(λ, 0) − 1/10} ≥ 1 + λ_{i+1}` in every band, hence
  `T(λ, m, r) ≤ e^{−ℓm}(1 + λ_{i+1})^r ≤ e^{−m/30}` at `r = ⌈m/3⌉ − 1`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.Profile30

namespace Erdos993Lean.Analytic.Atlas

/-- **The profile's `D`** (hypothesis `hD` of `thresholdNoValley_of_split`): `0 ≤ D ≤ 8/5`. -/
theorem profile30_hD : ∀ t, InRange t → 0 ≤ Profile30.P.Db t ∧ Profile30.P.Db t ≤ 8 / 5 := by
  intro t ht
  have hi := (bandOf_spec ht).1
  have key : ∀ i < 30, 0 ≤ Dt.getD i (8 / 5) ∧ Dt.getD i (8 / 5) ≤ 8 / 5 := by decide +kernel
  obtain ⟨h1, h2⟩ := key _ hi
  show 0 ≤ ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ) ∧ ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ) ≤ 8 / 5
  have h1' := (Rat.cast_le (K := ℝ)).mpr h1
  have h2' := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at h1' h2'
  exact ⟨h1', h2'⟩

theorem edgeR_six : edgeR 6 = 3 / 5 := by unfold edgeR; norm_num [edges]
theorem edgeR_twentyfive : edgeR 25 = 8 / 5 := by unfold edgeR; norm_num [edges]

/-- **The profile's `θ`** (hypothesis `hθ` of `thresholdNoValley_of_split`): `θ ≤ 7/10` on
`q ∈ [3/8, 8/13]` and `θ ≤ 1` everywhere. -/
theorem profile30_hθ : ∀ t, InRange t → 0 ≤ Profile30.P.θb t ∧
    ((3 / 8 ≤ actQ t ∧ actQ t ≤ 8 / 13 ∧ Profile30.P.θb t ≤ 7 / 10) ∨
      ((actQ t ≤ 3 / 8 ∨ 8 / 13 ≤ actQ t) ∧ Profile30.P.θb t ≤ 1)) := by
  intro t ht
  obtain ⟨hi, hlo, hhi⟩ := bandOf_spec ht
  have key1 : ∀ i < 30, 0 ≤ θt.getD i 1 ∧ θt.getD i 1 ≤ 1 := by decide +kernel
  have key2 : ∀ i < 30, 6 ≤ i → i ≤ 24 → θt.getD i 1 ≤ 7 / 10 := by decide +kernel
  have hθ : Profile30.P.θb t = ((θt.getD (bandOf t) 1 : ℚ) : ℝ) := rfl
  have k0 := (Rat.cast_le (K := ℝ)).mpr (key1 _ hi).1
  have k1 := (Rat.cast_le (K := ℝ)).mpr (key1 _ hi).2
  push_cast at k0 k1
  refine ⟨by rw [hθ]; exact k0, ?_⟩
  by_cases hq : actQ t ≤ 3 / 8 ∨ 8 / 13 ≤ actQ t
  · exact Or.inr ⟨hq, by rw [hθ]; exact k1⟩
  · push_neg at hq
    obtain ⟨hq1, hq2⟩ := hq
    have ht1 : 0 < 1 + t := by linarith [ht.1]
    have h35 : 3 / 5 < t := by
      unfold actQ at hq1; rw [lt_div_iff₀ ht1] at hq1; linarith
    have h85 : t < 8 / 5 := by
      unfold actQ at hq2; rw [div_lt_iff₀ ht1] at hq2; linarith
    have hi6 : 6 ≤ bandOf t := by
      by_contra hc
      push_neg at hc
      have := edgeR_mono (bandOf t + 1) 6 (by omega) (by norm_num)
      rw [edgeR_six] at this
      linarith
    have hi24 : bandOf t ≤ 24 := by
      by_contra hc
      push_neg at hc
      have := edgeR_mono 25 (bandOf t) (by omega) (by omega)
      rw [edgeR_twentyfive] at this
      linarith
    have h7 := (Rat.cast_le (K := ℝ)).mpr (key2 _ hi hi6 hi24)
    push_cast at h7
    exact Or.inl ⟨hq1.le, hq2.le, by rw [hθ]; exact h7⟩

/-- `1 + λ_{i+1} ≤ ∑_{j < 12} x^j/j!` with `x = 3ℓ(i, 0) − 1/10 ≥ 0`: `e^{3ℓ − 1/10} > 1 + λ_{i+1}`
(the source's third-mean inequality; smallest margin in band 29). -/
theorem third_mean_rational : ∀ i < 30,
    0 ≤ 3 * (rates.getD i []).getD 0 0 - 1 / 10 ∧
      1 + edges.getD (i + 1) 0 ≤ expPartial (3 * (rates.getD i []).getD 0 0 - 1 / 10) 12 := by
  decide +kernel

/-- **The third-mean tail of the profile** (hypothesis `htail` of `thresholdNoValley_of_split`): for
`m ≥ 400`, `r = ⌈m/3⌉ − 1` has `r < M1`, `m/3 ≤ r + 1` and `T(λ, m, r) ≤ e^{−m/30}`. -/
theorem profile30_htail : ∀ t, InRange t → ∀ m, 400 ≤ m →
    ∃ r : ℕ, r < Profile30.P.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧
      Profile30.P.Tb t m r ≤ Real.exp (-(m / 30)) := by
  intro t ht m hm
  have hi := (bandOf_spec ht).1
  obtain ⟨hx0, hx⟩ := third_mean_rational _ hi
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℚ, ℓ = (rates.getD (bandOf t) []).getD 0 0 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℚ, h = edges.getD (bandOf t + 1) 0 := ⟨_, rfl⟩
  rw [← hℓ] at hx0 hx
  rw [← hh] at hx
  have hm3 : 0 < m / 3 := by linarith
  have hc1 : 1 ≤ ⌈m / 3⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hm3).ne'
  have hcle : m / 3 ≤ (⌈m / 3⌉₊ : ℝ) := Nat.le_ceil _
  have hclt : (⌈m / 3⌉₊ : ℝ) < m / 3 + 1 := Nat.ceil_lt_add_one hm3.le
  have hrcast : ((⌈m / 3⌉₊ - 1 : ℕ) : ℝ) = (⌈m / 3⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hc1]; simp
  have hrm : ((⌈m / 3⌉₊ - 1 : ℕ) : ℝ) ≤ m / 3 := by rw [hrcast]; linarith
  refine ⟨⌈m / 3⌉₊ - 1, ?_, ?_, ?_⟩
  · have h1 : ((⌈m / 3⌉₊ - 1 : ℕ) : ℝ) < (⌈m⌉₊ : ℝ) + 1 := by
      have := Nat.le_ceil m
      linarith
    show ⌈m / 3⌉₊ - 1 < ⌈m⌉₊ + 1
    exact_mod_cast h1
  · rw [hrcast]; linarith
  · -- `T ≤ e^{−ℓ m} (1 + h)^r ≤ e^{−ℓ m + (m/3) log(1 + h)} ≤ e^{−m/30}`
    have hT : Profile30.P.Tb t m (⌈m / 3⌉₊ - 1) ≤ tailTerm t m (⌈m / 3⌉₊ - 1) 0 :=
      (min5_le (fun k => tailTerm t m (⌈m / 3⌉₊ - 1) k)).2 0 (by norm_num)
    refine hT.trans ?_
    have htv : ((Profile30.tvals.getD 0 0 : ℚ) : ℝ) = 0 := by norm_num [Profile30.tvals]
    have hterm : tailTerm t m (⌈m / 3⌉₊ - 1) 0 =
        Real.exp (-((ℓ : ℝ) * m)) * (1 + (h : ℝ)) ^ (⌈m / 3⌉₊ - 1) := by
      unfold tailTerm ell hiEdge
      rw [← hℓ, ← hh, htv, mul_zero, add_zero, div_one]
    rw [hterm]
    have hx0R : (0 : ℝ) ≤ 3 * (ℓ : ℝ) - 1 / 10 := by
      have := (Rat.cast_le (K := ℝ)).mpr hx0; push_cast at this; linarith
    have hh0 : (0 : ℝ) ≤ h := by
      have := edgeR_pos (bandOf t + 1) (by omega)
      unfold edgeR at this
      rw [hh]; exact this.le
    have hexp : 1 + (h : ℝ) ≤ Real.exp (3 * (ℓ : ℝ) - 1 / 10) := by
      have h1 : ((1 + h : ℚ) : ℝ) ≤ ((expPartial (3 * ℓ - 1 / 10) 12 : ℚ) : ℝ) := by exact_mod_cast hx
      rw [expPartial_eq] at h1
      push_cast at h1
      exact h1.trans (Real.sum_le_exp_of_nonneg hx0R 12)
    have hlog : Real.log (1 + (h : ℝ)) ≤ 3 * (ℓ : ℝ) - 1 / 10 := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact hexp
    have hlog0 : 0 ≤ Real.log (1 + (h : ℝ)) := Real.log_nonneg (by linarith)
    have hpow : (1 + (h : ℝ)) ^ (⌈m / 3⌉₊ - 1) =
        Real.exp (((⌈m / 3⌉₊ - 1 : ℕ) : ℝ) * Real.log (1 + (h : ℝ))) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [hpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : ((⌈m / 3⌉₊ - 1 : ℕ) : ℝ) * Real.log (1 + (h : ℝ)) ≤ m / 3 * Real.log (1 + (h : ℝ)) :=
      mul_le_mul_of_nonneg_right hrm hlog0
    have h2 : m / 3 * Real.log (1 + (h : ℝ)) ≤ m / 3 * (3 * (ℓ : ℝ) - 1 / 10) :=
      mul_le_mul_of_nonneg_left hlog hm3.le
    have e : m / 3 * (3 * (ℓ : ℝ) - 1 / 10) = (ℓ : ℝ) * m - m / 30 := by ring
    linarith

end Erdos993Lean.Analytic.Atlas
