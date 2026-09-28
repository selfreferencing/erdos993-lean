import Erdos993Lean.Analytic.Defs

/-!
# Averaging pointwise minorants over a binomial mixture

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F2.
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md`, §1 (conclusion form) and §5.

* `binom_nonneg`, `binom_le_one`: `0 ≤ b_M(j) ≤ 1` for `0 ≤ q ≤ 1`; hence
  `fC_ge_neg_two`: `f_C = 2b_M(j) − b_M(j − 1) − b_M(j + 1) ≥ −2`.
* `kappa_eq`: T1's kernel is `κ = f_L/q + f_R/(1 − q) = f_C + ((1 − 2q)²/(q(1 − q))) b_M(j)`.
* `expect_kappa_nonpos`: a weak valley at `k` gives `E κ ≤ 0` (with `j = k − Y`).
* `expect_ge_of_pointwise`: averaging a pointwise minorant
  `a + b(M/m − 1) − c(M/m − 1)² − ν h(M, Y) − ρ 1[M ≤ r]` of `g(M, Y)` over a probability mixture
  with `E M = m` gives `E g ≥ a − c Var M/m² − ν E h − ρ P(M ≤ r)` (the linear term averages
  to zero).  The multiplier `ν` of `h = δ²` is a single constant, independent of `M`.
-/

namespace Erdos993Lean.Analytic.LargeMean

open Finset

theorem binom_nonneg {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℤ) : 0 ≤ binom M q j := by
  unfold binom
  split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _))
      (pow_nonneg (by linarith) _)
  · exact le_refl 0

theorem binom_le_one {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℤ) : binom M q j ≤ 1 := by
  unfold binom
  split_ifs with h
  · have hsum : ∑ i ∈ Finset.range (M + 1), q ^ i * (1 - q) ^ (M - i) * (M.choose i : ℝ) = 1 := by
      rw [← add_pow]; simp
    have hmem : j.toNat ∈ Finset.range (M + 1) := by
      rw [Finset.mem_range]; omega
    have hle : q ^ j.toNat * (1 - q) ^ (M - j.toNat) * (M.choose j.toNat : ℝ) ≤
        ∑ i ∈ Finset.range (M + 1), q ^ i * (1 - q) ^ (M - i) * (M.choose i : ℝ) :=
      Finset.single_le_sum (f := fun i => q ^ i * (1 - q) ^ (M - i) * (M.choose i : ℝ))
        (fun i _ => mul_nonneg (mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (by linarith) _))
          (Nat.cast_nonneg _)) hmem
    linarith
  · norm_num

/-- `f_C = 2b_M(j) − b_M(j − 1) − b_M(j + 1) ≥ −2`. -/
theorem fC_ge_neg_two {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℤ) :
    -2 ≤ 2 * binom M q j - binom M q (j - 1) - binom M q (j + 1) := by
  have := binom_nonneg (M := M) hq0 hq1 j
  have := binom_le_one (M := M) hq0 hq1 (j - 1)
  have := binom_le_one (M := M) hq0 hq1 (j + 1)
  linarith

/-- T1's kernel: `κ = f_L/q + f_R/(1 − q) = f_C + ((1 − 2q)²/(q(1 − q))) b_M(j)`. -/
theorem kappa_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) (j : ℤ) :
    kappa q M j = (2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) +
      (1 - 2 * q) ^ 2 / (q * (1 - q)) * binom M q j := by
  have h1 : q ≠ 0 := hq0.ne'
  have h2 : 1 - q ≠ 0 := (by linarith : (0:ℝ) < 1 - q).ne'
  unfold kappa
  field_simp
  ring

/-- **A weak valley has nonpositive expected kernel.**  If `(1 − q)P_k ≤ qP_{k−1}` and
`qP_k ≤ (1 − q)P_{k+1}` then `E κ(M, k − Y) = E f_L/q + E f_R/(1 − q) ≤ 0`. -/
theorem expect_kappa_nonpos {ι : Type*} (X : Mixture ι) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) {k : ℤ} (hV : X.WeakValley q k) :
    X.expect (fun M Y => kappa q M (k - Y)) ≤ 0 := by
  have hq1' : 0 < 1 - q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hq1ne : 1 - q ≠ 0 := hq1'.ne'
  have hsplit : ∀ σ ∈ X.S, X.w σ * kappa q (X.M σ) (k - X.Y σ) =
      (1 - q) / q * (X.w σ * binom (X.M σ) q (k - X.Y σ)) - X.w σ * binom (X.M σ) q (k - 1 - X.Y σ)
      + (q / (1 - q) * (X.w σ * binom (X.M σ) q (k - X.Y σ))
        - X.w σ * binom (X.M σ) q (k + 1 - X.Y σ)) := by
    intro σ _
    have e1 : k - 1 - (X.Y σ : ℤ) = k - (X.Y σ : ℤ) - 1 := by ring
    have e2 : k + 1 - (X.Y σ : ℤ) = k - (X.Y σ : ℤ) + 1 := by ring
    rw [e1, e2]
    unfold kappa
    field_simp
  have e : X.expect (fun M Y => kappa q M (k - Y)) =
      ((1 - q) / q * X.prob q k - X.prob q (k - 1)) +
        (q / (1 - q) * X.prob q k - X.prob q (k + 1)) := by
    simp only [Mixture.expect, Mixture.prob]
    rw [Finset.sum_congr rfl hsplit]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e]
  obtain ⟨h1, h2⟩ := hV
  have t1 : (1 - q) / q * X.prob q k ≤ X.prob q (k - 1) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq0]; linarith
  have t2 : q / (1 - q) * X.prob q k ≤ X.prob q (k + 1) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq1']; linarith
  linarith

/-- **Averaging a pointwise quadratic minorant** over a probability mixture with `E M = m`:
if `g(M, Y) ≥ a + b(M/m − 1) − c(M/m − 1)² − ν h(M, Y) − ρ 1[M ≤ r]` on every state, then
`E g ≥ a − c Var M/m² − ν E h − ρ P(M ≤ r)`. -/
theorem expect_ge_of_pointwise {ι : Type*} (X : Mixture ι) (hX : X.IsProb) {m : ℝ}
    (hmean : X.meanM = m) (hm : m ≠ 0) (g h : ℕ → ℕ → ℝ) (r : ℕ) (a b c ν ρ : ℝ)
    (hpt : ∀ σ ∈ X.S, a + b * ((X.M σ : ℝ) / m - 1) - c * ((X.M σ : ℝ) / m - 1) ^ 2
        - ν * h (X.M σ) (X.Y σ) - ρ * (if X.M σ ≤ r then 1 else 0) ≤ g (X.M σ) (X.Y σ)) :
    a - c * (X.varM / m ^ 2) - ν * X.expect h - ρ * X.cdfM r ≤ X.expect g := by
  have hw1 : ∑ σ ∈ X.S, X.w σ = 1 := hX.2
  have hM : ∑ σ ∈ X.S, X.w σ * (X.M σ : ℝ) = m := hmean
  have e1 : ∑ σ ∈ X.S, X.w σ * ((X.M σ : ℝ) / m - 1) = 0 := by
    have : ∀ σ ∈ X.S, X.w σ * ((X.M σ : ℝ) / m - 1) = X.w σ * (X.M σ : ℝ) / m - X.w σ := by
      intro σ _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_div, hM, hw1, div_self hm,
      sub_self]
  have e2 : ∑ σ ∈ X.S, X.w σ * ((X.M σ : ℝ) / m - 1) ^ 2 = X.varM / m ^ 2 := by
    have : ∀ σ ∈ X.S, X.w σ * ((X.M σ : ℝ) / m - 1) ^ 2 =
        X.w σ * ((X.M σ : ℝ) - m) ^ 2 / m ^ 2 := by
      intro σ _
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_div]
    simp only [Mixture.varM, Mixture.expect, hmean]
  have e3 : ∑ σ ∈ X.S, X.w σ * (if X.M σ ≤ r then (1 : ℝ) else 0) = X.cdfM r := by
    rw [Mixture.cdfM, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp
  have hsplit : ∀ σ ∈ X.S, X.w σ * (a + b * ((X.M σ : ℝ) / m - 1) - c * ((X.M σ : ℝ) / m - 1) ^ 2
        - ν * h (X.M σ) (X.Y σ) - ρ * (if X.M σ ≤ r then 1 else 0)) =
      a * X.w σ + b * (X.w σ * ((X.M σ : ℝ) / m - 1)) - c * (X.w σ * ((X.M σ : ℝ) / m - 1) ^ 2)
        - ν * (X.w σ * h (X.M σ) (X.Y σ)) - ρ * (X.w σ * (if X.M σ ≤ r then 1 else 0)) := by
    intro σ _; ring
  have hle : ∑ σ ∈ X.S, X.w σ * (a + b * ((X.M σ : ℝ) / m - 1) - c * ((X.M σ : ℝ) / m - 1) ^ 2
        - ν * h (X.M σ) (X.Y σ) - ρ * (if X.M σ ≤ r then 1 else 0)) ≤ X.expect g := by
    unfold Mixture.expect
    apply Finset.sum_le_sum
    intro σ hσ
    exact mul_le_mul_of_nonneg_left (hpt σ hσ) (hX.1 σ hσ)
  rw [Finset.sum_congr rfl hsplit] at hle
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hle
  rw [hw1, e1, e2, e3] at hle
  have e4 : X.expect h = ∑ σ ∈ X.S, X.w σ * h (X.M σ) (X.Y σ) := rfl
  rw [e4]
  linarith

end Erdos993Lean.Analytic.LargeMean
