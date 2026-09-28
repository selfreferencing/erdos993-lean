import Mathlib
import Erdos993Lean.Analytic.Tail.Weight

/-!
# The tail input T3, part 15: the lower tail of the free count (the consumer form of O3)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A3.  Source: `SOUL/O3/per_unit_proof.md` §5
and `SOUL/RESULTS/O3.md` (the H3 handoff): for integers `j ≥ 0`,
`P(M ≤ j) ≤ E[(1 − q + q z)^M] (1 − q + q z)^{−j} ≤ exp(−ℓ m) ((1 + λ)/(1 + λ z))^j`.

Main results:
* `cdfM_le_expect_pow` (Markov/Chernoff for any mixture with nonnegative weights and `0 < b ≤ 1`):
  `P(M ≤ M') ≤ E[b^M] / b^{M'}`;
* `forestMixture_w_nonneg`;
* `tail_fallback` (**unconditional**): `P(M ≤ j) ≤ exp(−q(1 − q) r(λ, z) m) ((1 + λ)/(1 + λ z))^j`;
* `tail_t3` (given `T3UNonneg`, the leaf condition, `λ ≤ 6`) and `tail_t31` (given `PerUnitRate`):
  `P(M ≤ j) ≤ exp(−ℓ m) ((1 + λ)/(1 + λ z))^j`.
-/

namespace Erdos993Lean.Analytic.Tail

open Finset

/-- **Markov/Chernoff**: for a mixture with nonnegative weights and `0 < b ≤ 1`,
`P(M ≤ M') ≤ E[b^M] / b^{M'}`. -/
theorem cdfM_le_expect_pow {ι : Type*} (X : Mixture ι) (hw : ∀ σ ∈ X.S, 0 ≤ X.w σ) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (M' : ℕ) :
    X.cdfM M' ≤ X.expect (fun M _ => b ^ M) / b ^ M' := by
  unfold Mixture.cdfM Mixture.expect
  rw [le_div_iff₀ (pow_pos hb0 M'), Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro σ hσ
  split_ifs with h
  · -- `b^{M'} ≤ b^{M σ}` for `M σ ≤ M'`
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb0.le hb1 h) (hw σ hσ)
  · exact mul_nonneg (hw σ hσ) (pow_nonneg hb0.le _)

theorem forestMixture_w_nonneg (F : FiniteForest) (B : Finset (Fin F.n)) {t : ℝ} (ht : 0 < t) :
    ∀ σ ∈ (forestMixture F B t).S, 0 ≤ (forestMixture F B t).w σ := by
  intro σ _
  classical
  have hZ : 0 < partitionFn F t := by
    rw [partitionFn_eq_Zw]
    exact Zw_pos (fun _ => ht.le) _
  simp only [forestMixture]
  positivity

/-- `1 − q + q z = (1 + λ z)/(1 + λ)`. -/
theorem one_sub_actQ_add {t : ℝ} (ht : 0 ≤ t) (z : ℝ) : 1 - actQ t + actQ t * z = (1 + t * z) / (1 + t) := by
  unfold actQ
  have : (1 + t) ≠ 0 := by linarith
  field_simp
  ring

/-- The Chernoff step with `b = 1 − q + q z`: `P(M ≤ j) ≤ E[b^M] ((1 + λ)/(1 + λ z))^j`. -/
theorem cdfM_le_laplace (F : FiniteForest) (B : Finset (Fin F.n)) {t z : ℝ} (ht : 0 < t)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (j : ℕ) :
    (forestMixture F B t).cdfM j ≤
      (forestMixture F B t).expect (fun M _ => (1 - actQ t + actQ t * z) ^ M) *
        ((1 + t) / (1 + t * z)) ^ j := by
  have hb := one_sub_actQ_add ht.le z
  have h1 : 0 < 1 + t * z := by positivity
  have h2 : 0 < 1 + t := by linarith
  have hb0 : 0 < 1 - actQ t + actQ t * z := by rw [hb]; positivity
  have hb1 : 1 - actQ t + actQ t * z ≤ 1 := by
    rw [hb, div_le_one h2]
    nlinarith
  have h := cdfM_le_expect_pow (forestMixture F B t) (forestMixture_w_nonneg F B ht) hb0 hb1 j
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, ← inv_pow]
  congr 2
  rw [hb, inv_div]

/-- **The lower tail of `M` from Soul's fallback (unconditional)**: for every forest, every
independent `B`, `λ > 0`, `z ∈ [0, 1]` and `j`:
`P(M ≤ j) ≤ exp(−q (1 − q) r(λ, z) m) · ((1 + λ)/(1 + λ z))^j`. -/
theorem tail_fallback (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t z : ℝ} (ht : 0 < t) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) (j : ℕ) :
    (forestMixture F B t).cdfM j ≤
      Real.exp (-(actQ t * (1 - actQ t) * rFallback t z) * (forestMixture F B t).meanM) *
        ((1 + t) / (1 + t * z)) ^ j :=
  (cdfM_le_laplace F B ht hz0 hz1 j).trans
    (mul_le_mul_of_nonneg_right (laplace_fallback_mixture F B hB ht hz0 hz1) (by positivity))

/-- **The lower tail of `M` from Theorem T3-2 (repaired)**: given `T3UNonneg λ z a ℓ`. -/
theorem tail_t3 (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : LeafCondition F.graph B)
    {lam z a ell : ℝ} (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ha : 0 ≤ a) (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z)))
    (hU : T3UNonneg lam z a ell) (j : ℕ) :
    (forestMixture F B lam).cdfM j ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) * ((1 + lam) / (1 + lam * z)) ^ j :=
  (cdfM_le_laplace F B hlam0 hz0 hz1 j).trans (mul_le_mul_of_nonneg_right
    (t3_reduction_mixture F B hB hleaf hlam0 hlam6 hz0 hz1 ha hiso hU) (by positivity))

/-- **The lower tail of `M` from Theorem T3-1 (per-unit form)**: given `PerUnitRate λ z ℓ`. -/
theorem tail_t31 (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {lam z ell : ℝ} (hlam0 : 0 < lam)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hR : PerUnitRate lam z ell) (j : ℕ) :
    (forestMixture F B lam).cdfM j ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) * ((1 + lam) / (1 + lam * z)) ^ j :=
  (cdfM_le_laplace F B hlam0 hz0 hz1 j).trans (mul_le_mul_of_nonneg_right
    (t31_reduction_mixture F B hB hlam0 hz0 hz1 hell hiso hR) (by positivity))

end Erdos993Lean.Analytic.Tail
