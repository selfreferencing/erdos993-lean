import Mathlib
import Erdos993Lean.Analytic.HardCore.Laplace

/-!
# Lower tails of the free count from its Laplace transform (Markov/Chernoff)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A1, extra E3.  Sources: campaign report
`ProofRuns/2026-09-27_zhang_review/reports/T23.md` §0.4 and §1 (`T(M') ≤ e^{−ℓ m} (1 + λ)^{M'}` from
`E(1 − q)^M ≤ e^{−ℓ m}`); `Defs.lean` (`Mixture.cdfM`, the input `TailBound`).

* **`Mixture.cdfM_le_expect_pow_div`** (E3): for every mixture with nonnegative weights, every
  `0 < b ≤ 1` and every `M'`, `P(M ≤ M') ≤ E[b^M] / b^M'` (Markov's inequality for `b^M`, a
  nonincreasing function of `M`).
* `forestMixture_cdfM_le_laplace`: with the Laplace identity (E2), for `0 ≤ s ≤ 1`,
  `P(M ≤ M') ≤ Σ_{S indep} t^|S \ B| (ts)^|S ∩ B| / (Z_F(t) (1 − q + qs)^M')`.
* `forestMixture_cdfM_le`: at `s = 0`, `P(M ≤ M') ≤ (1 + t)^M' Z_{F[C]}(t) / Z_F(t)`.

Scalarity: `b` (resp. `s`) is the argument of the Laplace transform `E[b^M]` of the free count `M`;
E2 produces the transform, these bounds consume it and produce the lower-tail function of `M`
(`TailBound`'s `T`, consumed by the no-valley lemma through `NoValleyAt`).

Namespaces: `Mixture.cdfM_le_expect_pow_div` is in `Erdos993Lean.Analytic.Mixture`; the forest
corollaries are in `Erdos993Lean.Analytic.HardCore`.

Grade: PROVED IN LEAN (standard axioms only).
-/

namespace Erdos993Lean.Analytic

open Finset

namespace Mixture

variable {ι : Type*} (X : Mixture ι)

/-- **E3 (Markov/Chernoff).**  For a mixture with nonnegative weights, `0 < b ≤ 1` and any `M'`:
`P(M ≤ M') ≤ E[b^M] / b^M'`. -/
theorem cdfM_le_expect_pow_div (hw : ∀ σ ∈ X.S, 0 ≤ X.w σ) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (M' : ℕ) : X.cdfM M' ≤ X.expect (fun M _ => b ^ M) / b ^ M' := by
  unfold cdfM expect
  rw [le_div_iff₀ (pow_pos hb0 M'), Finset.sum_mul]
  calc ∑ σ ∈ X.S with X.M σ ≤ M', X.w σ * b ^ M'
      ≤ ∑ σ ∈ X.S with X.M σ ≤ M', X.w σ * b ^ X.M σ := by
        refine Finset.sum_le_sum fun σ hσ => ?_
        rw [Finset.mem_filter] at hσ
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb0.le hb1 hσ.2) (hw σ hσ.1)
    _ ≤ ∑ σ ∈ X.S, X.w σ * b ^ X.M σ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun σ hσ _ => mul_nonneg (hw σ hσ) (pow_nonneg hb0.le _)

end Mixture

namespace HardCore

variable (F : FiniteForest)

/-- The lower tail of `M` from the Laplace identity: for `0 ≤ s ≤ 1`,
`P(M ≤ M') ≤ (Σ_{S indep} t^|S \ B| (ts)^|S ∩ B|) / Z_F(t) / (1 − q + qs)^M'`. -/
theorem forestMixture_cdfM_le_laplace {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤
      (∑ S ∈ indepSets F, t ^ (S \ B).card * (t * s) ^ (S ∩ B).card) / partitionFn F t /
        (1 - actQ t + actQ t * s) ^ M' := by
  rw [← expect_pow_freeCount F hB ht s]
  have hq := actQ_pos ht
  have hq1 := one_sub_actQ_pos ht.le
  refine Mixture.cdfM_le_expect_pow_div _ (forestMixture_isProb F hB ht).1 ?_ ?_ M'
  · exact add_pos_of_pos_of_nonneg hq1 (mul_nonneg hq.le hs0)
  · have := mul_le_mul_of_nonneg_left hs1 hq.le
    linarith

/-- **The lower tail of `M` at `s = 0`**: `P(M ≤ M') ≤ (1 + t)^M' Z_{F[C]}(t) / Z_F(t)`. -/
theorem forestMixture_cdfM_le {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤ (1 + t) ^ M' * partitionFnCompl F B t / partitionFn F t := by
  have hq := actQ_pos ht
  have h := Mixture.cdfM_le_expect_pow_div (forestMixture F B t) (forestMixture_isProb F hB ht).1
    (one_sub_actQ_pos ht.le) (by linarith) M'
  rw [expect_one_sub_pow_freeCount F B ht.le] at h
  have e : 1 - actQ t = (1 + t)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (one_add_mul_one_sub_actQ (t := t) (by positivity))).symm
  rw [e, inv_pow, div_inv_eq_mul] at h
  calc (forestMixture F B t).cdfM M'
      ≤ partitionFnCompl F B t / partitionFn F t * (1 + t) ^ M' := h
    _ = (1 + t) ^ M' * partitionFnCompl F B t / partitionFn F t := by ring

end HardCore

end Erdos993Lean.Analytic
