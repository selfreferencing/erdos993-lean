import Mathlib
import Erdos993Lean.Analytic.HardCore.Mixture

/-!
# The Laplace transform of the free count `M`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A1, extra E2.  Sources: campaign report
`ProofRuns/2026-09-27_zhang_review/reports/T23.md` §1 ("Laplace: `E(1 − q + qt)^M = E t^{K_B} =
Z_F(λ on C, λ t on B)/Z_F`; `t = 0`: `E(1 − q)^M = P(S ∩ B = ∅) = Z_{F[C]}/Z_F`"); T. Zhang,
*Exact Certificates for Unimodality of Forest Independence Polynomials*, v1.1, Lemma 4.2.

For a forest `F`, an independent set `B`, `C = Bᶜ`, an activity `t > 0` and `q = t/(1 + t)`:

* **`expect_pow_freeCount`** (E2): for every real `s`,
  `E[(1 − q + qs)^M] = Σ_{S indep} t^|S \ B| (ts)^|S ∩ B| / Z_F(t)` (activity `t` on `C`, `ts` on
  `B`): conditionally on `σ`, `|S ∩ B| ~ Bin(M σ, q)` has generating function `(1 − q + qs)^M`.
* `partitionFnCompl F B t = Z_{F[C]}(t) = Σ_{σ ⊆ C independent} t^|σ|`, and
  **`expect_one_sub_pow_freeCount`** (E2 at `s = 0`): `E(1 − q)^M = Z_{F[C]}(t)/Z_F(t)`
  (the free-vertex factor `(1 + t)^M` cancels against `(1 − q)^M`).

Namespace: `Erdos993Lean.Analytic.HardCore`.

Grade: PROVED IN LEAN (standard axioms only).
-/

namespace Erdos993Lean.Analytic.HardCore

open Finset

variable (F : FiniteForest)

/-- **E2, the Laplace identity (T23 §1).**  For an independent set `B`, `t > 0` and every real `s`,
`E[(1 − q + qs)^M] = (Σ_{S indep} t^|S \ B| (ts)^|S ∩ B|) / Z_F(t)`. -/
theorem expect_pow_freeCount {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (s : ℝ) :
    (forestMixture F B t).expect (fun M _ => (1 - actQ t + actQ t * s) ^ M) =
      (∑ S ∈ indepSets F, t ^ (S \ B).card * (t * s) ^ (S ∩ B).card) / partitionFn F t := by
  have h := expect_eq_sum_indepSets F hB ht (fun _ k => s ^ k)
  simp only [sum_pow_mul_binom] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [mul_pow, ← Finset.card_sdiff_add_card_inter S B, pow_add]
  ring

/-- The partition function of the induced forest `F[C]`, `C = Bᶜ`:
`Z_{F[C]}(t) = Σ_{σ ⊆ C independent} t^|σ|`. -/
noncomputable def partitionFnCompl (B : Finset (Fin F.n)) (t : ℝ) : ℝ :=
  ∑ σ ∈ states F B, t ^ σ.card

theorem one_le_partitionFnCompl (B : Finset (Fin F.n)) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ partitionFnCompl F B t := by
  unfold partitionFnCompl
  have h := Finset.single_le_sum (f := fun σ : Finset (Fin F.n) => t ^ σ.card)
    (fun σ _ => pow_nonneg ht _) (empty_mem_states F B)
  simpa using h

/-- **E2 at `s = 0` (T23 §1, Zhang Lemma 4.2 summed).**  `E(1 − q)^M = Z_{F[C]}(t) / Z_F(t)`. -/
theorem expect_one_sub_pow_freeCount (B : Finset (Fin F.n)) {t : ℝ} (ht : 0 ≤ t) :
    (forestMixture F B t).expect (fun M _ => (1 - actQ t) ^ M) =
      partitionFnCompl F B t / partitionFn F t := by
  have h := one_add_mul_one_sub_actQ (t := t) (by positivity)
  unfold Mixture.expect partitionFnCompl
  simp only [forestMixture_S, forestMixture_w, forestMixture_M]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  calc t ^ σ.card * (1 + t) ^ freeCount F B σ / partitionFn F t * (1 - actQ t) ^ freeCount F B σ
      = t ^ σ.card * ((1 + t) * (1 - actQ t)) ^ freeCount F B σ / partitionFn F t := by
        rw [mul_pow]
        ring
    _ = t ^ σ.card / partitionFn F t := by rw [h, one_pow, mul_one]

end Erdos993Lean.Analytic.HardCore
