import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperTail
import Erdos993Lean.Analytic.Reserve.UpperLeaf
import Erdos993Lean.Analytic.Reserve.Assembly

/-!
# O1 on the upper band `[8/5, 7/3]`: the step certificate and the band conclusion (lane A14)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lane A14).  Sources: Astra's
`UPPER_SHARP_SIGNED_PORT_PROOF.md` (reviewed snapshot `LEAN/referee/astra_o1/snapshot_0845`; "Consumer, scalarity
and residual": at a paid component root PSD gives `F ≥ 0`, and `Var K_B = (1 − q) W + q² Var M`, `W = q E M`
give the cap `D = 8/5`), and the referee's `LEAN/referee/REVIEW_ASTRA_O1_UPPER_PROOF.md` (TASK 2, TASK 5, TASK 6).

The glue from the three numeric obligations of `Reserve/UpperDefs.lean` to lane A11's induction:

* **`stepCert_upper`**: for `λ ∈ [8/5, 7/3]`, `StepCert` of the signed reserve `α y + β u + γ u²/y`
  (`α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100`) with cap `A = 1 + 3q/5`: PSD `β² ≤ 4αγ` is rational in `λ`
  (`Upper.upper_psd`); the leaf base is `UpperLeafOK`; on the box `T ≤ 6`, `Y ≤ 4` the comparisons come
  from `UpperBoxOK`, with CC from `β² T ≤ 8 α Z` and the Pinsker half of `EntropyOK`
  (`compCC_nonneg_of_entropy`, lane A11); beyond the box from `UpperTailOK`;
* **`bandVar_upper`**: `Var M ≤ (8/5) E M` for every forest, every `λ ∈ [8/5, 7/3]` and every
  maximum-weight independent `B` (lane A11's `varM_le_of_stepCert` with `1 + (8/5 − 1) q = A`, and the
  leaf property `leafProp_of_isMaxWeight`), from `EntropyOK` and `UpperBoxOK` (the tails and the leaf base
  are proved: `upperTailOK`, `upperLeafOK`); `bandVar_upper_of_box` also discharges `EntropyOK`
  (lane A13's `entropyOK`).

Scalarity: `D = 8/5` is an output (it bounds `Var M / E M` of the actual forest mixture; consumer
`VarianceBound` through `Profile30.P.Db` on `(8/5, 7/3]`); `A = 1 + 3q/5` is the same bound in `K_B` form,
used at the component roots; `α, β, γ` are the fixed design coefficients of the certified step (the reserve
`Φ(y, u)` attached to each actual rooted subtree, with the signed port `u = U⁰ − U¹` as its object).
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

/-- **The step certificate on the upper band.**  For `λ ∈ [8/5, 7/3]`, the entropy facts, the finite box
and the analytic tails of the upper band and its selected-leaf base give the per-activity certificate of
the signed reserve `uAlpha λ · y + uBeta λ · u + uGamma λ · u²/y` with cap `uCapA λ`. -/
theorem stepCert_upper (hE : EntropyOK) (hbox : UpperBoxOK) (htail : UpperTailOK)
    (hleaf : UpperLeafOK) {lam : ℝ} (hlo : 8 / 5 ≤ lam) (hhi : lam ≤ 7 / 3) :
    StepCert (uGamma lam) lam (uAlpha lam) (uBeta lam) (uCapA lam) := by
  have hlam : 0 < lam := by linarith
  have hα : 0 ≤ uAlpha lam := by
    have := Upper.uAlpha_ge hlo
    linarith
  have hγ : 0 < uGamma lam := by
    have := Upper.uGamma_ge hlo
    linarith
  refine ⟨hlam, hα, hγ, Upper.upper_psd hlo hhi, hleaf lam hlo hhi, ?_⟩
  intro T Y hT hY
  by_cases h : T ≤ 6 ∧ Y ≤ 4
  · -- the finite box: CC from `β² T ≤ 8 α Z` and the Pinsker floor
    obtain ⟨hZ, h8, hCB, hBC⟩ := hbox lam T Y hlo hhi hT h.1 hY h.2
    exact ⟨hZ, compCC_nonneg_of_entropy hE hlam hT hY hα hZ h8, hCB, hBC⟩
  · -- the analytic tails
    apply htail lam T Y hlo hhi hT hY
    by_cases hT6 : T ≤ 6
    · left
      by_contra hY4
      exact h ⟨hT6, by linarith⟩
    · right
      linarith

/-- **O1 on the upper band** (`D = 8/5`): for every forest, every activity `t ∈ [8/5, 7/3]` and every
maximum-weight independent set `B`, `Var M ≤ (8/5) E M`, from the entropy facts and the finite box of the
upper band. -/
theorem bandVar_upper (hE : EntropyOK) (hbox : UpperBoxOK) :
    ∀ F : FiniteForest, ∀ t : ℝ, 8 / 5 ≤ t → t ≤ 7 / 3 → ∀ B, IsMaxWeight F t B →
      (forestMixture F B t).varM ≤ 8 / 5 * (forestMixture F B t).meanM := by
  intro F t hlo hhi B hB
  have ht : 0 < t := by linarith
  have hcert := stepCert_upper hE hbox upperTailOK upperLeafOK hlo hhi
  have hA : uCapA t = 1 + (8 / 5 - 1) * actQ t := by
    unfold uCapA
    ring
  rw [hA] at hcert
  exact varM_le_of_stepCert F hB.1 (leafProp_of_isMaxWeight F ht hB) hcert

/-- `bandVar_upper` with the entropy facts discharged (lane A13's `entropyOK`): O1 on the upper band from
the finite box alone. -/
theorem bandVar_upper_of_box (hbox : UpperBoxOK) :
    ∀ F : FiniteForest, ∀ t : ℝ, 8 / 5 ≤ t → t ≤ 7 / 3 → ∀ B, IsMaxWeight F t B →
      (forestMixture F B t).varM ≤ 8 / 5 * (forestMixture F B t).meanM :=
  bandVar_upper entropyOK hbox

end Erdos993Lean.Analytic.Reserve
