import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperBounds

/-!
# O1 on the upper band `[8/5, 7/3]`: the selected-leaf base (`UpperLeafOK`, lane A14)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lane A14).  Sources: Astra's
`UPPER_SHARP_SIGNED_PORT_PROOF.md` (reviewed snapshot `LEAN/referee/astra_o1/snapshot_0845`: "A selected leaf has
`F = Dq², u = q, y = log(1+λ), G = 0`"), the referee's check `LEAN/referee/REVIEW_ASTRA_O1_UPPER_PROOF.md`,
TASK 5 (true minimum margin `0.0337` at `λ = 7/3`; `review_upper_proof/u5_leaf_psd_iv.py`).

At a selected leaf the reserve inequality of `StepCert` reads, with `q = λ/(1 + λ)`, `ℓ = log(1 + λ)`,
`α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100`, `A = 1 + 3q/5`:

  `α ℓ + β q + γ q²/ℓ ≤ A q − q (1 − q) = (8/5) q²`.

Multiplying by `ℓ (1 + λ) > 0` and using `q (1 + λ) = λ`, it is `q · P(λ, ℓ) ≥ 0` with the polynomial

  `P(λ, ℓ) = (8/5) λ ℓ − (1 + λ) ℓ²/2 − (λ − 1)(1 + λ) ℓ/27 − (31/100) λ²`.

`P` is a concave quadratic in `ℓ` for fixed `λ` and in `λ` for fixed `ℓ`, so on the box
`[8/5, 7/3] × [19/20, 1227/1000]` it is at least its bilinear interpolation of the four corner values
(`0.410, 0.319, 0.198, 0.182`, all positive); `leaf_poly` is the resulting certificate (`linarith` over the
seven products of the box constraints).  The box contains `(λ, log(1 + λ))`: `log x ≤ x/e` and
`log x ≥ 2 − e/x` with `2.7182818283 < e < 2.7182818286` (`log_le_hi`, `log_ge_lo`).

Main result: **`upperLeafOK : UpperLeafOK`**.

Scalarity: `λ` is the activity (an input); `ℓ = log(1 + λ)` is the log-mass of the selected leaf's
occupation message `q`; the corner values are outputs.  Consumer: `stepCert_upper` (field `leaf` of
`StepCert`), hence the leaf base of lane A11's induction.
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

namespace Upper

/-- `log (1 + λ) ≤ 1227/1000` for `0 ≤ λ ≤ 7/3` (`log x ≤ x/e`, `e > 2.7182818283`). -/
theorem log_le_hi {lam : ℝ} (h0 : 0 ≤ lam) (h : lam ≤ 7 / 3) : log (1 + lam) ≤ 1227 / 1000 := by
  have hx : 0 < 1 + lam := by linarith
  have he := Real.exp_one_gt_d9
  have hep : 0 < exp 1 := exp_pos 1
  have h1 : log ((1 + lam) / exp 1) ≤ (1 + lam) / exp 1 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx.ne' hep.ne', Real.log_exp] at h1
  have h2 : (1 + lam) / exp 1 ≤ 1227 / 1000 := by
    rw [div_le_iff₀ hep]
    linarith
  linarith

/-- `log (1 + λ) ≥ 19/20` for `λ ≥ 8/5` (`log x ≥ 2 − e/x`, `e < 2.7182818286`). -/
theorem log_ge_lo {lam : ℝ} (h : 8 / 5 ≤ lam) : 19 / 20 ≤ log (1 + lam) := by
  have hx : 0 < 1 + lam := by linarith
  have he := Real.exp_one_lt_d9
  have hep : 0 < exp 1 := exp_pos 1
  have h1 : 1 - ((1 + lam) / exp 1)⁻¹ ≤ log ((1 + lam) / exp 1) :=
    Real.one_sub_inv_le_log_of_pos (by positivity)
  rw [Real.log_div hx.ne' hep.ne', Real.log_exp, inv_div] at h1
  have h2 : exp 1 / (1 + lam) ≤ 21 / 20 := by
    rw [div_le_iff₀ hx]
    linarith
  linarith

/-- **The leaf polynomial is nonnegative on the box** `[8/5, 7/3] × [19/20, 1227/1000]`: bilinear
interpolation of the corner values plus the two concavity remainders
`((1 + λ)/2)(ℓ − 19/20)(1227/1000 − ℓ)` and `(ℓᵢ/27 + 31/100)(λ − 8/5)(7/3 − λ)`. -/
theorem leaf_poly {lam l : ℝ} (h1 : 8 / 5 ≤ lam) (h2 : lam ≤ 7 / 3) (hl1 : 19 / 20 ≤ l)
    (hl2 : l ≤ 1227 / 1000) :
    0 ≤ 8 / 5 * lam * l - (1 + lam) * l ^ 2 / 2 - (lam - 1) * (1 + lam) * l / 27 -
      31 / 100 * lam ^ 2 := by
  have ha : 0 ≤ lam - 8 / 5 := by linarith
  have ha' : 0 ≤ 7 / 3 - lam := by linarith
  have hb : 0 ≤ l - 19 / 20 := by linarith
  have hb' : 0 ≤ 1227 / 1000 - l := by linarith
  have hlam1 : 0 ≤ 1 + lam := by linarith
  linarith [mul_nonneg ha hb, mul_nonneg ha hb', mul_nonneg ha' hb, mul_nonneg ha' hb',
    mul_nonneg (mul_nonneg ha ha') hb, mul_nonneg (mul_nonneg ha ha') hb',
    mul_nonneg (mul_nonneg hb hb') hlam1]

end Upper

open Upper in
/-- **The selected-leaf base of the upper band**: for `λ ∈ [8/5, 7/3]`,
`α log(1+λ) + β q + γ q²/log(1+λ) ≤ A q − q (1 − q)` with `α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100`,
`A = 1 + 3q/5` (`StepCert`'s form of the leaf base; the right side is `(8/5) q²`). -/
theorem upperLeafOK : UpperLeafOK := by
  intro lam h1 h2
  rw [msg_zero, lmass_zero]
  have hlam : 0 < lam := by linarith
  have hl1 := log_ge_lo h1
  have hl2 := log_le_hi hlam.le h2
  have hl0 : 0 < log (1 + lam) := by linarith
  have hP := leaf_poly h1 h2 hl1 hl2
  have hx : 0 < 1 + lam := by linarith
  have hq0 : 0 < actQ lam := Tails.actQ_pos hlam
  have hq1 : actQ lam * (1 + lam) = lam := by
    unfold actQ
    field_simp
  set q := actQ lam with hq
  set l := log (1 + lam) with hl
  have ht : 31 * lam / 100 * q ^ 2 / l * l = 31 * lam / 100 * q ^ 2 := div_mul_cancel₀ _ hl0.ne'
  set t := 31 * lam / 100 * q ^ 2 / l with htdef
  have hmul : (8 / 5 * q ^ 2 - q / 2 * l - (lam - 1) / 27 * q - t) * (l * (1 + lam)) =
      q * (8 / 5 * lam * l - (1 + lam) * l ^ 2 / 2 - (lam - 1) * (1 + lam) * l / 27 -
        31 / 100 * lam ^ 2) := by
    linear_combination (8 / 5 * q * l - 31 / 100 * lam * q) * hq1 - (1 + lam) * ht
  have hG : 0 ≤ 8 / 5 * q ^ 2 - q / 2 * l - (lam - 1) / 27 * q - t := by
    have hpos : 0 < l * (1 + lam) := mul_pos hl0 hx
    have hqP : 0 ≤ q * (8 / 5 * lam * l - (1 + lam) * l ^ 2 / 2 - (lam - 1) * (1 + lam) * l / 27 -
        31 / 100 * lam ^ 2) := mul_nonneg hq0.le hP
    rw [← hmul] at hqP
    exact (mul_nonneg_iff_of_pos_right hpos).mp hqP
  have e : uCapA lam * q - q * (1 - q) = 8 / 5 * q ^ 2 := by
    unfold uCapA
    ring
  rw [e]
  have e2 : uAlpha lam * l + uBeta lam * q + uGamma lam * q ^ 2 / l =
      q / 2 * l + (lam - 1) / 27 * q + t := by
    unfold uAlpha uBeta uGamma
    rw [htdef]
  rw [e2]
  linarith

end Erdos993Lean.Analytic.Reserve
