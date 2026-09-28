import Mathlib

/-!
# Quadratic majorants of inverse powers

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F2.
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md`, §4.

For `t ≥ 1/3`:
* `inv_sq_le_quad`: `t^{−2} ≤ 1 − 2(t − 1) + 15(t − 1)²`;
* `inv_pow_five_halves_le_quad`: `t^{−5/2} ≤ 1 − (5/2)(t − 1) + 30(t − 1)²`
  (written `1/(t² √t)`).

The source proves them by Taylor's integral remainder.  Here they are exact polynomial
certificates: with `y = t − 1`, `t²(1 − 2y + 15y²) − 1 = y²(3y + 2)(5y + 6)`; with `r = √t`,
`r⁵(1 − (5/2)(r² − 1) + 30(r² − 1)²) − 1 = (r − 1)² R(r)`, and `R ≥ 0` for `r² ≥ 1/3` by a
linear certificate in `r` and `c = r²` (`R = c²(30r + 60)(c − 1/3) + c(75r/2 + 15)(c − 1/3)
+ (17r/2 + 2)(c − 1/3) + (5/6)(r − 2/5)`).
-/

namespace Erdos993Lean.Analytic.LargeMean

/-- `t^{−2} ≤ 1 − 2(t − 1) + 15(t − 1)²` for `t ≥ 1/3` (equality at `t = 1/3` and `t = 1`). -/
theorem inv_sq_le_quad {t : ℝ} (ht : 1 / 3 ≤ t) : 1 / t ^ 2 ≤ 1 - 2 * (t - 1) + 15 * (t - 1) ^ 2 := by
  have htpos : 0 < t := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (t - 1)) (by linarith : (0:ℝ) ≤ 3 * (t - 1) + 2))
    (by linarith : (0:ℝ) ≤ 5 * (t - 1) + 6)]

/-- `t^{−5/2} ≤ 1 − (5/2)(t − 1) + 30(t − 1)²` for `t ≥ 1/3`. -/
theorem inv_pow_five_halves_le_quad {t : ℝ} (ht : 1 / 3 ≤ t) :
    1 / (t ^ 2 * Real.sqrt t) ≤ 1 - 5 / 2 * (t - 1) + 30 * (t - 1) ^ 2 := by
  have htpos : 0 < t := by linarith
  obtain ⟨r, hr0, rfl⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = t :=
    ⟨Real.sqrt t, Real.sqrt_pos.mpr htpos, Real.sq_sqrt htpos.le⟩
  rw [Real.sqrt_sq hr0.le, div_le_iff₀ (by positivity)]
  have hr25 : 2 / 5 ≤ r := by nlinarith
  have hc : 0 ≤ r ^ 2 - 1 / 3 := by linarith
  have hR : 0 ≤ 30 * r ^ 7 + 60 * r ^ 6 + 55 / 2 * r ^ 5 - 5 * r ^ 4 - 4 * r ^ 3 - 3 * r ^ 2
      - 2 * r - 1 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (r ^ 2)) (by linarith : (0:ℝ) ≤ 30 * r + 60)) hc,
      mul_nonneg (mul_nonneg (sq_nonneg r) (by linarith : (0:ℝ) ≤ 75 / 2 * r + 15)) hc,
      mul_nonneg (by linarith : (0:ℝ) ≤ 17 / 2 * r + 2) hc]
  nlinarith [mul_nonneg (sq_nonneg (r - 1)) hR]

end Erdos993Lean.Analytic.LargeMean
