import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Binom
import Erdos993Lean.Analytic.Fourier.Main
import Erdos993Lean.Analytic.LargeMean.Averaging
import Erdos993Lean.Analytic.LargeMean.Envelope
import Erdos993Lean.Analytic.LargeMean.Constants
import Erdos993Lean.Analytic.Atlas.Checker

/-!
# The O4 atlas (lane A9): the quadratic penalty, the Fourier tail and `e^{−x}`

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  Sources: Soul's `SOUL/O4/ATLAS_PROOF.md`
(sections "Skipped integers and the closed infinite fibre tail" and "Candidate repair and arithmetic
direction") and `SOUL/O4/PARAMETER_BOX_PROOF.md` ("Infinite M tail"); lane F1's binomial Fourier
estimate `fC_sub_gaussCurv_le` (`Erdos993Lean/Analytic/Fourier/Main.lean`).

Soul's tail uses `κ ≥ −1/(4vM)` for `vM ≥ 16`; in Lean the Fourier estimate is available (and used
here) only for `u = vM ≥ 25`.

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* `quad_ge_at_left`, `quad_ge_at_right`, `quad_ge_at_vertex` and the checker forms `quadMinI_le`,
  `quadMinLeft_le`, `quadMinRight_le`: the clamped minima of `μδ² + cδ` (`μ > 0`).
* `gaussCurv_ge`: `G_u(d) ≥ −a₀ u^{−3/2}`.
* **`kappa_ge_fourier`**: `κ_q(M, j) ≥ −(1/(20u) + 1/u²)` for `u = M q(1 − q) ≥ 25`.
* `expPartial_go`, `expPartial_eq`, **`exp_neg_le_expNegUpper`**: `e^{−x} ≤ 1/∑_{i < 120} x^i/i!` for
  rational `x ≥ 0`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.Atlas

/-! ### The quadratic `μδ² + cδ` -/

theorem quad_ge_at_left {mu c lo x : ℝ} (hmu : 0 < mu) (hlo : -c / (2 * mu) < lo) (hx : lo ≤ x) :
    mu * (lo * lo) + c * lo ≤ mu * (x * x) + c * x := by
  have hv : c = -2 * mu * (-c / (2 * mu)) := by field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by nlinarith : (0 : ℝ) ≤ mu * (x + lo) + c)]

theorem quad_ge_at_right {mu c hi x : ℝ} (hmu : 0 < mu) (hhi : hi < -c / (2 * mu)) (hx : x ≤ hi) :
    mu * (hi * hi) + c * hi ≤ mu * (x * x) + c * x := by
  have hv : c = -2 * mu * (-c / (2 * mu)) := by field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by nlinarith : (0 : ℝ) ≤ -(mu * (x + hi) + c))]

theorem quad_ge_at_vertex {mu c x : ℝ} (hmu : 0 < mu) :
    mu * ((-c / (2 * mu)) * (-c / (2 * mu))) + c * (-c / (2 * mu)) ≤ mu * (x * x) + c * x := by
  have key : mu * (x * x) + c * x - (mu * ((-c / (2 * mu)) * (-c / (2 * mu))) + c * (-c / (2 * mu))) =
      mu * (x + c / (2 * mu)) ^ 2 := by
    field_simp; ring
  nlinarith [mul_nonneg hmu.le (sq_nonneg (x + c / (2 * mu)))]

/-- The checker's `quadMinI` is below `μx² + cx` on `[lo, hi]`. -/
theorem quadMinI_le {mu c lo hi : ℚ} (hmu : 0 < mu) {x : ℝ} (hx : (lo : ℝ) ≤ x) (hx' : x ≤ (hi : ℝ)) :
    ((quadMinI mu c lo hi : ℚ) : ℝ) ≤ (mu : ℝ) * (x * x) + (c : ℝ) * x := by
  have hmuR : (0 : ℝ) < mu := by exact_mod_cast hmu
  unfold quadMinI quadV
  split_ifs with h1 h2
  · have h1' : (-(c : ℝ)) / (2 * (mu : ℝ)) < lo := by exact_mod_cast h1
    push_cast
    exact quad_ge_at_left hmuR h1' hx
  · have h2' : (hi : ℝ) < (-(c : ℝ)) / (2 * (mu : ℝ)) := by exact_mod_cast h2
    push_cast
    exact quad_ge_at_right hmuR h2' hx'
  · push_cast
    exact quad_ge_at_vertex hmuR

/-- The checker's `quadMinLeft` is below `μx² + cx` on `(−∞, a]`. -/
theorem quadMinLeft_le {mu c a : ℚ} (hmu : 0 < mu) {x : ℝ} (hx : x ≤ (a : ℝ)) :
    ((quadMinLeft mu c a : ℚ) : ℝ) ≤ (mu : ℝ) * (x * x) + (c : ℝ) * x := by
  have hmuR : (0 : ℝ) < mu := by exact_mod_cast hmu
  unfold quadMinLeft quadV
  split_ifs with h1
  · have h1' : (a : ℝ) < (-(c : ℝ)) / (2 * (mu : ℝ)) := by exact_mod_cast h1
    push_cast
    exact quad_ge_at_right hmuR h1' hx
  · push_cast
    exact quad_ge_at_vertex hmuR

/-- The checker's `quadMinRight` is below `μx² + cx` on `[a, ∞)`. -/
theorem quadMinRight_le {mu c a : ℚ} (hmu : 0 < mu) {x : ℝ} (hx : (a : ℝ) ≤ x) :
    ((quadMinRight mu c a : ℚ) : ℝ) ≤ (mu : ℝ) * (x * x) + (c : ℝ) * x := by
  have hmuR : (0 : ℝ) < mu := by exact_mod_cast hmu
  unfold quadMinRight quadV
  split_ifs with h1
  · have h1' : (-(c : ℝ)) / (2 * (mu : ℝ)) < a := by exact_mod_cast h1
    push_cast
    exact quad_ge_at_left hmuR h1' hx
  · push_cast
    exact quad_ge_at_vertex hmuR

/-! ### The Fourier tail (`u = M q(1 − q) ≥ 25`) -/

/-- The Gaussian curvature is bounded below: `G_u(d) ≥ −a₀/u^{3/2}`. -/
theorem gaussCurv_ge {u d : ℝ} (hu : 0 < u) :
    -(LargeMean.gaussA0 / u ^ ((3 : ℝ) / 2)) ≤ gaussCurv u d := by
  have hw := LargeMean.neg_one_le_mul_exp_half (1 - d ^ 2 / u)
  have hexp : Real.exp (-(d ^ 2) / (2 * u)) = Real.exp ((1 - d ^ 2 / u) / 2) * Real.exp (-(1 / 2)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hden : 0 < Real.sqrt (2 * Real.pi) * u ^ ((3 : ℝ) / 2) := by positivity
  have hA : LargeMean.gaussA0 = Real.exp (-(1 / 2)) / Real.sqrt (2 * Real.pi) := rfl
  unfold gaussCurv
  rw [hexp, hA, le_div_iff₀ hden]
  have he := Real.exp_pos (-(1 / 2))
  have hu32 : 0 < u ^ ((3 : ℝ) / 2) := by positivity
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have e : -(Real.exp (-(1 / 2)) / Real.sqrt (2 * Real.pi) / u ^ ((3 : ℝ) / 2)) *
      (Real.sqrt (2 * Real.pi) * u ^ ((3 : ℝ) / 2)) = -Real.exp (-(1 / 2)) := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right hw he.le]

/-- **The Fourier kernel bound** (lane F1's `fC_sub_gaussCurv_le`, used only for `u ≥ 25`):
`κ_q(M, j) ≥ −(1/(20u) + 1/u²)` for `u = M q(1 − q) ≥ 25`. -/
theorem kappa_ge_fourier {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {M : ℕ}
    (hu25 : 25 ≤ (M : ℝ) * (q * (1 - q))) (j : ℤ) :
    -(1 / (20 * ((M : ℝ) * (q * (1 - q)))) + 1 / (((M : ℝ) * (q * (1 - q))) * ((M : ℝ) * (q * (1 - q))))) ≤
      kappa q M j := by
  set u := (M : ℝ) * (q * (1 - q)) with hu
  have hu0 : 0 < u := by linarith
  have hk := LargeMean.kappa_eq hq0 hq1 M j
  have hb := NoValley.binom_nonneg (M := M) hq0.le hq1.le j
  have hv : 0 < q * (1 - q) := by nlinarith
  have hextra : 0 ≤ (1 - 2 * q) ^ 2 / (q * (1 - q)) * binom M q j := by positivity
  have hF := fC_sub_gaussCurv_le M q hq0 hq1 j hu25
  rw [← hu] at hF
  have hG := gaussCurv_ge (d := (j : ℝ) - q * M) hu0
  have hA := LargeMean.gaussA0_lt
  have hA0 := LargeMean.gaussA0_pos
  have hsq : 5 ≤ Real.sqrt u := by
    rw [show (5 : ℝ) = Real.sqrt 25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu25
  have h32 : u ^ ((3 : ℝ) / 2) = u * Real.sqrt u := LargeMean.rpow_three_halves_eq hu0
  have h52 : u ^ ((5 : ℝ) / 2) = u ^ 2 * Real.sqrt u := LargeMean.rpow_five_halves_eq hu0
  rw [h32] at hG
  rw [h52] at hF
  have hq2 : |1 - 2 * q| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  -- the three error terms
  have t1 : LargeMean.gaussA0 / (u * Real.sqrt u) ≤ 1 / (20 * u) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hu0.le]
  have t2 : 2 / 3 * |1 - 2 * q| / u ^ 2 ≤ (2 / 3) / (u * u) := by
    rw [sq]
    gcongr
    linarith
  have t3 : 1 / (u ^ 2 * Real.sqrt u) ≤ (1 / 5) / (u * u) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ u * u)]
  have t4 : (2 / 3) / (u * u) + (1 / 5) / (u * u) ≤ 1 / (u * u) := by
    rw [← add_div]; gcongr; norm_num
  have hf := neg_abs_le ((2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) -
    gaussCurv u ((j : ℝ) - q * M))
  rw [hk]
  linarith

/-! ### The rational upper bound of `e^{−x}` -/

theorem expPartial_go (x : ℚ) : ∀ (k i : ℕ) (acc : ℚ),
    (expPartial.go x k i (x ^ i / (i.factorial : ℚ)) acc).2 =
      acc + ∑ l ∈ Finset.Ico i (i + k), x ^ l / (l.factorial : ℚ) := by
  intro k
  induction k with
  | zero => intro i acc; simp [expPartial.go]
  | succ k ih =>
    intro i acc
    have hstep : x ^ i / (i.factorial : ℚ) * x / ((i : ℚ) + 1) = x ^ (i + 1) / ((i + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      have : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      field_simp
      ring
    rw [expPartial.go, hstep, ih (i + 1)]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i < i + (k + 1))]
    rw [show i + 1 + k = i + (k + 1) by omega]
    ring

theorem expPartial_eq (x : ℚ) (n : ℕ) : expPartial x n = ∑ l ∈ Finset.range n, x ^ l / (l.factorial : ℚ) := by
  unfold expPartial
  have := expPartial_go x n 0 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add] at this
  rw [this, Finset.range_eq_Ico]

/-- `e^{−x} ≤ 1/∑_{i < 120} x^i/i!` for rational `x ≥ 0`. -/
theorem exp_neg_le_expNegUpper {x : ℚ} (hx : 0 ≤ x) : Real.exp (-(x : ℝ)) ≤ ((expNegUpper x : ℚ) : ℝ) := by
  have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hS : ((expPartial x 120 : ℚ) : ℝ) = ∑ l ∈ Finset.range 120, (x : ℝ) ^ l / (l.factorial : ℝ) := by
    rw [expPartial_eq]; push_cast; rfl
  have hle := Real.sum_le_exp_of_nonneg hxR 120
  have hpos : (1 : ℝ) ≤ ∑ l ∈ Finset.range 120, (x : ℝ) ^ l / (l.factorial : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have : 0 ≤ ∑ l ∈ Finset.range 119, (x : ℝ) ^ (l + 1) / ((l + 1).factorial : ℝ) :=
      Finset.sum_nonneg fun l _ => by positivity
    linarith
  unfold expNegUpper
  push_cast
  rw [hS, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by linarith) hle

end Erdos993Lean.Analytic.Atlas
