import Erdos993Lean.Analytic.LargeMean.Envelope

/-!
# The numerical constants of the large-mean theorem

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F2.
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md`, §3, §5, §6, and the rational
checks of `check_large_mean_400.py`; all comparisons here use only Mathlib's
`π > 3`, `π < 3.15`, `2.7182818283 < e < 2.7182818286` and `e^x ≥ 1 + x (+ x²/2)`.

* `gaussA0_lt`, `gaussA0_gt`: `6/25 < a₀ < 1/4` (the source uses `1/5 < a₀`; the sharper lower
  bound pays for the cruder `f_C ≥ −2` used on `M < m/3`).
* `exp_forty_thirds_gt`: `e^{40/3} > 500000`; `sq_mul_exp_neg_le`: `m² e^{−m/30} ≤ 8/25` for
  `m ≥ 400`; `tail_term_le`: `2 e^{−m/30} ρ³ ≤ 1/250` when `ρ² ≤ m/4`, `m ≥ 400` (the tail term
  of (B), with `ρ³ = s^{3/2}`).
* `phi_const`: `e^{−3/2}/(2√π) > 1/16` (source §6).
* `central_margin`, `outer_margin`: the final rational comparisons of the central case (cost
  `< 7/25`-type margin; source §5) and of the outer case (source §6), in normalized form
  (multiplied by `s^{3/2} = ρ³`).
-/

namespace Erdos993Lean.Analytic.LargeMean

theorem gaussA0_sq : gaussA0 ^ 2 = 1 / (2 * Real.pi * Real.exp 1) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : Real.exp (-(1 / 2)) ^ 2 = (Real.exp 1)⁻¹ := by
    rw [sq, ← Real.exp_add, ← Real.exp_neg]; norm_num
  unfold gaussA0
  rw [div_pow, Real.sq_sqrt hpi.le, h1]
  have := Real.exp_pos 1
  field_simp

/-- `a₀ < 1/4`. -/
theorem gaussA0_lt : gaussA0 < 1 / 4 := by
  have h := gaussA0_sq
  have hpos := gaussA0_pos
  have he := Real.exp_one_gt_d9
  have hpi := Real.pi_gt_three
  have h16 : 16 < 2 * Real.pi * Real.exp 1 := by nlinarith
  have hsq : gaussA0 ^ 2 < 1 / 16 := by
    rw [h, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  nlinarith

/-- `a₀ > 6/25`. -/
theorem gaussA0_gt : 6 / 25 < gaussA0 := by
  have h := gaussA0_sq
  have hpos := gaussA0_pos
  have he := Real.exp_one_lt_d9
  have hpi := Real.pi_lt_d2
  have he0 := Real.exp_pos 1
  have hpi0 := Real.pi_pos
  have hlt : 2 * Real.pi * Real.exp 1 < 625 / 36 := by nlinarith
  have hsq : 36 / 625 < gaussA0 ^ 2 := by
    rw [h, div_lt_div_iff₀ (by norm_num) (by positivity)]; linarith
  nlinarith

theorem exp_forty_thirds_gt : (500000 : ℝ) < Real.exp (40 / 3) := by
  have h1 : Real.exp (40 / 3) = Real.exp 1 ^ 13 * Real.exp (1 / 3) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 : (2.7182818283 : ℝ) ^ 13 ≤ Real.exp 1 ^ 13 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 13
  have h3 : (4 / 3 : ℝ) ≤ Real.exp (1 / 3) := by
    have := Real.add_one_le_exp (1 / 3 : ℝ); linarith
  rw [h1]
  calc (500000 : ℝ) < 2.7182818283 ^ 13 * (4 / 3) := by norm_num
    _ ≤ Real.exp 1 ^ 13 * Real.exp (1 / 3) := mul_le_mul h2 h3 (by norm_num) (by positivity)

/-- `m² e^{−m/30} ≤ 8/25` for `m ≥ 400`. -/
theorem sq_mul_exp_neg_le {m : ℝ} (hm : 400 ≤ m) : m ^ 2 * Real.exp (-(m / 30)) ≤ 8 / 25 := by
  have hy0 : 0 ≤ (m - 400) / 30 := by linarith
  have h1 : Real.exp (m / 30) = Real.exp (40 / 3) * Real.exp ((m - 400) / 30) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.quadratic_le_exp_of_nonneg hy0
  have h3 := exp_forty_thirds_gt
  have h4 : 500000 * (1 + (m - 400) / 30 + ((m - 400) / 30) ^ 2 / 2) ≤ Real.exp (m / 30) := by
    rw [h1]
    exact mul_le_mul h3.le h2 (by nlinarith [sq_nonneg ((m - 400) / 30)]) (by positivity)
  have h5 : m ^ 2 ≤ 8 / 25 * Real.exp (m / 30) := by nlinarith
  have h6 : Real.exp (-(m / 30)) * Real.exp (m / 30) = 1 := by
    rw [← Real.exp_add]; simp
  have h7 := Real.exp_pos (-(m / 30))
  nlinarith [mul_le_mul_of_nonneg_left h5 h7.le]

/-- The tail term of (B): `2 e^{−m/30} ρ³ ≤ 1/250` for `m ≥ 400` and `ρ² ≤ m/4`. -/
theorem tail_term_le {m ρ : ℝ} (hm : 400 ≤ m) (hρ : 0 < ρ) (hρm : ρ ^ 2 ≤ m / 4) :
    2 * Real.exp (-(m / 30)) * ρ ^ 3 ≤ 1 / 250 := by
  have hρ40 : ρ ≤ m / 40 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ m - 400) (by linarith : (0:ℝ) ≤ m),
      (by linarith : (0:ℝ) < ρ + m / 40)]
  have hρ3 : ρ ^ 3 ≤ m ^ 2 / 160 := by
    have e : ρ ^ 3 = ρ ^ 2 * ρ := by ring
    rw [e]
    calc ρ ^ 2 * ρ ≤ m / 4 * (m / 40) := mul_le_mul hρm hρ40 hρ.le (by linarith)
      _ = m ^ 2 / 160 := by ring
  have h1 := sq_mul_exp_neg_le hm
  have h2 := Real.exp_pos (-(m / 30))
  nlinarith [mul_le_mul_of_nonneg_left hρ3 h2.le]

/-- `e^{−3/2}/(2√π) > 1/16` (source §6: `e^{3/2} < 9/2`, `√π < 16/9`). -/
theorem phi_const : 1 / 16 < Real.exp (-(3 / 2)) / (2 * Real.sqrt Real.pi) := by
  have he3 : Real.exp (3 / 2) < 9 / 2 := by
    have h : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    nlinarith [Real.exp_pos (3 / 2)]
  have hsp : Real.sqrt Real.pi < 16 / 9 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith [Real.pi_lt_d2]
  have hsp0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hneg : 2 / 9 < Real.exp (-(3 / 2)) := by
    have h1 : Real.exp (-(3 / 2)) * Real.exp (3 / 2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(3 / 2)), Real.exp_pos (3 / 2)]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- The central-case comparison (source §5), normalized by `s^{3/2} = ρ³`: with `a = a₀`,
`ε = D/m`, `A = |1 − 2q|` and `E = 2e^{−m/30}ρ³`,
`a(1 − θ − 20ε) − (2/3)A(1 + 15ε)/ρ − (1 + 30ε)/ρ² − E > 0`. -/
theorem central_margin {a θ ε ρ A E : ℝ} (ha : 6 / 25 ≤ a) (hθ : θ ≤ 7 / 10) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 250) (hρ : 8 ≤ ρ) (hρ2 : 75 ≤ ρ ^ 2) (hA : A ≤ 1 / 4)
    (hE : E ≤ 1 / 250) :
    0 < a * (1 - θ - 20 * ε) - 2 / 3 * A * (1 + 15 * ε) / ρ - (1 + 30 * ε) / ρ ^ 2 - E := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : 6 / 25 * (11 / 50) ≤ a * (1 - θ - 20 * ε) :=
    mul_le_mul ha (by linarith) (by norm_num) (by linarith)
  have h2 : 2 / 3 * A * (1 + 15 * ε) / ρ ≤ 2 / 3 * (1 / 4) * (53 / 50) / 8 := by
    rw [div_le_div_iff₀ hρ0 (by norm_num)]
    have h2a : 2 / 3 * A * (1 + 15 * ε) ≤ 2 / 3 * (1 / 4) * (53 / 50) := by
      have := mul_le_mul hA (by linarith : 1 + 15 * ε ≤ 53 / 50) (by linarith) (by norm_num)
      nlinarith
    nlinarith
  have h3 : (1 + 30 * ε) / ρ ^ 2 ≤ 28 / 25 / 75 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The outer-case comparison (source §6), normalized by `ρ³`: the curvature deficit is beaten by
the binomial drift term `(9/1600) ρ² (1 − 4ε − 2θ/3)`. -/
theorem outer_margin {a θ ε ρ A E : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hθ : θ ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 250) (hρ : 8 ≤ ρ) (hρ2 : 75 ≤ ρ ^ 2)
    (hA : A ≤ 1 / 2) (hE : E ≤ 1 / 250) :
    0 < a * (1 - θ - 20 * ε) - 2 / 3 * A * (1 + 15 * ε) / ρ - (1 + 30 * ε) / ρ ^ 2 - E
      + 9 / 1600 * ρ ^ 2 * (1 - 4 * ε - 2 * θ / 3) := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : -(1 / 4) * (20 * (1 / 250)) ≤ a * (1 - θ - 20 * ε) := by
    nlinarith [mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - θ),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - a) hε0]
  have h2 : 2 / 3 * A * (1 + 15 * ε) / ρ ≤ 2 / 3 * (1 / 2) * (53 / 50) / 8 := by
    rw [div_le_div_iff₀ hρ0 (by norm_num)]
    have h2a : 2 / 3 * A * (1 + 15 * ε) ≤ 2 / 3 * (1 / 2) * (53 / 50) := by
      have := mul_le_mul hA (by linarith : 1 + 15 * ε ≤ 53 / 50) (by linarith) (by norm_num)
      nlinarith
    nlinarith
  have h3 : (1 + 30 * ε) / ρ ^ 2 ≤ 28 / 25 / 75 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : 9 / 1600 * (75 * (119 / 375)) ≤ 9 / 1600 * ρ ^ 2 * (1 - 4 * ε - 2 * θ / 3) := by
    have h4a : 119 / 375 ≤ 1 - 4 * ε - 2 * θ / 3 := by linarith
    have := mul_le_mul hρ2 h4a (by norm_num) (by positivity)
    nlinarith
  linarith

end Erdos993Lean.Analytic.LargeMean
