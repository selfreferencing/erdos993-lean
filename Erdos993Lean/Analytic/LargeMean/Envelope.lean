import Erdos993Lean.Analytic.LargeMean.Interface

/-!
# The Gaussian envelope inequality (E) and its curvature form (G)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F2.
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md`, §3.

* `envelope_ineq` — **(E)**: for `t ≥ 1/3` and `x ≥ 0`,
  `t^{−3/2} (1 − x/t) e^{(1 − x/t)/2} + x ≥ t − 20 (t − 1)²`.
* `gaussA0` — `a₀ = e^{−1/2}/√(2π)`.
* `gaussCurv_envelope` — **(G)**: for `ρ > 0`, `u ≥ ρ²/3` and every real `d`,
  `G_u(d) + (a₀/ρ⁵) d² ≥ (a₀/ρ³) [u/ρ² − 20 (u/ρ² − 1)²]`.  With `s = ρ² = q(1 − q)m`,
  `u = q(1 − q)M` and `d = δ` this is the source's (G) with `μ = a₀ s^{−5/2}`, which does not
  depend on `M`.

The proof of (E) differs from the source's implicit differentiation (same statement).  Put
`r = √t`, `z = x/t`, `w = 1 − z`, so the left side is `w e^{w/2}/r³ + r² z`.
* `w e^{w/2} ≥ −1` for every `w` (`neg_one_le_mul_exp_half`); this settles `t ≤ 9/16`,
  `t ≥ 4/3` and `z ≥ 7` by one-variable polynomial inequalities (`env_caseA`, `env_caseC`,
  `env_caseB`).
* `w e^{w/2} ≥ w + w²/8` for `w ≥ −6` (`quad_le_mul_exp_half`); on `9/16 ≤ t ≤ 4/3`, `z ≤ 7` the
  resulting quadratic in `w` is nonnegative because its discriminant condition
  `(1 − r⁵)² ≤ 10 r³ (r² − 1)²` holds on `3/4 ≤ r ≤ 7/6` (`env_caseD`): the quotient by
  `(r − 1)²` is a degree-8 polynomial with positive Bernstein coefficients on `[3/4, 7/6]`
  (`env_poly_pos`).
-/

namespace Erdos993Lean.Analytic.LargeMean

/-- `w e^{w/2} ≥ −1` for every real `w`. -/
theorem neg_one_le_mul_exp_half (w : ℝ) : -1 ≤ w * Real.exp (w / 2) := by
  rcases le_or_gt 0 w with hw | hw
  · have h := Real.exp_pos (w / 2)
    nlinarith [mul_nonneg hw h.le]
  · have h1 := Real.quadratic_le_exp_of_nonneg (x := -w / 2) (by linarith)
    have h2 : Real.exp (-w / 2) * Real.exp (w / 2) = 1 := by
      rw [← Real.exp_add, show -w / 2 + w / 2 = 0 by ring, Real.exp_zero]
    have h3 := Real.exp_pos (w / 2)
    have h4 : 0 ≤ Real.exp (-w / 2) + w := by nlinarith [sq_nonneg (w + 2)]
    have h5 := mul_nonneg h4 h3.le
    nlinarith

/-- The quadratic minorant `w e^{w/2} ≥ w + w²/8` for `w ≥ −6`. -/
theorem quad_le_mul_exp_half {w : ℝ} (hw : -6 ≤ w) : w + w ^ 2 / 8 ≤ w * Real.exp (w / 2) := by
  rcases le_or_gt 0 w with h0 | h0
  · have h1 := Real.add_one_le_exp (w / 2)
    nlinarith [mul_le_mul_of_nonneg_left h1 h0, sq_nonneg w]
  · have h1 := Real.add_one_le_exp (-w / 2)
    have h2 : Real.exp (-w / 2) * Real.exp (w / 2) = 1 := by
      rw [← Real.exp_add, show -w / 2 + w / 2 = 0 by ring, Real.exp_zero]
    have h3 := Real.exp_pos (w / 2)
    have h4 : Real.exp (w / 2) * (-w / 2 + 1) ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]
    have h6 : 0 < 1 - w / 2 := by linarith
    have h5 : Real.exp (w / 2) ≤ 1 + w / 8 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -w) (by linarith : (0:ℝ) ≤ 6 + w), h6]
    nlinarith [mul_le_mul_of_nonpos_left h5 h0.le]

/-- (E) for `1/3 ≤ t ≤ 9/16` (with `t = r²`): `r³ (20 (r² − 1)² − r²) ≥ 1`. -/
theorem env_caseA {r : ℝ} (hr : 0 < r) (h1 : 1 / 3 ≤ r ^ 2) (h2 : r ^ 2 ≤ 9 / 16) :
    1 ≤ (20 * (r ^ 2 - 1) ^ 2 - r ^ 2) * (r ^ 2 * r) := by
  rcases le_or_gt (r ^ 2) (2 / 5) with h3 | h3
  · have hr1 : 4 / 7 ≤ r := by nlinarith
    have hA : 4 / 21 ≤ r ^ 2 * r := by nlinarith
    have hB : 34 / 5 ≤ 20 * (r ^ 2 - 1) ^ 2 - r ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 / 5 - r ^ 2)
        (by linarith : (0:ℝ) ≤ 33 - 20 * r ^ 2)]
    nlinarith [mul_le_mul hB hA (by norm_num) (by linarith)]
  · rcases le_or_gt (r ^ 2) (1 / 2) with h4 | h4
    · have hr1 : 5 / 8 ≤ r := by nlinarith
      have hA : 1 / 4 ≤ r ^ 2 * r := by nlinarith
      have hB : 9 / 2 ≤ 20 * (r ^ 2 - 1) ^ 2 - r ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 2 - r ^ 2)
          (by linarith : (0:ℝ) ≤ 31 - 20 * r ^ 2)]
      nlinarith [mul_le_mul hB hA (by norm_num) (by linarith)]
    · have hr1 : 7 / 10 ≤ r := by nlinarith
      have hA : 7 / 20 ≤ r ^ 2 * r := by nlinarith
      have hB : 209 / 64 ≤ 20 * (r ^ 2 - 1) ^ 2 - r ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 9 / 16 - r ^ 2)
          (by linarith : (0:ℝ) ≤ 119 / 4 - 20 * r ^ 2)]
      nlinarith [mul_le_mul hB hA (by norm_num) (by linarith)]

/-- (E) for `t ≥ 1/2` and `x/t ≥ 7` (with `t = r²`): `r³ (6r² + 20 (r² − 1)²) ≥ 1`. -/
theorem env_caseB {r : ℝ} (hr : 0 < r) (h1 : 1 / 2 ≤ r ^ 2) :
    1 ≤ (6 * r ^ 2 + 20 * (r ^ 2 - 1) ^ 2) * (r ^ 2 * r) := by
  have hr1 : 7 / 10 ≤ r := by nlinarith
  have hA : 7 / 20 ≤ r ^ 2 * r := by nlinarith
  have hB : 3 ≤ 6 * r ^ 2 + 20 * (r ^ 2 - 1) ^ 2 := by nlinarith [sq_nonneg (r ^ 2 - 1)]
  nlinarith [mul_le_mul hB hA (by norm_num) (by linarith)]

/-- (E) for `t ≥ 4/3` (with `t = r²`): `r³ (20 (r² − 1)² − r²) ≥ 1`. -/
theorem env_caseC {r : ℝ} (hr : 0 < r) (h1 : 4 / 3 ≤ r ^ 2) :
    1 ≤ (20 * (r ^ 2 - 1) ^ 2 - r ^ 2) * (r ^ 2 * r) := by
  have hr1 : 1 ≤ r := by nlinarith
  have hA : 4 / 3 ≤ r ^ 2 * r := by nlinarith
  have hB : 8 / 9 ≤ 20 * (r ^ 2 - 1) ^ 2 - r ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r ^ 2 - 4 / 3)
      (by linarith : (0:ℝ) ≤ 20 * r ^ 2 - 43 / 3)]
  nlinarith [mul_le_mul hB hA (by norm_num) (by linarith)]

/-- The quotient `(10 r³ (r² − 1)² − (1 − r⁵)²)/(r − 1)²` is nonnegative on `[3/4, 7/6]`: it is a
positive combination of the Bernstein basis `(r − 3/4)^i (7/6 − r)^{8−i}`. -/
theorem env_poly_pos {r : ℝ} (h1 : 3 / 4 ≤ r) (h2 : r ≤ 7 / 6) :
    0 ≤ -r ^ 8 - 2 * r ^ 7 - 3 * r ^ 6 + 6 * r ^ 5 + 15 * r ^ 4 + 6 * r ^ 3 - 3 * r ^ 2 - 2 * r
      - 1 := by
  have ha : 0 ≤ r - 3 / 4 := by linarith
  have hb : 0 ≤ 7 / 6 - r := by linarith
  linarith [mul_nonneg (pow_nonneg ha 8) (pow_nonneg hb 0),
    mul_nonneg (pow_nonneg ha 7) (pow_nonneg hb 1), mul_nonneg (pow_nonneg ha 6) (pow_nonneg hb 2),
    mul_nonneg (pow_nonneg ha 5) (pow_nonneg hb 3), mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 4),
    mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 5), mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 6),
    mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 7), mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 8)]

/-- (E) on `3/4 ≤ r ≤ 7/6`, `w = 1 − x/t ≥ −6`: the quadratic `w + w²/8 − r⁵ w + 20 r³ (r² − 1)²`
in `w` is nonnegative. -/
theorem env_caseD {r w : ℝ} (h1 : 3 / 4 ≤ r) (h2 : r ≤ 7 / 6) :
    0 ≤ w + w ^ 2 / 8 - r ^ 5 * w + 20 * r ^ 3 * (r ^ 2 - 1) ^ 2 := by
  have hP := env_poly_pos h1 h2
  have hid : 10 * r ^ 3 * (r ^ 2 - 1) ^ 2 - (1 - r ^ 5) ^ 2 = (r - 1) ^ 2 *
      (-r ^ 8 - 2 * r ^ 7 - 3 * r ^ 6 + 6 * r ^ 5 + 15 * r ^ 4 + 6 * r ^ 3 - 3 * r ^ 2 - 2 * r
        - 1) := by ring
  have hQ : 0 ≤ 10 * r ^ 3 * (r ^ 2 - 1) ^ 2 - (1 - r ^ 5) ^ 2 := by
    rw [hid]; exact mul_nonneg (sq_nonneg _) hP
  nlinarith [sq_nonneg (w + 4 * (1 - r ^ 5))]

/-- **The Gaussian envelope inequality (E)** (source §3): for `t ≥ 1/3` and `x ≥ 0`,
`t^{−3/2} (1 − x/t) e^{(1 − x/t)/2} + x ≥ t − 20 (t − 1)²`. -/
theorem envelope_ineq {t x : ℝ} (ht : 1 / 3 ≤ t) (hx : 0 ≤ x) :
    t - 20 * (t - 1) ^ 2 ≤ (1 - x / t) * Real.exp ((1 - x / t) / 2) / (t * Real.sqrt t) + x := by
  have htpos : 0 < t := by linarith
  obtain ⟨r, hr0, rfl⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = t :=
    ⟨Real.sqrt t, Real.sqrt_pos.mpr htpos, Real.sq_sqrt htpos.le⟩
  rw [Real.sqrt_sq hr0.le]
  have hr2 : 0 < r ^ 2 := by positivity
  have hxz : x = r ^ 2 * (x / r ^ 2) := (mul_div_cancel₀ x hr2.ne').symm
  set z := x / r ^ 2 with hz
  have hz0 : 0 ≤ z := div_nonneg hx hr2.le
  set w := 1 - z with hw
  have hc : 0 < r ^ 2 * r := by positivity
  suffices key : (r ^ 2 - 20 * (r ^ 2 - 1) ^ 2 - r ^ 2 * z) * (r ^ 2 * r) ≤ w * Real.exp (w / 2) by
    have := (le_div_iff₀ hc).mpr key
    rw [hxz]
    linarith
  have g1 := neg_one_le_mul_exp_half w
  have hzr : 0 ≤ r ^ 2 * z * (r ^ 2 * r) := by positivity
  rcases le_or_gt (r ^ 2) (9 / 16) with hA | hA
  · have := env_caseA hr0 ht hA
    nlinarith
  rcases le_or_gt (4 / 3) (r ^ 2) with hC | hC
  · have := env_caseC hr0 hC
    nlinarith
  rcases le_or_gt 7 z with hB | hB
  · have := env_caseB hr0 (by linarith)
    have h7 : 7 * (r ^ 2 * (r ^ 2 * r)) ≤ z * (r ^ 2 * (r ^ 2 * r)) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    nlinarith
  · have hr1 : 3 / 4 ≤ r := by nlinarith
    have hr2' : r ≤ 7 / 6 := by nlinarith
    have g2 := quad_le_mul_exp_half (w := w) (by linarith)
    have hD := env_caseD (w := w) hr1 hr2'
    have hzw : z = 1 - w := by rw [hw]; ring
    rw [hzw]
    nlinarith

/-- `a₀ = e^{−1/2}/√(2π)` (the source's `a0`). -/
noncomputable def gaussA0 : ℝ := Real.exp (-(1 / 2)) / Real.sqrt (2 * Real.pi)

theorem gaussA0_pos : 0 < gaussA0 := by unfold gaussA0; positivity

theorem rpow_three_halves_eq {u : ℝ} (hu : 0 < u) : u ^ ((3 : ℝ) / 2) = u * Real.sqrt u := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_one,
    Real.sqrt_eq_rpow]

theorem rpow_five_halves_eq {u : ℝ} (hu : 0 < u) : u ^ ((5 : ℝ) / 2) = u ^ 2 * Real.sqrt u := by
  rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_two,
    Real.sqrt_eq_rpow]

/-- **The curvature envelope (G)** (source §3, with `s = ρ²`): for `ρ > 0`, `u ≥ ρ²/3` and every
real `d`, `G_u(d) + (a₀/ρ⁵) d² ≥ (a₀/ρ³) [u/ρ² − 20 (u/ρ² − 1)²]`.  The `d²`-multiplier `a₀/ρ⁵`
does not depend on `u`. -/
theorem gaussCurv_envelope {ρ u d : ℝ} (hρ : 0 < ρ) (hu : ρ ^ 2 / 3 ≤ u) :
    gaussA0 / ρ ^ 3 * (u / ρ ^ 2 - 20 * (u / ρ ^ 2 - 1) ^ 2) ≤
      gaussCurv u d + gaussA0 / ρ ^ 5 * d ^ 2 := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hupos : 0 < u := by linarith
  have hune : u ≠ 0 := hupos.ne'
  have hρne : ρ ≠ 0 := hρ.ne'
  have ht : 1 / 3 ≤ u / ρ ^ 2 := by rw [le_div_iff₀ hρ2]; linarith
  have hx : 0 ≤ d ^ 2 / ρ ^ 2 := by positivity
  have hE := envelope_ineq ht hx
  have hc : 0 ≤ gaussA0 / ρ ^ 3 := by have := gaussA0_pos; positivity
  have key := mul_le_mul_of_nonneg_left hE hc
  have hxt : d ^ 2 / ρ ^ 2 / (u / ρ ^ 2) = d ^ 2 / u := by field_simp
  have hsq : Real.sqrt (u / ρ ^ 2) = Real.sqrt u / ρ := by
    rw [Real.sqrt_div' u hρ2.le, Real.sqrt_sq hρ.le]
  have hexp : Real.exp ((1 - d ^ 2 / u) / 2) =
      Real.exp (1 / 2) * Real.exp (-(d ^ 2) / (2 * u)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hxt, hsq, hexp] at key
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hupos
  have hsune : Real.sqrt u ≠ 0 := hsu.ne'
  have he : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have hene : Real.exp (1 / 2) ≠ 0 := he.ne'
  have hpi : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hpine : Real.sqrt (2 * Real.pi) ≠ 0 := hpi.ne'
  have hA : gaussA0 = 1 / (Real.exp (1 / 2) * Real.sqrt (2 * Real.pi)) := by
    unfold gaussA0; rw [Real.exp_neg]; field_simp
  have e1 : gaussA0 / ρ ^ 3 * ((1 - d ^ 2 / u) * (Real.exp (1 / 2) * Real.exp (-(d ^ 2) / (2 * u))) /
      (u / ρ ^ 2 * (Real.sqrt u / ρ)) + d ^ 2 / ρ ^ 2) = gaussCurv u d + gaussA0 / ρ ^ 5 * d ^ 2 := by
    unfold gaussCurv
    rw [rpow_three_halves_eq hupos, hA]
    field_simp
  linarith [key, e1]

end Erdos993Lean.Analytic.LargeMean
