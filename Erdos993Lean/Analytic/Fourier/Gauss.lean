import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Gaussian integrals for the binomial Fourier estimates

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F1; interface `Analytic/Defs.lean`.
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` §2 (older, coarser version:
`SOUL/O4/LARGE_MEAN_PROOF.md` §1).

The Gaussian side of the binomial local limit estimates of lane F1:

* `gaussPhi u d = e^{−d²/(2u)} / √(2πu)` and
  `gaussCurv u d = (1 − d²/u) e^{−d²/(2u)} / (√(2π) u^{3/2})`, the density `φ_u` and its curvature
  `G_u = −φ_u''` (the definitions consumed by lane F2);
* the absolute Gaussian moments `∫ |t|^k e^{−β²t²} dt = Γ((k + 1)/2) / β^{k+1}`
  (`integral_abs_pow_mul_gauss`, from Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`) and their
  values for `k = 0, 2, 3, 4, 5, 6` (`moment_zero`, …, `moment_six`);
* Gaussian Fourier inversion: `φ_u(d) = (2π)⁻¹ ∫ e^{−ut²/2 − idt} dt` (`gaussPhi_eq_integral`, from
  Mathlib's `integral_cexp_quadratic`) and `G_u(d) = (2π)⁻¹ ∫ t² e^{−ut²/2 − idt} dt`
  (`gaussCurv_eq_integral`; the `t²` moment is reduced to the zeroth one by integrating two exact
  derivatives, `integral_eq_zero_of_hasDerivAt_of_integrable`).
-/

open Real MeasureTheory Set

namespace Erdos993Lean.Analytic

/-- The Gaussian density `φ_u(d) = e^{−d²/(2u)} / √(2πu)`. -/
noncomputable def gaussPhi (u d : ℝ) : ℝ :=
  Real.exp (-(d ^ 2) / (2 * u)) / Real.sqrt (2 * Real.pi * u)

/-- The Gaussian curvature `G_u(d) = −φ_u''(d) = (1 − d²/u) e^{−d²/(2u)} / (√(2π) u^{3/2})`. -/
noncomputable def gaussCurv (u d : ℝ) : ℝ :=
  (1 - d ^ 2 / u) * Real.exp (-(d ^ 2) / (2 * u)) / (Real.sqrt (2 * Real.pi) * u ^ ((3 : ℝ) / 2))

namespace Fourier

/-! ## Absolute Gaussian moments -/

lemma integrable_abs_pow_mul_gauss (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-b * t ^ 2)) := by
  have hk : (-1 : ℝ) < k := by have := k.cast_nonneg (α := ℝ); linarith
  refine (integrable_rpow_mul_exp_neg_mul_sq hb hk).norm.congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_pow, Real.abs_exp]

/-- **Absolute Gaussian moments**: `∫ |t|^k e^{−β²t²} dt = Γ((k + 1)/2) / β^{k+1}`. -/
lemma integral_abs_pow_mul_gauss (k : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, |t| ^ k * Real.exp (-(β ^ 2) * t ^ 2) =
      Real.Gamma (((k : ℝ) + 1) / 2) / β ^ (k + 1) := by
  have h1 := integral_comp_abs (f := fun x : ℝ => x ^ k * Real.exp (-(β ^ 2) * x ^ 2))
  simp only [sq_abs] at h1
  rw [h1]
  have h2 : ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-(β ^ 2) * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ (k : ℝ) * Real.exp (-(β ^ 2) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [Real.rpow_natCast, Real.rpow_two]
  have hk : (-1 : ℝ) < k := by have := k.cast_nonneg (α := ℝ); linarith
  rw [h2, _root_.integral_rpow_mul_exp_neg_mul_rpow two_pos hk (by positivity)]
  have h3 : (β ^ 2) ^ (-((k : ℝ) + 1) / 2) = (β ^ (k + 1))⁻¹ := by
    rw [← Real.rpow_natCast β 2, ← Real.rpow_mul hβ.le, ← Real.rpow_natCast β (k + 1),
      ← Real.rpow_neg hβ.le]
    congr 1; push_cast; ring
  rw [h3]
  field_simp

lemma Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

lemma Gamma_five_halves : Real.Gamma (5 / 2) = 3 * √π / 4 := by
  rw [show (5 : ℝ) / 2 = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Gamma_three_halves]
  ring

lemma Gamma_seven_halves : Real.Gamma (7 / 2) = 15 * √π / 8 := by
  rw [show (7 : ℝ) / 2 = 5 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Gamma_five_halves]
  ring

lemma Gamma_three : Real.Gamma 3 = 2 := by
  rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

lemma moment_zero {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, |t| ^ 0 * Real.exp (-(β ^ 2) * t ^ 2) = √π / β := by
  rw [integral_abs_pow_mul_gauss 0 hβ]; norm_num [Real.Gamma_one_half_eq]

lemma moment_two {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, |t| ^ 2 * Real.exp (-(β ^ 2) * t ^ 2) = √π / 2 / β ^ 3 := by
  rw [integral_abs_pow_mul_gauss 2 hβ]; norm_num [Gamma_three_halves]

lemma moment_three {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, |t| ^ 3 * Real.exp (-(β ^ 2) * t ^ 2) = 1 / β ^ 4 := by
  rw [integral_abs_pow_mul_gauss 3 hβ]
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  norm_num [h2]

lemma moment_four {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, |t| ^ 4 * Real.exp (-(β ^ 2) * t ^ 2) = 3 * √π / 4 / β ^ 5 := by
  rw [integral_abs_pow_mul_gauss 4 hβ]; norm_num [Gamma_five_halves]

lemma moment_five {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, |t| ^ 5 * Real.exp (-(β ^ 2) * t ^ 2) = 2 / β ^ 6 := by
  rw [integral_abs_pow_mul_gauss 5 hβ]; norm_num [Gamma_three]

lemma moment_six {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, |t| ^ 6 * Real.exp (-(β ^ 2) * t ^ 2) = 15 * √π / 8 / β ^ 7 := by
  rw [integral_abs_pow_mul_gauss 6 hβ]; norm_num [Gamma_seven_halves]

/-! ## The Fourier transform of the Gaussian -/

open Complex in
/-- The Fourier transform of the Gaussian: `∫ e^{−ut²/2 − idt} dt = √(2π/u) e^{−d²/(2u)}`. -/
lemma integral_gauss_cexp (u d : ℝ) (hu : 0 < u) :
    ∫ t : ℝ, Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I) =
      ((Real.sqrt (2 * π / u) * Real.exp (-(d ^ 2) / (2 * u)) : ℝ) : ℂ) := by
  have hb : (-((u : ℂ) / 2)).re < 0 := by
    rw [show (-((u : ℂ) / 2)) = ((-(u / 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    linarith
  have key := integral_cexp_quadratic hb (-((d : ℂ) * I)) 0
  have e1 : (fun t : ℝ => Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I)) =
      fun t : ℝ => Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 + (-((d : ℂ) * I)) * t + 0) := by
    ext t; congr 1; ring
  rw [e1, key]
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have e2 : (π : ℂ) / -(-((u : ℂ) / 2)) = ((2 * π / u : ℝ) : ℂ) := by
    push_cast; field_simp
  have e3 : (0 : ℂ) - (-((d : ℂ) * I)) ^ 2 / (4 * -((u : ℂ) / 2)) =
      ((-(d ^ 2) / (2 * u) : ℝ) : ℂ) := by
    rw [neg_sq, mul_pow, I_sq]
    push_cast
    field_simp
    ring
  rw [e2, e3, ← Complex.ofReal_exp,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, ← Complex.ofReal_mul]

lemma gaussPhi_eq (u d : ℝ) (hu : 0 < u) :
    gaussPhi u d = (2 * π)⁻¹ * (Real.sqrt (2 * π / u) * Real.exp (-(d ^ 2) / (2 * u))) := by
  have hπ : 0 < 2 * π := by positivity
  have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 hπ
  have h3 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  rw [gaussPhi, Real.sqrt_div hπ.le, Real.sqrt_mul hπ.le]
  calc Real.exp (-(d ^ 2) / (2 * u)) / (Real.sqrt (2 * π) * Real.sqrt u)
      = ((2 * π)⁻¹ * Real.sqrt (2 * π)) / Real.sqrt u * Real.exp (-(d ^ 2) / (2 * u)) := by
        rw [inv_mul_eq_div, Real.sqrt_div_self']
        field_simp
    _ = (2 * π)⁻¹ * (Real.sqrt (2 * π) / Real.sqrt u * Real.exp (-(d ^ 2) / (2 * u))) := by
        ring

open Complex in
/-- **Gaussian Fourier inversion (mass)**: `φ_u(d) = (2π)⁻¹ ∫ e^{−ut²/2 − idt} dt`. -/
lemma gaussPhi_eq_integral (u d : ℝ) (hu : 0 < u) :
    (gaussPhi u d : ℂ) = (2 * (π : ℂ))⁻¹ *
      ∫ t : ℝ, Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I) := by
  rw [integral_gauss_cexp u d hu, gaussPhi_eq u d hu]
  push_cast
  ring

open Complex in
lemma integrable_pow_mul_gauss_cexp (k : ℕ) (u d : ℝ) (hu : 0 < u) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ k * Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I)) := by
  refine (integrable_abs_pow_mul_gauss k (b := u / 2) (by positivity)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  apply le_of_eq
  congr 2
  simp [Complex.sub_re, Complex.mul_re, pow_two]

open Complex in
/-- The `t²` moment of the Fourier integrand:
`∫ t² e^{−ut²/2 − idt} dt = ((1 − d²/u)/u) ∫ e^{−ut²/2 − idt} dt`. -/
lemma integral_sq_mul_gauss_cexp (u d : ℝ) (hu : 0 < u) :
    ∫ t : ℝ, (t : ℂ) ^ 2 * Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I) =
      (((1 - d ^ 2 / u) / u : ℝ) : ℂ) *
        ∫ t : ℝ, Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I) := by
  set h : ℝ → ℂ := fun t => Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I)
    with hh_def
  have hint : ∀ k : ℕ, Integrable (fun t : ℝ => (t : ℂ) ^ k * h t) := fun k =>
    integrable_pow_mul_gauss_cexp k u d hu
  have hderiv : ∀ t : ℝ, HasDerivAt h ((-(u : ℂ) * t - d * I) * h t) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => -((u : ℂ) / 2) * z ^ 2 - (d : ℂ) * z * I)
        (-(u : ℂ) * t - d * I) (t : ℂ) := by
      have := ((hasDerivAt_pow 2 (t : ℂ)).const_mul (-((u : ℂ) / 2))).sub
        (((hasDerivAt_id (t : ℂ)).const_mul (d : ℂ)).mul_const I)
      convert this using 1
      push_cast; ring
    have h2 := h1.comp_ofReal.cexp
    convert h2 using 1
    rw [hh_def]; ring
  have i0 : Integrable (fun t : ℝ => h t) := by simpa using hint 0
  have i1 : Integrable (fun t : ℝ => (t : ℂ) * h t) := by simpa using hint 1
  have i2 : Integrable (fun t : ℝ => (t : ℂ) ^ 2 * h t) := hint 2
  have E1' : -(u : ℂ) * (∫ t : ℝ, (t : ℂ) * h t) - d * I * ∫ t : ℝ, h t = 0 := by
    have e : (fun t : ℝ => (-(u : ℂ) * t - d * I) * h t) =
        fun t : ℝ => -(u : ℂ) * ((t : ℂ) * h t) - ((d : ℂ) * I) * h t := by
      ext t; ring
    have hI1 : Integrable (fun t : ℝ => (-(u : ℂ) * t - d * I) * h t) := by
      rw [e]; exact (i1.const_mul _).sub (i0.const_mul _)
    have E1 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hI1 i0
    rw [e, integral_sub (i1.const_mul _) (i0.const_mul _), integral_const_mul,
      integral_const_mul] at E1
    exact E1
  have hderiv2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) * h t)
      (h t + (t : ℂ) * ((-(u : ℂ) * t - d * I) * h t)) t := by
    intro t
    have := (hasDerivAt_id t).ofReal_comp.mul (hderiv t)
    convert this using 1
    simp
  have E2' : (∫ t : ℝ, h t) - u * (∫ t : ℝ, (t : ℂ) ^ 2 * h t) -
      d * I * (∫ t : ℝ, (t : ℂ) * h t) = 0 := by
    have e : (fun t : ℝ => h t + (t : ℂ) * ((-(u : ℂ) * t - d * I) * h t)) =
        fun t : ℝ => (h t - (u : ℂ) * ((t : ℂ) ^ 2 * h t)) - ((d : ℂ) * I) * ((t : ℂ) * h t) := by
      ext t; ring
    have i02 : Integrable (fun t : ℝ => h t - (u : ℂ) * ((t : ℂ) ^ 2 * h t)) :=
      i0.sub (i2.const_mul _)
    have hI2 : Integrable (fun t : ℝ => h t + (t : ℂ) * ((-(u : ℂ) * t - d * I) * h t)) := by
      rw [e]; exact i02.sub (i1.const_mul _)
    have E2 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv2 hI2 i1
    rw [e, integral_sub i02 (i1.const_mul _),
      integral_sub i0 (i2.const_mul _), integral_const_mul, integral_const_mul] at E2
    exact E2
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have key : (u : ℂ) ^ 2 * (∫ t : ℝ, (t : ℂ) ^ 2 * h t) = (u - d ^ 2) * ∫ t : ℝ, h t := by
    linear_combination (-(u : ℂ)) * E2' + ((d : ℂ) * I) * E1' +
      ((d : ℂ) ^ 2 * ∫ t : ℝ, h t) * I_sq
  have : (∫ t : ℝ, (t : ℂ) ^ 2 * h t) = (u - d ^ 2) * (∫ t : ℝ, h t) / (u : ℂ) ^ 2 := by
    field_simp
    linear_combination key
  rw [this]
  push_cast
  field_simp

/-- `G_u(d) = ((1 − d²/u)/u) φ_u(d)`. -/
lemma gaussCurv_eq (u d : ℝ) (hu : 0 < u) :
    gaussCurv u d = (1 - d ^ 2 / u) / u * gaussPhi u d := by
  have h32 : u ^ ((3 : ℝ) / 2) = u * Real.sqrt u := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hπ : 0 < 2 * π := by positivity
  have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 hπ
  have h3 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  rw [gaussCurv, gaussPhi, h32, Real.sqrt_mul hπ.le]
  field_simp

open Complex in
/-- **Gaussian Fourier inversion (curvature)**: `G_u(d) = (2π)⁻¹ ∫ t² e^{−ut²/2 − idt} dt`. -/
lemma gaussCurv_eq_integral (u d : ℝ) (hu : 0 < u) :
    (gaussCurv u d : ℂ) = (2 * (π : ℂ))⁻¹ *
      ∫ t : ℝ, (t : ℂ) ^ 2 * Complex.exp (-((u : ℂ) / 2) * (t : ℂ) ^ 2 - (d : ℂ) * t * I) := by
  rw [integral_sq_mul_gauss_cexp u d hu, gaussCurv_eq u d hu, Complex.ofReal_mul,
    gaussPhi_eq_integral u d hu]
  ring

end Fourier

end Erdos993Lean.Analytic
