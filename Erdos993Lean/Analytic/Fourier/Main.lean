import Erdos993Lean.Analytic.Fourier.Circle
import Erdos993Lean.Analytic.Fourier.Majorant
import Erdos993Lean.Analytic.Fourier.Numerics

/-!
# The binomial Fourier estimates (lane F1): the two statements consumed by lane F2

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F1; interface `Analytic/Defs.lean`.
Source: `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` §2 (the two estimates for `u = Mv ≥ 25`); lane order
`LEAN/lanes/F1/PROMPT.md`.

For `q ∈ (0, 1)`, `v = q(1 − q)`, `M ∈ ℕ` with `u = Mv ≥ 25`, every integer `j` and `d = j − qM`:

* `binom_sub_gaussPhi_le`: `|b_M(j) − φ_u(d)| ≤ |1 − 2q|/(6u) + 1/(4u^{3/2})`;
* `fC_sub_gaussCurv_le`: `|f_C − G_u(d)| ≤ (2/3)|1 − 2q|/u² + 1/u^{5/2}`, where
  `f_C = 2b_M(j) − b_M(j − 1) − b_M(j + 1)`.

Proof: circle inversion (`Fourier/Circle.lean`) and Gaussian inversion (`Fourier/Gauss.lean`)
write `2π(b_M(j) − φ_u(d))` as `∫_ℝ (1_{(−π, π]} χ^M − e^{−ut²/2}) e^{−itd} dt`; the pointwise
majorant of `Fourier/Majorant.lean`, its exact integral and the comparisons of
`Fourier/Numerics.lean` give the bound.  The curvature is identical with the multipliers
`2 − 2 cos t` (circle) and `t²` (Gaussian).

Scalarity: the only data are one binomial atom `(M, j)` and `q`; `u = Mq(1 − q)` is the variance
of the conditional binomial count, produced here and consumed by lane F2 (the Gaussian envelope
(G) and the cost bound (B) of the source, §3–§6).  The coefficients `1/6, 1/4, 2/3, 1` are outputs
of this lane, consumed by F2's cost bound (B) and drift bound (§6).
-/

namespace Erdos993Lean.Analytic

open MeasureTheory Set

namespace Fourier

lemma norm_cexp_neg_ofReal_mul_I (x : ℝ) : ‖Complex.exp (-((x : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [show -((x : ℂ)) * Complex.I = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_two_pi_inv : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_inv,
    Complex.norm_of_nonneg (by positivity)]

/-- `u = Mq(1 − q) ≥ 25` forces `M ≥ 100` (as `q(1 − q) ≤ 1/4`) and `√u ≥ 5`. -/
lemma setup_bounds {M : ℕ} {q : ℝ} (hu : 25 ≤ (M : ℝ) * (q * (1 - q))) :
    100 ≤ M ∧ 5 ≤ √((M : ℝ) * (q * (1 - q))) := by
  constructor
  · have hv : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
    have : (100 : ℝ) ≤ M := by
      nlinarith [mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) (sub_nonneg.2 hv)]
    exact_mod_cast this
  · rw [show (5 : ℝ) = √25 by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu

lemma continuous_chi (q : ℝ) : Continuous (chi q) := by
  unfold chi; fun_prop

lemma integrable_indicator_Ioc_pi_of_continuous {F : ℝ → ℂ} (hF : Continuous F) :
    Integrable ((Ioc (-Real.pi) Real.pi).indicator F) :=
  ((hF.integrableOn_Icc).mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

/-- `(s²)^{k/2} = s^k` for `s ≥ 0`. -/
lemma sq_rpow_half {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    (s ^ 2) ^ ((k : ℝ) / 2) = s ^ k := by
  rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs, ← Real.rpow_natCast s k]
  congr 1; push_cast; ring

end Fourier

open Fourier

/-- **The binomial local limit estimate (mass).** For `q ∈ (0, 1)`, `u = M q(1 − q) ≥ 25` and every
integer `j`, with `d = j − qM`:
`|b_M(j) − φ_u(d)| ≤ |1 − 2q|/(6u) + 1/(4u^{3/2})`. -/
theorem binom_sub_gaussPhi_le (M : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (j : ℤ)
    (hu : 25 ≤ (M : ℝ) * (q * (1 - q))) :
    |binom M q j - gaussPhi (M * (q * (1 - q))) (j - q * M)| ≤
      |1 - 2 * q| / (6 * (M * (q * (1 - q)))) + 1 / (4 * (M * (q * (1 - q))) ^ ((3 : ℝ) / 2)) := by
  obtain ⟨hM, hs5⟩ := setup_bounds hu
  obtain ⟨s, hs⟩ : ∃ s, s = √((M : ℝ) * (q * (1 - q))) := ⟨_, rfl⟩
  rw [← hs] at hs5
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < (M : ℝ) * (q * (1 - q)) := by linarith
  have hsu : s ^ 2 = (M : ℝ) * (q * (1 - q)) := by rw [hs]; exact Real.sq_sqrt hu0.le
  have hb := binom_eq_integral M q j
  have hphi := gaussPhi_eq_integral ((M : ℝ) * (q * (1 - q))) ((j : ℝ) - q * M) hu0
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← integral_indicator measurableSet_Ioc] at hb
  have hF := integrable_indicator_Ioc_pi_of_continuous (F := fun t : ℝ => chi q t ^ M *
      Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I))
    (by have := continuous_chi q; fun_prop)
  have hG := integrable_pow_mul_gauss_cexp 0 ((M : ℝ) * (q * (1 - q))) ((j : ℝ) - q * M) hu0
  simp only [pow_zero, one_mul] at hG
  have hdiff : ((binom M q j - gaussPhi (M * (q * (1 - q))) (j - q * M) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t, ((Ioc (-Real.pi) Real.pi).indicator (fun t => chi q t ^ M) t -
        ((Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)) *
          Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_sub, hb, hphi, ← mul_sub, ← integral_sub hF hG]
    congr 2
    ext t
    rw [Set.indicator_mul_left, sub_mul]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add, hsu]
    congr 1
    push_cast
    ring
  have hnorm : ‖∫ t, ((Ioc (-Real.pi) Real.pi).indicator (fun t => chi q t ^ M) t -
        ((Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)) *
          Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ t, massMaj q s t := by
    refine norm_integral_le_of_norm_le (integrable_massMaj q hs0)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_cexp_neg_ofReal_mul_I, mul_one]
    exact norm_mass_integrand_le hq0.le hq1.le hM hsu
  have h32 : ((M : ℝ) * (q * (1 - q))) ^ ((3 : ℝ) / 2) = s ^ 3 := by
    rw [← hsu]; exact_mod_cast sq_rpow_half hs0.le 3
  calc |binom M q j - gaussPhi (M * (q * (1 - q))) (j - q * M)|
      = ‖((binom M q j - gaussPhi (M * (q * (1 - q))) (j - q * M) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t, massMaj q s t := by
        rw [hdiff, norm_mul, norm_two_pi_inv]
        gcongr
    _ ≤ |1 - 2 * q| / (6 * s ^ 2) + 1 / (4 * s ^ 3) := by
        rw [integral_massMaj q hs0]; exact mass_numeric q hs5
    _ = _ := by rw [hsu, h32]

/-- **The binomial local limit estimate (curvature).** For `q ∈ (0, 1)`, `u = M q(1 − q) ≥ 25`
and every integer `j`, with `d = j − qM` and `f_C = 2b_M(j) − b_M(j − 1) − b_M(j + 1)`:
`|f_C − G_u(d)| ≤ (2/3)|1 − 2q|/u² + 1/u^{5/2}`. -/
theorem fC_sub_gaussCurv_le (M : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (j : ℤ)
    (hu : 25 ≤ (M : ℝ) * (q * (1 - q))) :
    |(2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) -
        gaussCurv (M * (q * (1 - q))) (j - q * M)| ≤
      (2 / 3) * |1 - 2 * q| / (M * (q * (1 - q))) ^ 2 +
        1 / (M * (q * (1 - q))) ^ ((5 : ℝ) / 2) := by
  obtain ⟨hM, hs5⟩ := setup_bounds hu
  obtain ⟨s, hs⟩ : ∃ s, s = √((M : ℝ) * (q * (1 - q))) := ⟨_, rfl⟩
  rw [← hs] at hs5
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < (M : ℝ) * (q * (1 - q)) := by linarith
  have hsu : s ^ 2 = (M : ℝ) * (q * (1 - q)) := by rw [hs]; exact Real.sq_sqrt hu0.le
  have hb := fC_eq_integral M q j
  have hphi := gaussCurv_eq_integral ((M : ℝ) * (q * (1 - q))) ((j : ℝ) - q * M) hu0
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← integral_indicator measurableSet_Ioc] at hb
  have hF := integrable_indicator_Ioc_pi_of_continuous (F := fun t : ℝ => chi q t ^ M *
      ((2 - 2 * Real.cos t : ℝ) : ℂ) *
      Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I))
    (by have := continuous_chi q; fun_prop)
  have hG := integrable_pow_mul_gauss_cexp 2 ((M : ℝ) * (q * (1 - q))) ((j : ℝ) - q * M) hu0
  have hdiff : (((2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) -
        gaussCurv (M * (q * (1 - q))) (j - q * M) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t, ((Ioc (-Real.pi) Real.pi).indicator
          (fun t => chi q t ^ M * ((2 - 2 * Real.cos t : ℝ) : ℂ)) t -
        ((t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)) *
          Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_sub, hb, hphi, ← mul_sub, ← integral_sub hF hG]
    congr 2
    ext t
    rw [Set.indicator_mul_left, sub_mul]
    congr 1
    rw [Complex.ofReal_mul (t ^ 2) (Real.exp (-(s ^ 2) * t ^ 2 / 2)), Complex.ofReal_exp,
      mul_assoc ((t ^ 2 : ℝ) : ℂ), ← Complex.exp_add, hsu]
    push_cast
    ring_nf
  have hnorm : ‖∫ t, ((Ioc (-Real.pi) Real.pi).indicator
          (fun t => chi q t ^ M * ((2 - 2 * Real.cos t : ℝ) : ℂ)) t -
        ((t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)) *
          Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ t, curvMaj q s t := by
    refine norm_integral_le_of_norm_le (integrable_curvMaj q hs0)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_cexp_neg_ofReal_mul_I, mul_one]
    exact norm_curv_integrand_le hq0.le hq1.le hM hsu
  have h52 : ((M : ℝ) * (q * (1 - q))) ^ ((5 : ℝ) / 2) = s ^ 5 := by
    rw [← hsu]; exact_mod_cast sq_rpow_half hs0.le 5
  calc |(2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) -
        gaussCurv (M * (q * (1 - q))) (j - q * M)|
      = ‖(((2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) -
          gaussCurv (M * (q * (1 - q))) (j - q * M) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t, curvMaj q s t := by
        rw [hdiff, norm_mul, norm_two_pi_inv]
        gcongr
    _ ≤ 2 / 3 * |1 - 2 * q| / (s ^ 2) ^ 2 + 1 / s ^ 5 := by
        rw [integral_curvMaj q hs0]; exact curv_numeric q hs5
    _ = _ := by rw [hsu, h52]

end Erdos993Lean.Analytic
