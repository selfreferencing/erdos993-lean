import Erdos993Lean.Analytic.Fourier.Gauss
import Erdos993Lean.Analytic.Fourier.CharFun
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Pointwise majorants of the Fourier errors and their integrals

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F1.
Source: `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` §2 (the integration step; lane order step 6).

Write `s = √u`, `u = Mq(1 − q)`, `M ≥ 100`.  On the real line the circle integrand is
`1_{(−π, π]}(t) χ(t)^M` and the Gaussian integrand is `e^{−s²t²/2}`.  Their difference is bounded
pointwise (`norm_mass_integrand_le`) by

  `massMaj q s t = s² (|1 − 2q|/6 · |t|³ + 5/96 · t⁴) e^{−(33s/50)² t²}
      + 1_{(−π, π]}(t) e^{−(43/96) s²} + e^{−s²/4} e^{−(s/2)² t²}`

(inner region `|t| ≤ 1`: `norm_chi_pow_sub_gauss_le`; outer circle `1 < |t| ≤ π`:
`norm_chi_pow_le_of_one_le`; Gaussian tail `|t| ≥ 1`: `e^{−s²t²/2} ≤ e^{−s²/4} e^{−(s/2)²t²}`).
The curvature integrands `1_{(−π, π]} χ^M (2 − 2 cos t)` and `t² e^{−s²t²/2}` are compared by
`curvMaj` (`norm_curv_integrand_le`), using `0 ≤ 2 − 2 cos t ≤ t²`, `|2 − 2 cos t − t²| ≤ (5/48) t⁴`
on `|t| ≤ 1` (from `Real.cos_bound`; the source has `t⁴/12`) and `2 − 2 cos t ≤ 4`.
`integral_massMaj` and `integral_curvMaj` evaluate the integrals of the majorants exactly through
the Gaussian moments of `Fourier/Gauss.lean`.
-/

namespace Erdos993Lean.Analytic.Fourier

open MeasureTheory Set

/-- The absolute Gaussian moment density `|t|^k e^{−β²t²}`. -/
noncomputable def gaussMom (k : ℕ) (β t : ℝ) : ℝ := |t| ^ k * Real.exp (-(β ^ 2) * t ^ 2)

lemma gaussMom_nonneg (k : ℕ) (β t : ℝ) : 0 ≤ gaussMom k β t := by
  unfold gaussMom; positivity

lemma integrable_gaussMom (k : ℕ) {β : ℝ} (hβ : 0 < β) : Integrable (gaussMom k β) :=
  integrable_abs_pow_mul_gauss k (b := β ^ 2) (by positivity)

lemma integrable_indicator_Ioc_pi (c : ℝ) :
    Integrable ((Ioc (-Real.pi) Real.pi).indicator (fun _ : ℝ => c)) :=
  ((continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self).integrable_indicator
    measurableSet_Ioc

lemma integral_indicator_Ioc_pi (c : ℝ) :
    ∫ t, (Ioc (-Real.pi) Real.pi).indicator (fun _ : ℝ => c) t = 2 * Real.pi * c := by
  rw [integral_indicator_const _ measurableSet_Ioc,
    Real.volume_real_Ioc_of_le (by linarith [Real.pi_pos]), smul_eq_mul]
  ring

/-- The pointwise majorant of the mass error `|1_{(−π,π]} χ^M − e^{−s²t²/2}|`, `s = √u`. -/
noncomputable def massMaj (q s t : ℝ) : ℝ :=
  s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 3 (33 / 50 * s) t + 5 / 96 * gaussMom 4 (33 / 50 * s) t) +
    (Ioc (-Real.pi) Real.pi).indicator (fun _ => Real.exp (-(43 / 96) * s ^ 2)) t +
    Real.exp (-(s ^ 2) / 4) * gaussMom 0 (s / 2) t

/-- The pointwise majorant of the curvature error
`|1_{(−π,π]} χ^M (2 − 2 cos t) − t² e^{−s²t²/2}|`. -/
noncomputable def curvMaj (q s t : ℝ) : ℝ :=
  s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 5 (33 / 50 * s) t + 5 / 96 * gaussMom 6 (33 / 50 * s) t) +
    5 / 48 * gaussMom 4 (33 / 50 * s) t +
    (Ioc (-Real.pi) Real.pi).indicator (fun _ => 4 * Real.exp (-(43 / 96) * s ^ 2)) t +
    Real.exp (-(s ^ 2) / 4) * gaussMom 2 (s / 2) t

lemma integrable_massMaj (q : ℝ) {s : ℝ} (hs : 0 < s) : Integrable (massMaj q s) := by
  have hb1 : 0 < 33 / 50 * s := by positivity
  have hb2 : 0 < s / 2 := by positivity
  exact ((((integrable_gaussMom 3 hb1).const_mul _).add
    ((integrable_gaussMom 4 hb1).const_mul _)).const_mul _ |>.add
    (integrable_indicator_Ioc_pi _)).add ((integrable_gaussMom 0 hb2).const_mul _)

lemma integrable_curvMaj (q : ℝ) {s : ℝ} (hs : 0 < s) : Integrable (curvMaj q s) := by
  have hb1 : 0 < 33 / 50 * s := by positivity
  have hb2 : 0 < s / 2 := by positivity
  exact (((((integrable_gaussMom 5 hb1).const_mul _).add
    ((integrable_gaussMom 6 hb1).const_mul _)).const_mul _ |>.add
    ((integrable_gaussMom 4 hb1).const_mul _)).add
    (integrable_indicator_Ioc_pi _)).add ((integrable_gaussMom 2 hb2).const_mul _)

/-- The integral of the mass majorant, in closed form. -/
lemma integral_massMaj (q : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ t, massMaj q s t =
      s ^ 2 * (|1 - 2 * q| / 6 * (1 / (33 / 50 * s) ^ 4) +
          5 / 96 * (3 * √Real.pi / 4 / (33 / 50 * s) ^ 5)) +
        2 * Real.pi * Real.exp (-(43 / 96) * s ^ 2) +
        Real.exp (-(s ^ 2) / 4) * (√Real.pi / (s / 2)) := by
  have hb1 : 0 < 33 / 50 * s := by positivity
  have hb2 : 0 < s / 2 := by positivity
  have i3 : Integrable (fun t => |1 - 2 * q| / 6 * gaussMom 3 (33 / 50 * s) t) :=
    (integrable_gaussMom 3 hb1).const_mul _
  have i4 : Integrable (fun t => 5 / 96 * gaussMom 4 (33 / 50 * s) t) :=
    (integrable_gaussMom 4 hb1).const_mul _
  have i1 : Integrable (fun t => s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 3 (33 / 50 * s) t +
      5 / 96 * gaussMom 4 (33 / 50 * s) t)) := (i3.add i4).const_mul _
  have i2 := integrable_indicator_Ioc_pi (Real.exp (-(43 / 96) * s ^ 2))
  have i12 : Integrable (fun t => s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 3 (33 / 50 * s) t +
      5 / 96 * gaussMom 4 (33 / 50 * s) t) +
      (Ioc (-Real.pi) Real.pi).indicator (fun _ => Real.exp (-(43 / 96) * s ^ 2)) t) := i1.add i2
  have i0 : Integrable (fun t => Real.exp (-(s ^ 2) / 4) * gaussMom 0 (s / 2) t) :=
    (integrable_gaussMom 0 hb2).const_mul _
  have m3 : ∫ t, gaussMom 3 (33 / 50 * s) t = 1 / (33 / 50 * s) ^ 4 := moment_three hb1
  have m4 : ∫ t, gaussMom 4 (33 / 50 * s) t = 3 * √Real.pi / 4 / (33 / 50 * s) ^ 5 :=
    moment_four hb1
  have m0 : ∫ t, gaussMom 0 (s / 2) t = √Real.pi / (s / 2) := moment_zero hb2
  unfold massMaj
  rw [integral_add i12 i0, integral_add i1 i2, integral_const_mul, integral_add i3 i4,
    integral_const_mul, integral_const_mul, integral_indicator_Ioc_pi, integral_const_mul,
    m3, m4, m0]

/-- The integral of the curvature majorant, in closed form. -/
lemma integral_curvMaj (q : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ t, curvMaj q s t =
      s ^ 2 * (|1 - 2 * q| / 6 * (2 / (33 / 50 * s) ^ 6) +
          5 / 96 * (15 * √Real.pi / 8 / (33 / 50 * s) ^ 7)) +
        5 / 48 * (3 * √Real.pi / 4 / (33 / 50 * s) ^ 5) +
        2 * Real.pi * (4 * Real.exp (-(43 / 96) * s ^ 2)) +
        Real.exp (-(s ^ 2) / 4) * (√Real.pi / 2 / (s / 2) ^ 3) := by
  have hb1 : 0 < 33 / 50 * s := by positivity
  have hb2 : 0 < s / 2 := by positivity
  have i5 : Integrable (fun t => |1 - 2 * q| / 6 * gaussMom 5 (33 / 50 * s) t) :=
    (integrable_gaussMom 5 hb1).const_mul _
  have i6 : Integrable (fun t => 5 / 96 * gaussMom 6 (33 / 50 * s) t) :=
    (integrable_gaussMom 6 hb1).const_mul _
  have i1 : Integrable (fun t => s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 5 (33 / 50 * s) t +
      5 / 96 * gaussMom 6 (33 / 50 * s) t)) := (i5.add i6).const_mul _
  have i4 : Integrable (fun t => 5 / 48 * gaussMom 4 (33 / 50 * s) t) :=
    (integrable_gaussMom 4 hb1).const_mul _
  have i14 : Integrable (fun t => s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 5 (33 / 50 * s) t +
      5 / 96 * gaussMom 6 (33 / 50 * s) t) + 5 / 48 * gaussMom 4 (33 / 50 * s) t) := i1.add i4
  have i2 := integrable_indicator_Ioc_pi (4 * Real.exp (-(43 / 96) * s ^ 2))
  have i142 : Integrable (fun t => s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 5 (33 / 50 * s) t +
      5 / 96 * gaussMom 6 (33 / 50 * s) t) + 5 / 48 * gaussMom 4 (33 / 50 * s) t +
      (Ioc (-Real.pi) Real.pi).indicator (fun _ => 4 * Real.exp (-(43 / 96) * s ^ 2)) t) :=
    i14.add i2
  have i0 : Integrable (fun t => Real.exp (-(s ^ 2) / 4) * gaussMom 2 (s / 2) t) :=
    (integrable_gaussMom 2 hb2).const_mul _
  have m5 : ∫ t, gaussMom 5 (33 / 50 * s) t = 2 / (33 / 50 * s) ^ 6 := moment_five hb1
  have m6 : ∫ t, gaussMom 6 (33 / 50 * s) t = 15 * √Real.pi / 8 / (33 / 50 * s) ^ 7 :=
    moment_six hb1
  have m4 : ∫ t, gaussMom 4 (33 / 50 * s) t = 3 * √Real.pi / 4 / (33 / 50 * s) ^ 5 :=
    moment_four hb1
  have m2 : ∫ t, gaussMom 2 (s / 2) t = √Real.pi / 2 / (s / 2) ^ 3 := moment_two hb2
  unfold curvMaj
  rw [integral_add i142 i0, integral_add i14 i2, integral_add i1 i4, integral_const_mul,
    integral_add i5 i6, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator_Ioc_pi, integral_const_mul, m5, m6, m4, m2]

/-- For `|t| ≥ 1`: `e^{−s²t²/2} ≤ e^{−s²/4} e^{−(s/2)²t²}`. -/
lemma exp_le_of_one_le_abs {s t : ℝ} (ht : 1 ≤ |t|) :
    Real.exp (-(s ^ 2) * t ^ 2 / 2) ≤ Real.exp (-(s ^ 2) / 4) * gaussMom 0 (s / 2) t := by
  unfold gaussMom
  rw [pow_zero, one_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have : 1 ≤ t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  nlinarith [sq_nonneg s]

lemma sq_mul_exp_le_of_one_le_abs {s t : ℝ} (ht : 1 ≤ |t|) :
    t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) ≤ Real.exp (-(s ^ 2) / 4) * gaussMom 2 (s / 2) t := by
  have h := exp_le_of_one_le_abs (s := s) ht
  unfold gaussMom at h ⊢
  rw [pow_zero, one_mul] at h
  rw [sq_abs]
  calc t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2)
      ≤ t ^ 2 * (Real.exp (-(s ^ 2) / 4) * Real.exp (-((s / 2) ^ 2) * t ^ 2)) := by gcongr
    _ = _ := by ring

lemma pi_mem_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) : t ∈ Ioc (-Real.pi) Real.pi := by
  rw [abs_le] at ht; constructor <;> linarith [Real.pi_gt_three]

/-- **Pointwise majorant, mass.** -/
lemma norm_mass_integrand_le {q s t : ℝ} {M : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hM : 100 ≤ M)
    (hsu : s ^ 2 = (M : ℝ) * (q * (1 - q))) :
    ‖(Ioc (-Real.pi) Real.pi).indicator (fun t => chi q t ^ M) t -
      ((Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤ massMaj q s t := by
  have hA : 0 ≤ s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 3 (33 / 50 * s) t +
      5 / 96 * gaussMom 4 (33 / 50 * s) t) := by
    have := gaussMom_nonneg 3 (33 / 50 * s) t
    have := gaussMom_nonneg 4 (33 / 50 * s) t
    positivity
  have hB : 0 ≤ (Ioc (-Real.pi) Real.pi).indicator
      (fun _ => Real.exp (-(43 / 96) * s ^ 2)) t :=
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t
  have hC : 0 ≤ Real.exp (-(s ^ 2) / 4) * gaussMom 0 (s / 2) t := by
    have := gaussMom_nonneg 0 (s / 2) t
    positivity
  have hgn : ‖((Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)‖ = Real.exp (-(s ^ 2) * t ^ 2 / 2) :=
    Complex.norm_of_nonneg (Real.exp_pos _).le
  unfold massMaj
  by_cases ht1 : |t| ≤ 1
  · rw [Set.indicator_of_mem (pi_mem_of_abs_le_one ht1)]
    have h := norm_chi_pow_sub_gauss_le hq0 hq1 ht1 hM
    rw [← hsu] at h
    have e : s ^ 2 * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) *
        Real.exp (-(1089 / 2500) * s ^ 2 * t ^ 2) =
        s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 3 (33 / 50 * s) t +
          5 / 96 * gaussMom 4 (33 / 50 * s) t) := by
      unfold gaussMom
      rw [show t ^ 4 = |t| ^ 4 by
          rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, show |t| ^ 4 = (|t| ^ 2) ^ 2 by ring, sq_abs],
        show -(1089 / 2500) * s ^ 2 * t ^ 2 = -((33 / 50 * s) ^ 2) * t ^ 2 by ring]
      ring
    rw [e] at h
    linarith
  · push_neg at ht1
    have hg := exp_le_of_one_le_abs (s := s) ht1.le
    by_cases hmem : t ∈ Ioc (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have habs : |t| ≤ Real.pi := abs_le.2 ⟨hmem.1.le, hmem.2⟩
      have h := norm_chi_pow_le_of_one_le M hq0 hq1 ht1.le habs
      rw [← hsu] at h
      calc _ ≤ ‖chi q t ^ M‖ + ‖((Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ _ := by rw [hgn]; linarith
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_sub, norm_neg, hgn]
      linarith

/-- **Pointwise majorant, curvature.** -/
lemma norm_curv_integrand_le {q s t : ℝ} {M : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hM : 100 ≤ M)
    (hsu : s ^ 2 = (M : ℝ) * (q * (1 - q))) :
    ‖(Ioc (-Real.pi) Real.pi).indicator
        (fun t => chi q t ^ M * ((2 - 2 * Real.cos t : ℝ) : ℂ)) t -
      ((t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤ curvMaj q s t := by
  have hA : 0 ≤ s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 5 (33 / 50 * s) t +
      5 / 96 * gaussMom 6 (33 / 50 * s) t) := by
    have := gaussMom_nonneg 5 (33 / 50 * s) t
    have := gaussMom_nonneg 6 (33 / 50 * s) t
    positivity
  have hD : 0 ≤ 5 / 48 * gaussMom 4 (33 / 50 * s) t := by
    have := gaussMom_nonneg 4 (33 / 50 * s) t
    positivity
  have hB : 0 ≤ (Ioc (-Real.pi) Real.pi).indicator
      (fun _ => 4 * Real.exp (-(43 / 96) * s ^ 2)) t :=
    Set.indicator_nonneg (fun _ _ => by positivity) t
  have hC : 0 ≤ Real.exp (-(s ^ 2) / 4) * gaussMom 2 (s / 2) t := by
    have := gaussMom_nonneg 2 (s / 2) t
    positivity
  have hc0 : 0 ≤ 2 - 2 * Real.cos t := by linarith [Real.cos_le_one t]
  have hc4 : 2 - 2 * Real.cos t ≤ 4 := by linarith [Real.neg_one_le_cos t]
  have hgn : ‖((t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)‖ =
      t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) :=
    Complex.norm_of_nonneg (by positivity)
  unfold curvMaj
  by_cases ht1 : |t| ≤ 1
  · rw [Set.indicator_of_mem (pi_mem_of_abs_le_one ht1)]
    have h := norm_chi_pow_sub_gauss_le hq0 hq1 ht1 hM
    rw [← hsu] at h
    obtain ⟨g, hg⟩ : ∃ g : ℂ, g = ((Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hdec : chi q t ^ M * ((2 - 2 * Real.cos t : ℝ) : ℂ) -
        ((t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ) =
        (chi q t ^ M - g) * ((2 - 2 * Real.cos t : ℝ) : ℂ) +
          g * ((2 - 2 * Real.cos t - t ^ 2 : ℝ) : ℂ) := by
      rw [hg]; push_cast; ring
    rw [← hg] at h
    rw [hdec]
    have hct : 2 - 2 * Real.cos t ≤ t ^ 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
    have hcb : |2 - 2 * Real.cos t - t ^ 2| ≤ 5 / 48 * |t| ^ 4 := by
      have := Real.cos_bound ht1
      rw [show 2 - 2 * Real.cos t - t ^ 2 = -2 * (Real.cos t - (1 - t ^ 2 / 2)) by ring,
        abs_mul]
      norm_num
      linarith
    have hgn' : ‖g‖ = Real.exp (-(s ^ 2) * t ^ 2 / 2) := by
      rw [hg]; exact Complex.norm_of_nonneg (Real.exp_pos _).le
    have hg' : Real.exp (-(s ^ 2) * t ^ 2 / 2) ≤ Real.exp (-((33 / 50 * s) ^ 2) * t ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg (s * t)])
    have hR : 0 ≤ s ^ 2 * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) *
        Real.exp (-(1089 / 2500) * s ^ 2 * t ^ 2) := by positivity
    have e : s ^ 2 * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) *
          Real.exp (-(1089 / 2500) * s ^ 2 * t ^ 2) * t ^ 2 +
        Real.exp (-((33 / 50 * s) ^ 2) * t ^ 2) * (5 / 48 * |t| ^ 4) =
        s ^ 2 * (|1 - 2 * q| / 6 * gaussMom 5 (33 / 50 * s) t +
          5 / 96 * gaussMom 6 (33 / 50 * s) t) + 5 / 48 * gaussMom 4 (33 / 50 * s) t := by
      unfold gaussMom
      have e2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, e2,
        show -(1089 / 2500) * s ^ 2 * |t| ^ 2 = -((33 / 50 * s) ^ 2) * |t| ^ 2 by ring]
      ring
    calc ‖(chi q t ^ M - g) * ((2 - 2 * Real.cos t : ℝ) : ℂ) +
          g * ((2 - 2 * Real.cos t - t ^ 2 : ℝ) : ℂ)‖
        ≤ ‖(chi q t ^ M - g) * ((2 - 2 * Real.cos t : ℝ) : ℂ)‖ +
          ‖g * ((2 - 2 * Real.cos t - t ^ 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖chi q t ^ M - g‖ * (2 - 2 * Real.cos t) +
          Real.exp (-(s ^ 2) * t ^ 2 / 2) * |2 - 2 * Real.cos t - t ^ 2| := by
          rw [norm_mul, norm_mul, Complex.norm_of_nonneg hc0, hgn', Complex.norm_real,
            Real.norm_eq_abs]
      _ ≤ s ^ 2 * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) *
            Real.exp (-(1089 / 2500) * s ^ 2 * t ^ 2) * t ^ 2 +
          Real.exp (-((33 / 50 * s) ^ 2) * t ^ 2) * (5 / 48 * |t| ^ 4) :=
          add_le_add (mul_le_mul h hct hc0 hR)
            (mul_le_mul hg' hcb (abs_nonneg _) (Real.exp_pos _).le)
      _ = _ := e
      _ ≤ _ := by linarith
  · push_neg at ht1
    have hg := sq_mul_exp_le_of_one_le_abs (s := s) ht1.le
    by_cases hmem : t ∈ Ioc (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have habs : |t| ≤ Real.pi := abs_le.2 ⟨hmem.1.le, hmem.2⟩
      have h := norm_chi_pow_le_of_one_le M hq0 hq1 ht1.le habs
      rw [← hsu] at h
      calc _ ≤ ‖chi q t ^ M * ((2 - 2 * Real.cos t : ℝ) : ℂ)‖ +
            ‖((t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ = ‖chi q t ^ M‖ * (2 - 2 * Real.cos t) + t ^ 2 * Real.exp (-(s ^ 2) * t ^ 2 / 2) := by
            rw [norm_mul, Complex.norm_of_nonneg hc0, hgn]
        _ ≤ Real.exp (-(43 / 96) * s ^ 2) * 4 + Real.exp (-(s ^ 2) / 4) * gaussMom 2 (s / 2) t :=
            add_le_add (mul_le_mul h hc4 hc0 (Real.exp_pos _).le) hg
        _ ≤ _ := by linarith
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_sub, norm_neg, hgn]
      linarith

end Erdos993Lean.Analytic.Fourier
