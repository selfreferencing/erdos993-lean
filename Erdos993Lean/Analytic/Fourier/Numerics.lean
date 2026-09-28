import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical comparisons for the binomial Fourier estimates

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F1.
Source: `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` §2 and its checker `check_large_mean_400.py` (the
comparisons below are the analogues for the constants of this lane; they are proved in Lean from
`π > 3.14` and `e > 2.7182818283`).

* `sqrt_pi_gt`: `1.77 < √π`;
* `exp_1075_96_gt`, `exp_25_4_gt`: `e^{1075/96} > 66000` and `e^{25/4} > 500` (using `e^x ≥ 1 + x`);
* `pow_mul_exp_neg_le`: `s^k e^{−cs²}` is nonincreasing on `s ≥ s₀` when `k ≤ 2cs₀²`
  (`exp_tail_43`, `exp_tail_quarter`: its values at `s₀ = 5`);
* `mass_numeric`, `curv_numeric`: the integrated majorants divided by `2π` are at most
  `|1 − 2q|/(6s²) + 1/(4s³)` and `(2/3)|1 − 2q|/s⁴ + 1/s⁵` for `s ≥ 5` (i.e. `u ≥ 25`).  The
  coefficients of `s^{-3}` and `s^{-5}` that are actually used are below `0.12` and `0.93`.
-/

namespace Erdos993Lean.Analytic.Fourier

/-- `1.77 < √π`, from `π > 3.14`. -/
lemma sqrt_pi_gt : (1.77 : ℝ) < √Real.pi := by
  rw [Real.lt_sqrt (by norm_num)]
  have := Real.pi_gt_d2
  norm_num at this ⊢
  linarith

/-- `e^{1075/96} > 66000`, from `e > 2.7182818283` and `e^{19/96} ≥ 1 + 19/96`. -/
lemma exp_1075_96_gt : (66000 : ℝ) < Real.exp (1075 / 96) := by
  have h1 : (2.7182818283 : ℝ) ^ 11 < Real.exp 1 ^ 11 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h3 : (1 + 19 / 96 : ℝ) ≤ Real.exp (19 / 96) := by
    linarith [Real.add_one_le_exp (19 / 96 : ℝ)]
  have h4 : Real.exp (1075 / 96) = Real.exp 1 ^ 11 * Real.exp (19 / 96) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [h4]
  calc (66000 : ℝ) < (2.7182818283 : ℝ) ^ 11 * (1 + 19 / 96) := by norm_num
    _ ≤ Real.exp 1 ^ 11 * Real.exp (19 / 96) :=
        mul_le_mul h1.le h3 (by norm_num) (by positivity)

/-- `e^{25/4} > 500`, from `e > 2.7182818283` and `e^{1/4} ≥ 5/4`. -/
lemma exp_25_4_gt : (500 : ℝ) < Real.exp (25 / 4) := by
  have h1 : (2.7182818283 : ℝ) ^ 6 < Real.exp 1 ^ 6 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h3 : (1 + 1 / 4 : ℝ) ≤ Real.exp (1 / 4) := by
    linarith [Real.add_one_le_exp (1 / 4 : ℝ)]
  have h4 : Real.exp (25 / 4) = Real.exp 1 ^ 6 * Real.exp (1 / 4) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [h4]
  calc (500 : ℝ) < (2.7182818283 : ℝ) ^ 6 * (1 + 1 / 4) := by norm_num
    _ ≤ Real.exp 1 ^ 6 * Real.exp (1 / 4) :=
        mul_le_mul h1.le h3 (by norm_num) (by positivity)

/-- `s^k e^{−cs²}` is nonincreasing on `s ≥ s₀` when `k ≤ 2cs₀²`. -/
lemma pow_mul_exp_neg_le {k : ℕ} {c s0 s : ℝ} (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hc : (k : ℝ) ≤ 2 * c * s0 ^ 2) :
    s ^ k * Real.exp (-c * s ^ 2) ≤ s0 ^ k * Real.exp (-c * s0 ^ 2) := by
  have hd : 0 ≤ s - s0 := by linarith
  have hc0 : 0 ≤ c := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : 0 ≤ 2 * c * s0 ^ 2 := le_trans hk hc
    have hs2 : 0 < 2 * s0 ^ 2 := by positivity
    nlinarith
  have h1 : s ≤ s0 * Real.exp ((s - s0) / s0) := by
    calc s = s0 * ((s - s0) / s0 + 1) := by field_simp; ring
      _ ≤ s0 * Real.exp ((s - s0) / s0) := by
          gcongr; exact Real.add_one_le_exp _
  have h2 : s ^ k ≤ s0 ^ k * Real.exp (k * ((s - s0) / s0)) := by
    calc s ^ k ≤ (s0 * Real.exp ((s - s0) / s0)) ^ k := by
          gcongr; linarith
      _ = s0 ^ k * Real.exp (k * ((s - s0) / s0)) := by rw [mul_pow, ← Real.exp_nat_mul]
  have h3 : (k : ℝ) * ((s - s0) / s0) ≤ c * (s ^ 2 - s0 ^ 2) := by
    have hk' : (k : ℝ) / s0 ≤ 2 * c * s0 := by
      rw [div_le_iff₀ hs0]; nlinarith
    calc (k : ℝ) * ((s - s0) / s0) = ((k : ℝ) / s0) * (s - s0) := by ring
      _ ≤ (2 * c * s0) * (s - s0) := by gcongr
      _ ≤ c * (s + s0) * (s - s0) := by
          apply mul_le_mul_of_nonneg_right _ hd; nlinarith
      _ = c * (s ^ 2 - s0 ^ 2) := by ring
  calc s ^ k * Real.exp (-c * s ^ 2)
      ≤ s0 ^ k * Real.exp (k * ((s - s0) / s0)) * Real.exp (-c * s ^ 2) := by gcongr
    _ ≤ s0 ^ k * Real.exp (c * (s ^ 2 - s0 ^ 2)) * Real.exp (-c * s ^ 2) := by gcongr
    _ = s0 ^ k * Real.exp (-c * s0 ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- `s^k e^{−(43/96)s²} ≤ 5^k/66000` for `k ≤ 5` and `s ≥ 5`. -/
lemma exp_tail_43 {k : ℕ} (hk : k ≤ 5) {s : ℝ} (hs : 5 ≤ s) :
    s ^ k * Real.exp (-(43 / 96) * s ^ 2) ≤ 5 ^ k / 66000 := by
  have h := pow_mul_exp_neg_le (k := k) (c := 43 / 96) (by norm_num : (0 : ℝ) < 5) hs
    (by have : (k : ℝ) ≤ 5 := by exact_mod_cast hk
        linarith)
  have e : Real.exp (-(43 / 96) * 5 ^ 2) * Real.exp (1075 / 96) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 : Real.exp (-(43 / 96) * 5 ^ 2) * 66000 ≤ 1 := by
    nlinarith [exp_1075_96_gt, Real.exp_pos (-(43 / 96) * (5 : ℝ) ^ 2)]
  have h5 : (0 : ℝ) < 5 ^ k := by positivity
  calc s ^ k * Real.exp (-(43 / 96) * s ^ 2) ≤ 5 ^ k * Real.exp (-(43 / 96) * 5 ^ 2) := h
    _ ≤ 5 ^ k / 66000 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith

/-- `s² e^{−s²/4} ≤ 1/20` for `s ≥ 5`. -/
lemma exp_tail_quarter {s : ℝ} (hs : 5 ≤ s) :
    s ^ 2 * Real.exp (-(s ^ 2) / 4) ≤ 1 / 20 := by
  have h := pow_mul_exp_neg_le (k := 2) (c := 1 / 4) (by norm_num : (0 : ℝ) < 5) hs
    (by norm_num)
  rw [show -(1 / 4 : ℝ) * s ^ 2 = -(s ^ 2) / 4 by ring] at h
  have e : Real.exp (-(1 / 4) * 5 ^ 2) * Real.exp (25 / 4) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 : Real.exp (-(1 / 4) * 5 ^ 2) * 500 ≤ 1 := by
    nlinarith [exp_25_4_gt, Real.exp_pos (-(1 / 4) * (5 : ℝ) ^ 2)]
  calc s ^ 2 * Real.exp (-(s ^ 2) / 4) ≤ 5 ^ 2 * Real.exp (-(1 / 4) * 5 ^ 2) := h
    _ ≤ 1 / 20 := by nlinarith

/-- **The numerical step of the mass estimate**, `s = √u ≥ 5`. -/
lemma mass_numeric (q : ℝ) {s : ℝ} (hs : 5 ≤ s) :
    (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (1 / (33 / 50 * s) ^ 4) +
          5 / 96 * (3 * √Real.pi / 4 / (33 / 50 * s) ^ 5)) +
        2 * Real.pi * Real.exp (-(43 / 96) * s ^ 2) +
        Real.exp (-(s ^ 2) / 4) * (√Real.pi / (s / 2))) ≤
      |1 - 2 * q| / (6 * s ^ 2) + 1 / (4 * s ^ 3) := by
  have hs0 : 0 < s := by linarith
  have hpi : 3.14 < Real.pi := Real.pi_gt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hP177 : 1.77 < √Real.pi := sqrt_pi_gt
  obtain ⟨P, hP⟩ : ∃ P, P = √Real.pi := ⟨_, rfl⟩
  rw [← hP] at hP177 ⊢
  have hPP : Real.pi = P * P := by rw [hP, Real.mul_self_sqrt hpi0.le]
  have hP0 : 0 < P := by linarith
  have hP177' : (1.77 : ℝ) ≤ P := hP177.le
  have hE1 := exp_tail_43 (k := 3) (by norm_num) hs
  have hE2 := exp_tail_quarter hs
  have hq : 0 ≤ |1 - 2 * q| := abs_nonneg _
  have hA : (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (1 / (33 / 50 * s) ^ 4))) ≤
      |1 - 2 * q| / (6 * s ^ 2) := by
    have e : (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (1 / (33 / 50 * s) ^ 4))) =
        |1 - 2 * q| / (6 * s ^ 2) * ((50 / 33) ^ 4 / (2 * Real.pi)) := by
      field_simp
    rw [e]
    apply mul_le_of_le_one_right (by positivity)
    rw [div_le_one (by positivity)]
    nlinarith
  have hsplit : (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (1 / (33 / 50 * s) ^ 4) +
          5 / 96 * (3 * P / 4 / (33 / 50 * s) ^ 5)) +
        2 * Real.pi * Real.exp (-(43 / 96) * s ^ 2) +
        Real.exp (-(s ^ 2) / 4) * (P / (s / 2))) =
      (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (1 / (33 / 50 * s) ^ 4))) +
        (15 / 768 * (50 / 33) ^ 5 / P + s ^ 3 * Real.exp (-(43 / 96) * s ^ 2) +
          s ^ 2 * Real.exp (-(s ^ 2) / 4) / P) / s ^ 3 := by
    rw [hPP]; field_simp; ring
  have hX : 15 / 768 * (50 / 33) ^ 5 / P + s ^ 3 * Real.exp (-(43 / 96) * s ^ 2) +
      s ^ 2 * Real.exp (-(s ^ 2) / 4) / P ≤ 1 / 4 := by
    have h1 : 15 / 768 * (50 / 33) ^ 5 / P ≤ 15 / 768 * (50 / 33) ^ 5 / 1.77 := by gcongr
    have h3 : s ^ 2 * Real.exp (-(s ^ 2) / 4) / P ≤ (1 / 20) / 1.77 := by
      calc s ^ 2 * Real.exp (-(s ^ 2) / 4) / P ≤ (1 / 20) / P := by gcongr
        _ ≤ (1 / 20) / 1.77 := by gcongr
    norm_num at h1 h3 hE1 ⊢
    linarith
  rw [hsplit]
  have hs3 : 0 < s ^ 3 := by positivity
  have hY : (15 / 768 * (50 / 33) ^ 5 / P + s ^ 3 * Real.exp (-(43 / 96) * s ^ 2) +
      s ^ 2 * Real.exp (-(s ^ 2) / 4) / P) / s ^ 3 ≤ 1 / (4 * s ^ 3) := by
    rw [div_le_div_iff₀ hs3 (by positivity)]
    nlinarith
  linarith

/-- **The numerical step of the curvature estimate**, `s = √u ≥ 5`. -/
lemma curv_numeric (q : ℝ) {s : ℝ} (hs : 5 ≤ s) :
    (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (2 / (33 / 50 * s) ^ 6) +
          5 / 96 * (15 * √Real.pi / 8 / (33 / 50 * s) ^ 7)) +
        5 / 48 * (3 * √Real.pi / 4 / (33 / 50 * s) ^ 5) +
        2 * Real.pi * (4 * Real.exp (-(43 / 96) * s ^ 2)) +
        Real.exp (-(s ^ 2) / 4) * (√Real.pi / 2 / (s / 2) ^ 3)) ≤
      2 / 3 * |1 - 2 * q| / (s ^ 2) ^ 2 + 1 / s ^ 5 := by
  have hs0 : 0 < s := by linarith
  have hpi : 3.14 < Real.pi := Real.pi_gt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hP177 : 1.77 < √Real.pi := sqrt_pi_gt
  obtain ⟨P, hP⟩ : ∃ P, P = √Real.pi := ⟨_, rfl⟩
  rw [← hP] at hP177 ⊢
  have hPP : Real.pi = P * P := by rw [hP, Real.mul_self_sqrt hpi0.le]
  have hP0 : 0 < P := by linarith
  have hP177' : (1.77 : ℝ) ≤ P := hP177.le
  have hE1 := exp_tail_43 (k := 5) (by norm_num) hs
  have hE2 := exp_tail_quarter hs
  have hq : 0 ≤ |1 - 2 * q| := abs_nonneg _
  have hA : (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (2 / (33 / 50 * s) ^ 6))) ≤
      2 / 3 * |1 - 2 * q| / (s ^ 2) ^ 2 := by
    have e : (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (2 / (33 / 50 * s) ^ 6))) =
        2 / 3 * |1 - 2 * q| / (s ^ 2) ^ 2 * ((50 / 33) ^ 6 / (4 * Real.pi)) := by
      field_simp; ring
    rw [e]
    apply mul_le_of_le_one_right (by positivity)
    rw [div_le_one (by positivity)]
    nlinarith
  have hsplit : (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (2 / (33 / 50 * s) ^ 6) +
          5 / 96 * (15 * P / 8 / (33 / 50 * s) ^ 7)) +
        5 / 48 * (3 * P / 4 / (33 / 50 * s) ^ 5) +
        2 * Real.pi * (4 * Real.exp (-(43 / 96) * s ^ 2)) +
        Real.exp (-(s ^ 2) / 4) * (P / 2 / (s / 2) ^ 3)) =
      (2 * Real.pi)⁻¹ * (s ^ 2 * (|1 - 2 * q| / 6 * (2 / (33 / 50 * s) ^ 6))) +
        (75 / 1536 * (50 / 33) ^ 7 / P + 15 / 384 * (50 / 33) ^ 5 / P +
          4 * (s ^ 5 * Real.exp (-(43 / 96) * s ^ 2)) +
          2 * (s ^ 2 * Real.exp (-(s ^ 2) / 4)) / P) / s ^ 5 := by
    rw [hPP]; field_simp; ring
  have hX : 75 / 1536 * (50 / 33) ^ 7 / P + 15 / 384 * (50 / 33) ^ 5 / P +
      4 * (s ^ 5 * Real.exp (-(43 / 96) * s ^ 2)) +
      2 * (s ^ 2 * Real.exp (-(s ^ 2) / 4)) / P ≤ 1 := by
    have h1 : 75 / 1536 * (50 / 33) ^ 7 / P ≤ 75 / 1536 * (50 / 33) ^ 7 / 1.77 := by gcongr
    have h2 : 15 / 384 * (50 / 33) ^ 5 / P ≤ 15 / 384 * (50 / 33) ^ 5 / 1.77 := by gcongr
    have h3 : 2 * (s ^ 2 * Real.exp (-(s ^ 2) / 4)) / P ≤ 2 * (1 / 20) / 1.77 := by
      calc 2 * (s ^ 2 * Real.exp (-(s ^ 2) / 4)) / P ≤ 2 * (1 / 20) / P := by gcongr
        _ ≤ 2 * (1 / 20) / 1.77 := by gcongr
    norm_num at h1 h2 h3 hE1 ⊢
    linarith
  rw [hsplit]
  have hs5 : 0 < s ^ 5 := by positivity
  have hY : (75 / 1536 * (50 / 33) ^ 7 / P + 15 / 384 * (50 / 33) ^ 5 / P +
      4 * (s ^ 5 * Real.exp (-(43 / 96) * s ^ 2)) +
      2 * (s ^ 2 * Real.exp (-(s ^ 2) / 4)) / P) / s ^ 5 ≤ 1 / s ^ 5 := by
    gcongr
  linarith

end Erdos993Lean.Analytic.Fourier
