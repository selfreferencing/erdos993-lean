import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Binom

/-!
# The exact kernel calculus (T1 Lemma 1.1; extra E2)

Source: T1 (`ProofRuns/2026-09-27_zhang_review/reports/T1.md`), §1, Lemma 1.1 (a)–(d) and its proof
(lines 97–113).  Notation of T1: `N = M + 2`, `i = j + 1`, `e = i − qN`, `u = j − M/2`,
`v = q(1 − q)`; the kernels

* `f_L(M, j) = (1 − q) b_M(j) − q b_M(j − 1)` (`fL`),
* `f_R(M, j) = q b_M(j) − (1 − q) b_M(j + 1)` (`fR`),
* `f_C(M, j) = 2 b_M(j) − b_M(j − 1) − b_M(j + 1)` (`fC`),
* `κ = f_L/q + f_R/(1 − q)` (`kappa`, `Erdos993Lean/Analytic/Defs.lean`; `kappa_eq_fL_fR`).

All identities hold for **every** integer `j` (the kernels and `b_N` vanish consistently off the
support), because they are derived from the step relations of `NoValley/Binom.lean`, which hold for
all `j`.  In the statements `N, i, e, u, v` are real variables tied to `M, j, q` by hypotheses.

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

* (a) `fL_eq`: `f_L = b_{M+1}(j) (M + 1 − 2j)/(M + 1)`; `fR_eq`: `f_R = b_{M+1}(j + 1) (2j + 1 − M)/(M + 1)`.
* (b) `fC_eq`: `f_C = (Nv + (1 − 2q)e − e²)/(N(N − 1)v²) · b_N(i)` (for `q ≠ 0, 1`).
* (c) `fL_fR_combination`: for all `a, b`,
  `a q f_L + b(1 − q) f_R = b_N(i)/(N(N − 1)) · [(a + b)(N/2 − 2u²) − (a − b)(N − 1)u]`.
* (d) `kappa_eq_fC_add`: `κ = f_C + (1 − 2q)²/v · b_M(j)`; `kappa_eq_weight_mul_quad`:
  `κ = W(i) Q_κ(i)` with `W(i) = b_N(i)/(N(N − 1)v²)` and
  `Q_κ(i) = Nv + (1 − 2q)e − e² + (1 − 2q)² i(N − i)` (for `q ≠ 0, 1`); in terms of the named
  functions `kappaWeight`, `kappaQuad`: `kappa_eq_kappaWeight_mul_kappaQuad`.
-/

namespace Erdos993Lean.Analytic.NoValley

/-! ## The kernels -/

/-- `f_L(M, j) = (1 − q) b_M(j) − q b_M(j − 1)`. -/
noncomputable def fL (q : ℝ) (M : ℕ) (j : ℤ) : ℝ := (1 - q) * binom M q j - q * binom M q (j - 1)

/-- `f_R(M, j) = q b_M(j) − (1 − q) b_M(j + 1)`. -/
noncomputable def fR (q : ℝ) (M : ℕ) (j : ℤ) : ℝ := q * binom M q j - (1 - q) * binom M q (j + 1)

/-- `f_C(M, j) = 2 b_M(j) − b_M(j − 1) − b_M(j + 1)`. -/
noncomputable def fC (q : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)

theorem kappa_eq_fL_fR (q : ℝ) (M : ℕ) (j : ℤ) : kappa q M j = fL q M j / q + fR q M j / (1 - q) :=
  rfl

/-- T1's weight `W(i) = b_N(i)/(N(N − 1)v²)`, `N = M + 2`, `v = q(1 − q)` (zero off `[0, N]`). -/
noncomputable def kappaWeight (q : ℝ) (M : ℕ) (i : ℤ) : ℝ :=
  binom (M + 2) q i / (((M : ℝ) + 2) * ((M : ℝ) + 1) * (q * (1 - q)) ^ 2)

/-- T1's quadratic `Q_κ(i) = Nv + (1 − 2q)e − e² + (1 − 2q)² i(N − i)`, `N = M + 2`, `e = i − qN`,
`v = q(1 − q)`. -/
noncomputable def kappaQuad (q : ℝ) (M : ℕ) (i : ℝ) : ℝ :=
  ((M : ℝ) + 2) * (q * (1 - q)) + (1 - 2 * q) * (i - q * ((M : ℝ) + 2)) -
    (i - q * ((M : ℝ) + 2)) ^ 2 + (1 - 2 * q) ^ 2 * i * ((M : ℝ) + 2 - i)

/-! ## (a) `f_L` and `f_R` through `b_{M+1}` -/

/-- **T1 Lemma 1.1 (a), left kernel.**  `f_L = b_{M+1}(j) (M + 1 − 2j)/(M + 1)`. -/
theorem fL_eq (q : ℝ) (M : ℕ) (j : ℤ) :
    fL q M j = binom (M + 1) q j * (((M : ℝ) + 1 - 2 * j) / ((M : ℝ) + 1)) := by
  have hM : (M : ℝ) + 1 ≠ 0 := by positivity
  have h1 := binom_step_right M q j
  have h2 := binom_step_left M q j
  rw [← mul_div_assoc, eq_div_iff hM]
  unfold fL
  linear_combination h1 - h2

/-- **T1 Lemma 1.1 (a), right kernel.**  `f_R = b_{M+1}(j + 1) (2j + 1 − M)/(M + 1)`. -/
theorem fR_eq (q : ℝ) (M : ℕ) (j : ℤ) :
    fR q M j = binom (M + 1) q (j + 1) * ((2 * (j : ℝ) + 1 - M) / ((M : ℝ) + 1)) := by
  have hM : (M : ℝ) + 1 ≠ 0 := by positivity
  have h1 := binom_step_right M q (j + 1)
  have h2 := binom_step_left M q (j + 1)
  rw [add_sub_cancel_right] at h2
  push_cast at h1 h2
  rw [← mul_div_assoc, eq_div_iff hM]
  unfold fR
  linear_combination h2 - h1

/-! ## (b) `f_C` through `b_{M+2}` -/

/-- **T1 Lemma 1.1 (b).**  With `N = M + 2`, `i = j + 1`, `e = i − qN`, `v = q(1 − q)` and
`q ≠ 0, 1`: `f_C = (Nv + (1 − 2q)e − e²)/(N(N − 1)v²) · b_N(i)`. -/
theorem fC_eq {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (M : ℕ) (j : ℤ) {N i e v : ℝ}
    (hN : N = M + 2) (hi : i = j + 1) (he : e = i - q * N) (hv : v = q * (1 - q)) :
    fC q M j =
      (N * v + (1 - 2 * q) * e - e ^ 2) / (N * (N - 1) * v ^ 2) * binom (M + 2) q (j + 1) := by
  subst hN hi he hv
  have hq1' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hden : ((M : ℝ) + 2) * ((M : ℝ) + 2 - 1) * (q * (1 - q)) ^ 2 ≠ 0 := by
    have : (M : ℝ) + 2 - 1 = (M : ℝ) + 1 := by ring
    rw [this]
    positivity
  have T0 := binom_two_step_mid M q j
  have Tm := binom_two_step_left M q j
  have Tp := binom_two_step_right M q j
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  unfold fC
  linear_combination (2 * (q * (1 - q))) * T0 - (1 - q) ^ 2 * Tm - q ^ 2 * Tp

/-! ## (c) the two-sided combination -/

/-- **T1 Lemma 1.1 (c).**  With `N = M + 2`, `u = j − M/2`, for all real `a, b` (T1 uses
`a, b ≥ 0`): `a q f_L + b(1 − q) f_R = b_N(i)/(N(N − 1)) · [(a + b)(N/2 − 2u²) − (a − b)(N − 1)u]`. -/
theorem fL_fR_combination (q : ℝ) (M : ℕ) (j : ℤ) (a b : ℝ) {N u : ℝ} (hN : N = M + 2)
    (hu : u = j - M / 2) :
    a * q * fL q M j + b * (1 - q) * fR q M j =
      binom (M + 2) q (j + 1) / (N * (N - 1)) *
        ((a + b) * (N / 2 - 2 * u ^ 2) - (a - b) * (N - 1) * u) := by
  subst hN hu
  have hden : ((M : ℝ) + 2) * ((M : ℝ) + 2 - 1) ≠ 0 := by
    have : (M : ℝ) + 2 - 1 = (M : ℝ) + 1 := by ring
    rw [this]
    positivity
  have hM : (M : ℝ) + 1 ≠ 0 := by positivity
  -- multiplicative forms of (a)
  have A1 : ((M : ℝ) + 1) * fL q M j = ((M : ℝ) + 1 - 2 * j) * binom (M + 1) q j := by
    rw [fL_eq]
    field_simp
  have A2 : ((M : ℝ) + 1) * fR q M j = (2 * (j : ℝ) + 1 - M) * binom (M + 1) q (j + 1) := by
    rw [fR_eq]
    field_simp
  -- `b_{M+1}` through `b_{M+2}`
  have S1 := binom_step_left (M + 1) q (j + 1)
  rw [add_sub_cancel_right] at S1
  have S2 := binom_step_right (M + 1) q (j + 1)
  push_cast at S1 S2
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (a * q * ((M : ℝ) + 2)) * A1 + (b * (1 - q) * ((M : ℝ) + 2)) * A2 +
    (a * ((M : ℝ) + 1 - 2 * j)) * S1 + (b * (2 * (j : ℝ) + 1 - M)) * S2

/-! ## (d) the valley kernel `κ` -/

/-- **T1 Lemma 1.1 (d), first form.**  `κ = f_C + (1 − 2q)²/v · b_M(j)`, `v = q(1 − q)`. -/
theorem kappa_eq_fC_add {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (M : ℕ) (j : ℤ) :
    kappa q M j = fC q M j + (1 - 2 * q) ^ 2 / (q * (1 - q)) * binom M q j := by
  have hq1' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  unfold kappa fC
  field_simp
  ring

/-- **T1 Lemma 1.1 (d), second form.**  With `N = M + 2`, `i = j + 1`, `e = i − qN`,
`v = q(1 − q)` and `q ≠ 0, 1`: `κ = W(i) Q_κ(i)` with `W(i) = b_N(i)/(N(N − 1)v²)` and
`Q_κ(i) = Nv + (1 − 2q)e − e² + (1 − 2q)² i(N − i)`. -/
theorem kappa_eq_weight_mul_quad {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (M : ℕ) (j : ℤ)
    {N i e v : ℝ} (hN : N = M + 2) (hi : i = j + 1) (he : e = i - q * N) (hv : v = q * (1 - q)) :
    kappa q M j = binom (M + 2) q (j + 1) / (N * (N - 1) * v ^ 2) *
      (N * v + (1 - 2 * q) * e - e ^ 2 + (1 - 2 * q) ^ 2 * i * (N - i)) := by
  subst hN hi he hv
  have hq1' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hden : ((M : ℝ) + 2) * ((M : ℝ) + 2 - 1) * (q * (1 - q)) ^ 2 ≠ 0 := by
    have : (M : ℝ) + 2 - 1 = (M : ℝ) + 1 := by ring
    rw [this]
    positivity
  have T0 := binom_two_step_mid M q j
  have Tm := binom_two_step_left M q j
  have Tp := binom_two_step_right M q j
  have hk : kappa q M j * (q * (1 - q)) =
      (1 - q) ^ 2 * binom M q j - q * (1 - q) * binom M q (j - 1) + q ^ 2 * binom M q j -
        q * (1 - q) * binom M q (j + 1) := by
    unfold kappa
    field_simp
    ring
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (((M : ℝ) + 2) * ((M : ℝ) + 1) * (q * (1 - q))) * hk +
    (1 - 2 * q + 2 * q ^ 2) * T0 - (1 - q) ^ 2 * Tm - q ^ 2 * Tp

/-- **T1 Lemma 1.1 (d) with the named weight and quadratic:** `κ(M, j) = W(j + 1) Q_κ(j + 1)`. -/
theorem kappa_eq_kappaWeight_mul_kappaQuad {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (M : ℕ) (j : ℤ) :
    kappa q M j = kappaWeight q M (j + 1) * kappaQuad q M ((j : ℝ) + 1) := by
  rw [kappa_eq_weight_mul_quad hq0 hq1 M j rfl rfl rfl rfl, kappaWeight, kappaQuad]
  congr 1
  congr 1
  ring

end Erdos993Lean.Analytic.NoValley
