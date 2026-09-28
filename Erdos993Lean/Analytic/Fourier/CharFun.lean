import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The characteristic function of a centred Bernoulli variable

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F1.
Source: `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` §2 (modulus and Taylor bounds, difference of powers; older
version `SOUL/O4/LARGE_MEAN_PROOF.md` §1).

For `X ~ Bernoulli(q)`, `v = q(1 − q)` and `χ(t) = E e^{it(X − q)}` (`chi`):

* `norm_chi_le`: `|χ(t)| ≤ exp(−v(1 − cos t))`, from `|χ(t)|² = 1 − 2v(1 − cos t)`;
* `one_sub_cos_ge_sq`, `one_sub_cos_ge_of_one_le`: `1 − cos t ≥ (43/96) t²` on `|t| ≤ 1` and
  `1 − cos t ≥ 43/96` on `1 ≤ |t| ≤ π` (Mathlib's `Real.cos_bound`);
* `norm_chi_sub_gauss_le` (Taylor): `|χ(t) − e^{−vt²/2}| ≤ v (|1 − 2q| |t|³/6 + 5t⁴/96)` on
  `|t| ≤ 1` (`E(X − q)³ = v(1 − 2q)`, `E(X − q)⁴ = v(1 − 3v)`);
* `norm_pow_sub_pow_le_of_le`: `|x^n − y^n| ≤ n |x − y| r^{n−1}` when `|x|, |y| ≤ r`;
* `norm_chi_pow_sub_gauss_le` (inner estimate; `M ≥ 100`, `u = Mv`):
  `|χ(t)^M − e^{−ut²/2}| ≤ u (|1 − 2q| |t|³/6 + 5t⁴/96) e^{−(1089/2500) u t²}` on `|t| ≤ 1`;
* `norm_chi_pow_le_of_one_le` (outer estimate): `|χ(t)|^M ≤ e^{−(43/96) u}` on `1 ≤ |t| ≤ π`.

Constants versus the source: the source uses `sin(|t|/2) ≥ 23|t|/48` (decay `529/1152`), the
power-step rate `a = 9/20`, the quartic Taylor coefficient `7/96` and the outer circle rate `9/20`.
Here the decay `43/96` comes directly from `Real.cos_bound`, the power-step rate is
`(33/50)² = 1089/2500` (valid because `(43/96)(M − 1) ≥ (1089/2500) M` for `M ≥ 100`, and `u ≥ 25`
forces `M ≥ 100`), the quartic coefficient is the sharper `5/96`, and the outer circle rate is
`43/96`.  The two final estimates (`Fourier/Main.lean`) are exactly the source's.
-/

namespace Erdos993Lean.Analytic.Fourier

/-- The centred characteristic function `χ(t) = E e^{it(X − q)}` of `X ~ Bernoulli(q)`. -/
noncomputable def chi (q t : ℝ) : ℂ :=
  (1 - (q : ℂ)) * Complex.exp (-((q : ℂ) * t) * Complex.I) +
    (q : ℂ) * Complex.exp ((1 - (q : ℂ)) * t * Complex.I)

/-- `ψ(t) = 1 − q + q e^{it}`, so that `ψ(t)^M = ∑_k b_M(k) e^{ikt}`. -/
noncomputable def psi (q t : ℝ) : ℂ := (1 - (q : ℂ)) + (q : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

lemma chi_eq (q t : ℝ) : chi q t = Complex.exp (-((q : ℂ) * t) * Complex.I) * psi q t := by
  have h : Complex.exp ((1 - (q : ℂ)) * t * Complex.I) =
      Complex.exp (-((q : ℂ) * t) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [chi, psi, h]; ring

lemma norm_psi_sq (q t : ℝ) : ‖psi q t‖ ^ 2 = 1 - 2 * (q * (1 - q)) * (1 - Real.cos t) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (psi q t).re = 1 - q + q * Real.cos t := by
    simp [psi, Complex.exp_ofReal_mul_I_re]
  have him : (psi q t).im = q * Real.sin t := by
    simp [psi, Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  linear_combination q ^ 2 * Real.sin_sq_add_cos_sq t

lemma norm_chi_eq (q t : ℝ) : ‖chi q t‖ = ‖psi q t‖ := by
  rw [chi_eq, norm_mul,
    show -((q : ℂ) * t) * Complex.I = ((-(q * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `|χ(t)| ≤ exp(−q(1 − q)(1 − cos t))`, from `|χ(t)|² = 1 − 2q(1 − q)(1 − cos t)`. -/
lemma norm_chi_le (q t : ℝ) : ‖chi q t‖ ≤ Real.exp (-(q * (1 - q)) * (1 - Real.cos t)) := by
  have e : Real.exp (-(q * (1 - q)) * (1 - Real.cos t)) ^ 2 =
      Real.exp (-(2 * (q * (1 - q)) * (1 - Real.cos t))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : ‖chi q t‖ ^ 2 ≤ Real.exp (-(q * (1 - q)) * (1 - Real.cos t)) ^ 2 := by
    rw [norm_chi_eq, norm_psi_sq, e]
    have := Real.add_one_le_exp (-(2 * (q * (1 - q)) * (1 - Real.cos t)))
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 h1

lemma one_sub_cos_ge_sq {t : ℝ} (ht : |t| ≤ 1) : 43 / 96 * t ^ 2 ≤ 1 - Real.cos t := by
  have h := Real.cos_bound ht
  have h4 : |t| ^ 4 = t ^ 2 * t ^ 2 := by
    rw [show |t| ^ 4 = (|t| ^ 2) ^ 2 by ring, sq_abs]; ring
  have ht2 : t ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  rw [abs_le, h4] at h
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.2 ht2)]

lemma one_sub_cos_ge_of_one_le {t : ℝ} (h1 : 1 ≤ |t|) (h2 : |t| ≤ Real.pi) :
    43 / 96 ≤ 1 - Real.cos t := by
  have hc : Real.cos t ≤ Real.cos 1 := by
    rw [← Real.cos_abs t]
    exact Real.cos_le_cos_of_nonneg_of_le_pi zero_le_one h2 h1
  have hb := (abs_le.1 (Real.cos_bound (x := 1) (by norm_num))).2
  norm_num at hb
  linarith

lemma norm_cexp_sub_cubic_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6)‖ ≤ ‖z‖ ^ 4 * (5 / 96) := by
  have h := Complex.exp_bound hz (n := 4) (by norm_num)
  have f2 : (2 : ℕ).factorial = 2 := rfl
  have f3 : (3 : ℕ).factorial = 6 := rfl
  have f4 : (4 : ℕ).factorial = 24 := rfl
  have e : (∑ m ∈ Finset.range 4, z ^ m / (m.factorial : ℂ)) =
      1 + z + z ^ 2 / 2 + z ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, f2, f3, Nat.factorial_zero,
      Nat.factorial_one]
    push_cast; ring
  rw [e, f4] at h
  convert h using 2
  norm_num

lemma abs_exp_neg_sub_quadratic_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |Real.exp (-y) - (1 - y + y ^ 2 / 2)| ≤ 2 / 9 * y ^ 3 := by
  have h := Real.exp_bound (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact hy1)
    (n := 3) (by norm_num)
  have f2 : (2 : ℕ).factorial = 2 := rfl
  have f3 : (3 : ℕ).factorial = 6 := rfl
  have e : (∑ m ∈ Finset.range 3, (-y) ^ m / (m.factorial : ℝ)) = 1 - y + y ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, f2, Nat.factorial_zero,
      Nat.factorial_one]
    push_cast; ring
  rw [e, abs_neg, abs_of_nonneg hy0, f3] at h
  convert h using 1
  norm_num
  ring

/-- **Taylor bound for the characteristic function** on `|t| ≤ 1`:
`|χ(t) − e^{−vt²/2}| ≤ v (|1 − 2q| |t|³/6 + 5t⁴/96)` with `v = q(1 − q)` (the source has the
weaker `7/96`). -/
lemma norm_chi_sub_gauss_le {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : |t| ≤ 1) :
    ‖chi q t - (Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℂ)‖ ≤
      q * (1 - q) * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) := by
  have ha0 : 0 ≤ |t| := abs_nonneg t
  have hq1' : 0 ≤ 1 - q := by linarith
  obtain ⟨z1, hz1⟩ : ∃ z : ℂ, z = ((1 - q : ℝ) : ℂ) * t * Complex.I := ⟨_, rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ z : ℂ, z = ((-q : ℝ) : ℂ) * t * Complex.I := ⟨_, rfl⟩
  have hn1 : ‖z1‖ = (1 - q) * |t| := by
    rw [hz1, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq1']
  have hn2 : ‖z2‖ = q * |t| := by
    rw [hz2, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg hq0]
  have B1 := norm_cexp_sub_cubic_le (z := z1) (by rw [hn1]; nlinarith)
  have B2 := norm_cexp_sub_cubic_le (z := z2) (by rw [hn2]; nlinarith)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = q * (1 - q) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; exact mul_nonneg hq0 hq1'
  have hv1 : v ≤ 1 / 4 := by rw [hv]; nlinarith [sq_nonneg (q - 1 / 2)]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have ha1 : |t| ^ 2 ≤ 1 := by nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = v * t ^ 2 / 2 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 8 := by rw [hy, ht2]; nlinarith
  have B3 := abs_exp_neg_sub_quadratic_le hy0 (by linarith)
  have hchi : chi q t = (1 - (q : ℂ)) * Complex.exp z2 + (q : ℂ) * Complex.exp z1 := by
    rw [chi, hz1, hz2]; push_cast; ring_nf
  have key : chi q t - (Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℂ) =
      (q : ℂ) * (Complex.exp z1 - (1 + z1 + z1 ^ 2 / 2 + z1 ^ 3 / 6)) +
      ((1 - q : ℝ) : ℂ) * (Complex.exp z2 - (1 + z2 + z2 ^ 2 / 2 + z2 ^ 3 / 6)) +
      (-Complex.I * ((v * (1 - 2 * q) * t ^ 3 / 6 : ℝ) : ℂ)) -
      ((Real.exp (-y) - (1 - y + y ^ 2 / 2) : ℝ) : ℂ) - ((y ^ 2 / 2 : ℝ) : ℂ) := by
    have ey : -(q * (1 - q)) * t ^ 2 / 2 = -y := by rw [hy, hv]; ring
    rw [hchi, ey, hz1, hz2, hy, hv]
    push_cast
    linear_combination ((q : ℂ) * (1 - (q : ℂ)) * (t : ℂ) ^ 2 / 2 +
      (q : ℂ) * (1 - (q : ℂ)) * (1 - 2 * (q : ℂ)) * (t : ℂ) ^ 3 * Complex.I / 6) * Complex.I_sq
  rw [key]
  have hc : ‖-Complex.I * ((v * (1 - 2 * q) * t ^ 3 / 6 : ℝ) : ℂ)‖ =
      v * |1 - 2 * q| * |t| ^ 3 / 6 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_mul, abs_mul, abs_pow, abs_of_nonneg hv0]
    norm_num
  have hq_norm : ‖(q : ℂ)‖ = q := Complex.norm_of_nonneg hq0
  have hq1_norm : ‖((1 - q : ℝ) : ℂ)‖ = 1 - q := Complex.norm_of_nonneg hq1'
  have h4 : ‖((Real.exp (-y) - (1 - y + y ^ 2 / 2) : ℝ) : ℂ)‖ ≤ 2 / 9 * y ^ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact B3
  have h5 : ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ = y ^ 2 / 2 := Complex.norm_of_nonneg (by positivity)
  have e1 : q * ((1 - q) * |t|) ^ 4 + (1 - q) * (q * |t|) ^ 4 = v * (1 - 3 * v) * |t| ^ 4 := by
    rw [hv]; ring
  have e2 : y ^ 2 = v ^ 2 * |t| ^ 4 / 4 := by
    rw [hy, ht2]; ring
  have e3 : y ^ 3 ≤ y ^ 2 / 8 := by nlinarith [sq_nonneg y]
  have e4 : t ^ 4 = |t| ^ 4 := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, show |t| ^ 4 = (|t| ^ 2) ^ 2 by ring, sq_abs]
  calc _ ≤ ‖(q : ℂ) * (Complex.exp z1 - (1 + z1 + z1 ^ 2 / 2 + z1 ^ 3 / 6))‖ +
        ‖((1 - q : ℝ) : ℂ) * (Complex.exp z2 - (1 + z2 + z2 ^ 2 / 2 + z2 ^ 3 / 6))‖ +
        ‖-Complex.I * ((v * (1 - 2 * q) * t ^ 3 / 6 : ℝ) : ℂ)‖ +
        ‖((Real.exp (-y) - (1 - y + y ^ 2 / 2) : ℝ) : ℂ)‖ + ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ q * (((1 - q) * |t|) ^ 4 * (5 / 96)) + (1 - q) * ((q * |t|) ^ 4 * (5 / 96)) +
        v * |1 - 2 * q| * |t| ^ 3 / 6 + 2 / 9 * y ^ 3 + y ^ 2 / 2 := by
        rw [norm_mul, norm_mul, hq_norm, hq1_norm, hc, h5, ← hn1, ← hn2]
        gcongr
    _ ≤ q * (1 - q) * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) := by
        rw [← hv, e4]
        nlinarith [e1, e2, e3, sq_nonneg y]

/-- `‖x^n − y^n‖ ≤ n ‖x − y‖ r^{n−1}` when `‖x‖, ‖y‖ ≤ r`. -/
lemma norm_pow_sub_pow_le_of_le {x y : ℂ} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * ‖x - y‖ * r ^ (n - 1) := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  rw [← geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤ n * r ^ (n - 1) := by
    calc ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖
        ≤ ∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, r ^ (n - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, norm_pow, norm_pow]
          have hi' : i + (n - 1 - i) = n - 1 := by
            have := Finset.mem_range.1 hi; omega
          calc ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i) ≤ r ^ i * r ^ (n - 1 - i) := by gcongr
            _ = r ^ (n - 1) := by rw [← pow_add, hi']
      _ = n * r ^ (n - 1) := by simp
  calc ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ * ‖x - y‖
      ≤ (n * r ^ (n - 1)) * ‖x - y‖ := by gcongr
    _ = n * ‖x - y‖ * r ^ (n - 1) := by ring

/-- **The inner estimate** (`|t| ≤ 1`, `M ≥ 100`):
`|χ(t)^M − e^{−ut²/2}| ≤ u (|1 − 2q| |t|³/6 + 5t⁴/96) e^{−(1089/2500) u t²}` with `u = Mq(1 − q)`. -/
lemma norm_chi_pow_sub_gauss_le {q t : ℝ} {M : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : |t| ≤ 1)
    (hM : 100 ≤ M) :
    ‖chi q t ^ M - (Real.exp (-((M : ℝ) * (q * (1 - q))) * t ^ 2 / 2) : ℂ)‖ ≤
      (M : ℝ) * (q * (1 - q)) * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) *
        Real.exp (-(1089 / 2500) * ((M : ℝ) * (q * (1 - q))) * t ^ 2) := by
  have hv0 : 0 ≤ q * (1 - q) := mul_nonneg hq0 (by linarith)
  have hx : ‖chi q t‖ ≤ Real.exp (-(43 / 96) * (q * (1 - q)) * t ^ 2) := by
    refine (norm_chi_le q t).trans (Real.exp_le_exp.2 ?_)
    have := one_sub_cos_ge_sq ht
    nlinarith
  have hy : ‖((Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      Real.exp (-(43 / 96) * (q * (1 - q)) * t ^ 2) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg t])
  have hpow : ((Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℝ) : ℂ) ^ M =
      ((Real.exp (-((M : ℝ) * (q * (1 - q))) * t ^ 2 / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]; congr 2; ring
  have h1 := norm_pow_sub_pow_le_of_le hx hy M
  rw [hpow] at h1
  have h2 := norm_chi_sub_gauss_le hq0 hq1 ht
  have h3 : Real.exp (-(43 / 96) * (q * (1 - q)) * t ^ 2) ^ (M - 1) ≤
      Real.exp (-(1089 / 2500) * ((M : ℝ) * (q * (1 - q))) * t ^ 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M)]; simp
    rw [hM1]
    have hw : 0 ≤ q * (1 - q) * t ^ 2 := by positivity
    have hM' : (100 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [mul_nonneg hw (sub_nonneg.2 hM')]
  calc ‖chi q t ^ M - ((Real.exp (-((M : ℝ) * (q * (1 - q))) * t ^ 2 / 2) : ℝ) : ℂ)‖
      ≤ M * ‖chi q t - ((Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℝ) : ℂ)‖ *
          Real.exp (-(43 / 96) * (q * (1 - q)) * t ^ 2) ^ (M - 1) := h1
    _ ≤ M * (q * (1 - q) * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4)) *
          Real.exp (-(1089 / 2500) * ((M : ℝ) * (q * (1 - q))) * t ^ 2) := by
        gcongr
    _ = (M : ℝ) * (q * (1 - q)) * (|1 - 2 * q| * |t| ^ 3 / 6 + 5 / 96 * t ^ 4) *
          Real.exp (-(1089 / 2500) * ((M : ℝ) * (q * (1 - q))) * t ^ 2) := by ring

/-- **The outer estimate** (`1 ≤ |t| ≤ π`): `|χ(t)|^M ≤ e^{−(43/96) u}`. -/
lemma norm_chi_pow_le_of_one_le {q t : ℝ} (M : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h1 : 1 ≤ |t|) (h2 : |t| ≤ Real.pi) :
    ‖chi q t ^ M‖ ≤ Real.exp (-(43 / 96) * ((M : ℝ) * (q * (1 - q)))) := by
  rw [norm_pow]
  have hv0 : 0 ≤ q * (1 - q) := mul_nonneg hq0 (by linarith)
  have hc := one_sub_cos_ge_of_one_le h1 h2
  calc ‖chi q t‖ ^ M ≤ Real.exp (-(43 / 96) * (q * (1 - q))) ^ M := by
        gcongr
        exact (norm_chi_le q t).trans (Real.exp_le_exp.2 (by nlinarith))
    _ = Real.exp (-(43 / 96) * ((M : ℝ) * (q * (1 - q)))) := by
        rw [← Real.exp_nat_mul]; ring_nf

end Erdos993Lean.Analytic.Fourier
