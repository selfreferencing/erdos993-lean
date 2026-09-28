import Erdos993Lean.Analytic.LargeMean.Constants
import Erdos993Lean.Analytic.LargeMean.InversePower
import Erdos993Lean.Analytic.LargeMean.Averaging

/-!
# Pointwise bounds on the conditioning atoms

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F2.
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md`, §5 and §6.

Notation: `q ∈ [1/4, 7/10]`, `m = E M`, `ρ > 0` with `ρ² = s = q(1 − q)m ≥ 75`, an atom `(M, j)`
with `t = M/m` and `δ = j − qM`, and `r` with `m/3 ≤ r + 1`.

* `curvMinorant q ρ t = (a₀/ρ³)(t − 20(t − 1)²) − (2/3)|1 − 2q|ρ^{−4}(1 − 2(t − 1) + 15(t − 1)²)
  − ρ^{−5}(1 − (5/2)(t − 1) + 30(t − 1)²)`, a quadratic in `t − 1` with coefficients
  `lmA`, `lmB`, `−lmC` (`curvMinorant_eq`).
* `fC_ge_of_large`: on `M ≥ m/3` (so `u = qM(1 − q) ≥ 25`), the curvature Fourier estimate, the
  envelope (G) and the inverse-power bounds give `f_C + (a₀/ρ⁵) δ² ≥ curvMinorant(t)`.
* `fC_ge_curvMinorant_sub`: on every atom, `f_C + (a₀/ρ⁵) δ² ≥ curvMinorant(t) − 2·1[M ≤ r]`
  (on `M < m/3` use `f_C ≥ −2` and `curvMinorant(t) ≤ 0`; the source uses `f_C ≥ −1`).
* `binom_ge_good`: on every atom,
  `b_M(j) ≥ (1/(40ρ)) (1 − 4(t − 1)² − (2/(3ρ²)) δ²)`.  On the source's event
  `A = {m/2 ≤ M ≤ 2m, δ² ≤ 3s/2}` the mass Fourier estimate gives `b_M(j) ≥ 1/(40ρ)`
  (`gaussPhi_ge_of_good`, `mass_err_le_of_good`, `good_const`), and off `A` the factor is `≤ 0`
  (`good_factor_nonpos`).  This is the pointwise form of the source's Chebyshev + Markov step.
-/

namespace Erdos993Lean.Analytic.LargeMean

/-- The curvature minorant `L(t)` (source (G) minus the Fourier errors after the inverse-power
bounds), with `ρ² = s`. -/
noncomputable def curvMinorant (q ρ t : ℝ) : ℝ :=
  gaussA0 / ρ ^ 3 * (t - 20 * (t - 1) ^ 2)
    - 2 / 3 * |1 - 2 * q| / ρ ^ 4 * (1 - 2 * (t - 1) + 15 * (t - 1) ^ 2)
    - 1 / ρ ^ 5 * (1 - 5 / 2 * (t - 1) + 30 * (t - 1) ^ 2)

/-- The constant coefficient of `curvMinorant` in `t − 1`. -/
noncomputable def lmA (q ρ : ℝ) : ℝ := gaussA0 / ρ ^ 3 - 2 / 3 * |1 - 2 * q| / ρ ^ 4 - 1 / ρ ^ 5

/-- The linear coefficient of `curvMinorant` in `t − 1`. -/
noncomputable def lmB (q ρ : ℝ) : ℝ :=
  gaussA0 / ρ ^ 3 + 2 * (2 / 3 * |1 - 2 * q| / ρ ^ 4) + 5 / 2 * (1 / ρ ^ 5)

/-- Minus the quadratic coefficient of `curvMinorant` in `t − 1`. -/
noncomputable def lmC (q ρ : ℝ) : ℝ :=
  20 * (gaussA0 / ρ ^ 3) + 15 * (2 / 3 * |1 - 2 * q| / ρ ^ 4) + 30 * (1 / ρ ^ 5)

theorem curvMinorant_eq (q ρ t : ℝ) :
    curvMinorant q ρ t = lmA q ρ + lmB q ρ * (t - 1) - lmC q ρ * (t - 1) ^ 2 := by
  unfold curvMinorant lmA lmB lmC; ring

theorem lmC_nonneg (q : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : 0 ≤ lmC q ρ := by
  unfold lmC; have := gaussA0_pos; positivity

/-- On `M ≥ m/3`: `f_C + (a₀/ρ⁵) δ² ≥ curvMinorant(M/m)`. -/
theorem fC_ge_of_large (hF : FourierEstimates) {q m ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hm : 0 < m) (hρ : 0 < ρ) (hρs : ρ ^ 2 = q * (1 - q) * m) (hρ75 : 75 ≤ ρ ^ 2) {M : ℕ}
    (hM : m / 3 ≤ (M : ℝ)) (j : ℤ) :
    curvMinorant q ρ ((M : ℝ) / m) ≤
      (2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) +
        gaussA0 / ρ ^ 5 * ((j : ℝ) - q * M) ^ 2 := by
  have hmne : m ≠ 0 := hm.ne'
  have hρne : ρ ≠ 0 := hρ.ne'
  set t : ℝ := (M : ℝ) / m with ht_def
  have ht3 : 1 / 3 ≤ t := by rw [ht_def, le_div_iff₀ hm]; linarith
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := htpos.ne'
  have hut : (M : ℝ) * (q * (1 - q)) = ρ ^ 2 * t := by
    rw [ht_def, hρs]; field_simp
  have hu0 : 0 < ρ ^ 2 * t := by positivity
  have hu25 : 25 ≤ (M : ℝ) * (q * (1 - q)) := by rw [hut]; nlinarith
  have hsu : ρ ^ 2 / 3 ≤ (M : ℝ) * (q * (1 - q)) := by rw [hut]; nlinarith
  obtain ⟨-, hcurv⟩ := hF M q hq0 hq1 j hu25
  have hG := gaussCurv_envelope (d := (j : ℝ) - q * M) hρ hsu
  rw [hut, show ρ ^ 2 * t / ρ ^ 2 = t by field_simp] at hG
  rw [hut] at hcurv
  have h2 := inv_sq_le_quad ht3
  have h5 := inv_pow_five_halves_le_quad ht3
  have e2 : 2 / 3 * |1 - 2 * q| / (ρ ^ 2 * t) ^ 2 = 2 / 3 * |1 - 2 * q| / ρ ^ 4 * (1 / t ^ 2) := by
    field_simp
  have hst : Real.sqrt (ρ ^ 2 * t) = ρ * Real.sqrt t := by
    rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ.le]
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hsqtne : Real.sqrt t ≠ 0 := hsqt.ne'
  have e5 : 1 / (ρ ^ 2 * t) ^ ((5 : ℝ) / 2) = 1 / ρ ^ 5 * (1 / (t ^ 2 * Real.sqrt t)) := by
    rw [rpow_five_halves_eq hu0, hst]; field_simp
  rw [e2, e5] at hcurv
  have hc2 : 0 ≤ 2 / 3 * |1 - 2 * q| / ρ ^ 4 := by positivity
  have hc5 : 0 ≤ 1 / ρ ^ 5 := by positivity
  have k2 := mul_le_mul_of_nonneg_left h2 hc2
  have k5 := mul_le_mul_of_nonneg_left h5 hc5
  have habs := (abs_le.mp hcurv).1
  unfold curvMinorant
  linarith

/-- On every atom: `f_C + (a₀/ρ⁵) δ² ≥ curvMinorant(M/m) − 2·1[M ≤ r]` (for `m/3 ≤ r + 1`). -/
theorem fC_ge_curvMinorant_sub (hF : FourierEstimates) {q m ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hm : 0 < m) (hρ : 0 < ρ) (hρs : ρ ^ 2 = q * (1 - q) * m) (hρ75 : 75 ≤ ρ ^ 2) {r : ℕ}
    (hr : m / 3 ≤ (r : ℝ) + 1) (M : ℕ) (j : ℤ) :
    curvMinorant q ρ ((M : ℝ) / m) - 2 * (if M ≤ r then 1 else 0) ≤
      (2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) +
        gaussA0 / ρ ^ 5 * ((j : ℝ) - q * M) ^ 2 := by
  by_cases hM : m / 3 ≤ (M : ℝ)
  · have h1 := fC_ge_of_large hF hq0 hq1 hm hρ hρs hρ75 hM j
    have h2 : (0 : ℝ) ≤ if M ≤ r then 1 else 0 := by split_ifs <;> norm_num
    linarith
  · push_neg at hM
    have hMr : M ≤ r := by
      have h : (M : ℝ) < (r : ℝ) + 1 := by linarith
      have h' : M < r + 1 := by exact_mod_cast h
      omega
    rw [if_pos hMr]
    have hfC := fC_ge_neg_two (M := M) hq0.le hq1.le j
    have hA := gaussA0_pos
    have hμ : 0 ≤ gaussA0 / ρ ^ 5 * ((j : ℝ) - q * M) ^ 2 := by positivity
    have ht0 : 0 ≤ (M : ℝ) / m := by positivity
    have ht1 : (M : ℝ) / m < 1 / 3 := by rw [div_lt_iff₀ hm]; linarith
    have hneg : (M : ℝ) / m - 20 * ((M : ℝ) / m - 1) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg ((M : ℝ) / m)]
    have hc0 : gaussA0 / ρ ^ 3 * ((M : ℝ) / m - 20 * ((M : ℝ) / m - 1) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    have hq2 : 0 ≤ 2 / 3 * |1 - 2 * q| / ρ ^ 4 *
        (1 - 2 * ((M : ℝ) / m - 1) + 15 * ((M : ℝ) / m - 1) ^ 2) :=
      mul_nonneg (by positivity) (by nlinarith [sq_nonneg ((M : ℝ) / m - 1 - 1 / 15)])
    have hq5 : 0 ≤ 1 / ρ ^ 5 * (1 - 5 / 2 * ((M : ℝ) / m - 1) + 30 * ((M : ℝ) / m - 1) ^ 2) :=
      mul_nonneg (by positivity) (by nlinarith [sq_nonneg ((M : ℝ) / m - 1 - 1 / 24)])
    unfold curvMinorant
    linarith

/-- On the good event: `φ_u(d) ≥ 1/(16ρ)` for `ρ²/2 ≤ u ≤ 2ρ²` and `d² ≤ 3ρ²/2`. -/
theorem gaussPhi_ge_of_good {ρ u d : ℝ} (hρ : 0 < ρ) (hu1 : ρ ^ 2 / 2 ≤ u) (hu2 : u ≤ 2 * ρ ^ 2)
    (hd : d ^ 2 ≤ 3 * ρ ^ 2 / 2) : 1 / (16 * ρ) ≤ gaussPhi u d := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hu0 : 0 < u := by linarith
  unfold gaussPhi
  have hq' : d ^ 2 / (2 * u) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hexp : Real.exp (-(3 / 2)) ≤ Real.exp (-(d ^ 2) / (2 * u)) := by
    apply Real.exp_le_exp.mpr
    have e : -(d ^ 2) / (2 * u) = -(d ^ 2 / (2 * u)) := by ring
    rw [e]; linarith
  have hπ := Real.pi_pos
  have hsq : Real.sqrt (2 * Real.pi * u) ≤ 2 * Real.sqrt Real.pi * ρ := by
    have h0 : 0 ≤ 2 * Real.sqrt Real.pi * ρ := by positivity
    rw [show 2 * Real.sqrt Real.pi * ρ = Real.sqrt ((2 * Real.sqrt Real.pi * ρ) ^ 2) from
      (Real.sqrt_sq h0).symm]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, mul_pow, Real.sq_sqrt hπ.le]
    nlinarith [mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hc16 := phi_const
  have hsp : 0 < Real.sqrt (2 * Real.pi * u) := by positivity
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  calc 1 / (16 * ρ) = (1 / 16) / ρ := by ring
    _ ≤ (Real.exp (-(3 / 2)) / (2 * Real.sqrt Real.pi)) / ρ :=
      div_le_div₀ (by positivity) hc16.le hρ le_rfl
    _ = Real.exp (-(3 / 2)) / (2 * Real.sqrt Real.pi * ρ) := by rw [div_div]
    _ ≤ Real.exp (-(d ^ 2) / (2 * u)) / Real.sqrt (2 * Real.pi * u) :=
      div_le_div₀ (Real.exp_pos _).le hexp hsp hsq

/-- On the good event: the mass Fourier error is at most `1/(6ρ²) + 1/ρ³` (for `u ≥ ρ²/2`,
`|1 − 2q| ≤ 1/2`). -/
theorem mass_err_le_of_good {q ρ u : ℝ} (hρ : 0 < ρ) (hA : |1 - 2 * q| ≤ 1 / 2)
    (hu1 : ρ ^ 2 / 2 ≤ u) :
    |1 - 2 * q| / (6 * u) + 1 / (4 * u ^ ((3 : ℝ) / 2)) ≤ 1 / (6 * ρ ^ 2) + 1 / ρ ^ 3 := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hu0 : 0 < u := by linarith
  have herr1 : |1 - 2 * q| / (6 * u) ≤ 1 / (6 * ρ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg (1 - 2 * q), mul_le_mul_of_nonneg_right hA hρ2.le]
  have hsu : ρ / 2 ≤ Real.sqrt u := by
    rw [show ρ / 2 = Real.sqrt ((ρ / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have herr2 : 1 / (4 * u ^ ((3 : ℝ) / 2)) ≤ 1 / ρ ^ 3 := by
    rw [rpow_three_halves_eq hu0]
    apply one_div_le_one_div_of_le (by positivity)
    have := mul_le_mul hu1 hsu (by positivity) hu0.le
    nlinarith
  linarith

/-- `1/(40ρ) ≤ 1/(16ρ) − 1/(6ρ²) − 1/ρ³` for `ρ ≥ 8` (source §6: `1/16 − 1/48 − 1/75 > 1/40`). -/
theorem good_const {ρ : ℝ} (hρ8 : 8 ≤ ρ) :
    1 / (40 * ρ) ≤ 1 / (16 * ρ) - 1 / (6 * ρ ^ 2) - 1 / ρ ^ 3 := by
  have hρ : 0 < ρ := by linarith
  have key : 1 / (16 * ρ) - 1 / (6 * ρ ^ 2) - 1 / ρ ^ 3 - 1 / (40 * ρ) =
      (3 / 80 * ρ ^ 2 - ρ / 6 - 1) / ρ ^ 3 := by
    field_simp
    ring
  have hk : 0 ≤ (3 / 80 * ρ ^ 2 - ρ / 6 - 1) / ρ ^ 3 :=
    div_nonneg (by nlinarith) (by positivity)
  linarith

/-- Off the good event the Chebyshev–Markov factor `1 − 4(t − 1)² − (2/(3ρ²)) d²` is `≤ 0`. -/
theorem good_factor_nonpos {t d ρ : ℝ} (hρ : 0 < ρ)
    (hA : ¬ (1 / 2 ≤ t ∧ t ≤ 2 ∧ d ^ 2 ≤ 3 * ρ ^ 2 / 2)) :
    1 - 4 * (t - 1) ^ 2 - 2 / (3 * ρ ^ 2) * d ^ 2 ≤ 0 := by
  have hd : 0 ≤ 2 / (3 * ρ ^ 2) * d ^ 2 := by positivity
  rcases lt_or_ge t (1 / 2) with h1 | h1
  · nlinarith [sq_nonneg (1 / 2 - t)]
  rcases lt_or_ge 2 t with h2 | h2
  · nlinarith [sq_nonneg (t - 2)]
  have h3 : 3 * ρ ^ 2 / 2 < d ^ 2 := by
    by_contra h
    push_neg at h
    exact hA ⟨h1, h2, h⟩
  have h4 : 1 < 2 / (3 * ρ ^ 2) * d ^ 2 := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    linarith
  nlinarith [sq_nonneg (t - 1)]

/-- **The binomial mass on the good event** (source §6), in pointwise form: on every atom,
`b_M(j) ≥ (1/(40ρ)) (1 − 4(M/m − 1)² − (2/(3ρ²)) δ²)`. -/
theorem binom_ge_good (hF : FourierEstimates) {q m ρ : ℝ} (hq : 1 / 4 ≤ q ∧ q ≤ 7 / 10)
    (hm : 0 < m) (hρ : 0 < ρ) (hρs : ρ ^ 2 = q * (1 - q) * m) (hρ8 : 8 ≤ ρ) (hρ75 : 75 ≤ ρ ^ 2)
    (M : ℕ) (j : ℤ) :
    1 / (40 * ρ) * (1 - 4 * ((M : ℝ) / m - 1) ^ 2 - 2 / (3 * ρ ^ 2) * ((j : ℝ) - q * M) ^ 2) ≤
      binom M q j := by
  obtain ⟨hq1, hq2⟩ := hq
  have hq0 : 0 < q := by linarith
  have hq1' : q < 1 := by linarith
  have hb0 := binom_nonneg (M := M) hq0.le hq1'.le j
  have hc : 0 < 1 / (40 * ρ) := by positivity
  by_cases hA : 1 / 2 ≤ (M : ℝ) / m ∧ (M : ℝ) / m ≤ 2 ∧ ((j : ℝ) - q * M) ^ 2 ≤ 3 * ρ ^ 2 / 2
  · obtain ⟨h1, h2, h3⟩ := hA
    have hut : (M : ℝ) * (q * (1 - q)) = ρ ^ 2 * ((M : ℝ) / m) := by
      rw [hρs]; field_simp
    have hu1 : ρ ^ 2 / 2 ≤ ρ ^ 2 * ((M : ℝ) / m) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ρ)]
    have hu2 : ρ ^ 2 * ((M : ℝ) / m) ≤ 2 * ρ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ρ)]
    have hu25 : 25 ≤ (M : ℝ) * (q * (1 - q)) := by rw [hut]; linarith
    obtain ⟨hmass, -⟩ := hF M q hq0 hq1' j hu25
    rw [hut] at hmass
    have hφ := gaussPhi_ge_of_good hρ hu1 hu2 h3
    have hA2 : |1 - 2 * q| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have herr := mass_err_le_of_good (q := q) hρ hA2 hu1
    have hg := good_const hρ8
    have habs := (abs_le.mp hmass).1
    have hb : 1 / (40 * ρ) ≤ binom M q j := by linarith
    have hfac : 1 - 4 * ((M : ℝ) / m - 1) ^ 2 - 2 / (3 * ρ ^ 2) * ((j : ℝ) - q * M) ^ 2 ≤ 1 := by
      have : 0 ≤ 2 / (3 * ρ ^ 2) * ((j : ℝ) - q * M) ^ 2 := by positivity
      nlinarith [sq_nonneg ((M : ℝ) / m - 1)]
    calc 1 / (40 * ρ) * (1 - 4 * ((M : ℝ) / m - 1) ^ 2 - 2 / (3 * ρ ^ 2) * ((j : ℝ) - q * M) ^ 2)
        ≤ 1 / (40 * ρ) * 1 := mul_le_mul_of_nonneg_left hfac hc.le
      _ ≤ binom M q j := by linarith
  · have := mul_nonpos_of_nonneg_of_nonpos hc.le (good_factor_nonpos hρ hA)
    linarith

end Erdos993Lean.Analytic.LargeMean
