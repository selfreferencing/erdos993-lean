import Erdos993Lean.Analytic.LargeMean.Pointwise

/-!
# The large-mean no-valley theorem (`m ≥ 400`)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F2.
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` (§1 conclusion form, §3–§6),
constants `check_large_mean_400.py`.

**Main result.** `noValleyAt_of_largeMean`: assuming the binomial Fourier estimates
(`FourierEstimates`, lane F1), for `q ∈ [1/4, 7/10]`, `m ≥ 400`, `0 ≤ D ≤ 8/5`, either
(i) `q ∈ [3/8, 8/13]` and `θ ≤ 7/10` or (ii) `q ≤ 3/8` or `q ≥ 8/13` and `θ ≤ 1`, and a tail
cutoff `r < M1` with `r + 1 ≥ m/3` and `T r ≤ e^{−m/30}`, the no-valley property
`NoValleyAt q m θ D T M1` holds.  (`θ ≥ 0` is not used; `E δ = 0` is not used.)

**Proof.** A weak valley gives `E κ ≤ 0` (`LargeMean.expect_kappa_nonpos`).  Put `ρ = √s`,
`s = q(1 − q)m ≥ 75`.  Pointwise on every atom (`kappa_ge_central`, `kappa_ge_outer`):
`κ = f_C + ((1 − 2q)²/(q(1 − q))) b ≥ f_C ≥ curvMinorant(M/m) − (a₀/ρ⁵) δ² − 2·1[M ≤ r]`, and in
case (ii) additionally `((1 − 2q)²/(q(1 − q))) b ≥ (9/40)(1/(40ρ))(1 − 4(M/m − 1)² − (2/(3ρ²))δ²)`.
Averaging (`LargeMean.expect_ge_of_pointwise`) with `E(M/m − 1) = 0`, `Var M ≤ Dm`,
`E δ² ≤ θ s`, `P(M ≤ r) ≤ e^{−m/30}` gives a lower bound for `E κ` that is positive by
`central_final` (source §5: `E f_C > 0`) resp. `outer_final` (source §6: the binomial drift).

**Names.**  Only `gaussPhi`, `gaussCurv`, `FourierEstimates` (`Interface.lean`) and
`noValleyAt_of_largeMean` live in `Erdos993Lean.Analytic`; every auxiliary lemma of the lane is in
the namespace `Erdos993Lean.Analytic.LargeMean`, so that merging with other lanes cannot clash.

**Scalarity check.**  `D` summarizes the variance of the free count `M` (`Var M ≤ Dm`, produced
by O1, consumed in the averaging step through `Var M/m² ≤ D/m`); `θ` summarizes the second moment
of `δ` (`E δ² ≤ θ q(1 − q)m`, O2, consumed through `ν E δ² ≤ ν θ s` with the single
`M`-independent multiplier `ν`); `T`, `M1`, `r` summarize the lower tail of `M` (O3, consumed
through `P(M ≤ r) ≤ e^{−m/30}`); `m = E M` (O5) fixes `s`.  The band edges `3/8`, `8/13`, `7/10`
and all rational margins are outputs of this file; the consumer is `NoValleyAt` (O4).
-/

namespace Erdos993Lean.Analytic.LargeMean

theorem qv_bounds {q : ℝ} (hq : 1 / 4 ≤ q ∧ q ≤ 7 / 10) :
    3 / 16 ≤ q * (1 - q) ∧ q * (1 - q) ≤ 1 / 4 := by
  obtain ⟨h1, h2⟩ := hq
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ q - 1 / 4) (by linarith : (0:ℝ) ≤ 3 / 4 - q)]
  · nlinarith [sq_nonneg (q - 1 / 2)]

theorem rho_bounds {q m ρ : ℝ} (hq : 1 / 4 ≤ q ∧ q ≤ 7 / 10) (hm : 400 ≤ m) (hρ : 0 < ρ)
    (hρs : ρ ^ 2 = q * (1 - q) * m) : 75 ≤ ρ ^ 2 ∧ 8 ≤ ρ ∧ ρ ^ 2 ≤ m / 4 := by
  obtain ⟨hv, hv4⟩ := qv_bounds hq
  have h75 : 75 ≤ ρ ^ 2 := by rw [hρs]; nlinarith
  refine ⟨h75, by nlinarith, ?_⟩
  rw [hρs]; nlinarith

/-- On the outer bands `(1 − 2q)²/(q(1 − q)) ≥ 9/40` (source §6). -/
theorem outer_coeff {q : ℝ} (hq : 1 / 4 ≤ q ∧ q ≤ 7 / 10) (hqout : q ≤ 3 / 8 ∨ 8 / 13 ≤ q) :
    9 / 40 ≤ (1 - 2 * q) ^ 2 / (q * (1 - q)) := by
  obtain ⟨h1, h2⟩ := hq
  have hvpos : 0 < q * (1 - q) := mul_pos (by linarith) (by linarith)
  rw [le_div_iff₀ hvpos]
  rcases hqout with h | h
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 / 8 - q) (by linarith : (0:ℝ) ≤ 5 / 8 - q)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ q - 8 / 13) (by linarith : (0:ℝ) ≤ q - 5 / 13)]

/-- The pointwise kernel bound of the central case: `κ ≥ f_C ≥ lmA + lmB(t − 1) − lmC(t − 1)²
− (a₀/ρ⁵) δ² − 2·1[M ≤ r]` with `t = M/m`, `δ = k − Y − qM`. -/
theorem kappa_ge_central (hF : FourierEstimates) {q m ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hm : 0 < m) (hρ : 0 < ρ) (hρs : ρ ^ 2 = q * (1 - q) * m) (hρ75 : 75 ≤ ρ ^ 2) {r : ℕ}
    (hr : m / 3 ≤ (r : ℝ) + 1) (k : ℤ) (M Y : ℕ) :
    lmA q ρ + lmB q ρ * ((M : ℝ) / m - 1) - lmC q ρ * ((M : ℝ) / m - 1) ^ 2
      - gaussA0 / ρ ^ 5 * delta q k M Y ^ 2 - 2 * (if M ≤ r then 1 else 0) ≤
      kappa q M (k - Y) := by
  have h1 := fC_ge_curvMinorant_sub hF hq0 hq1 hm hρ hρs hρ75 hr M (k - Y)
  have hd : ((k - (Y : ℤ) : ℤ) : ℝ) - q * (M : ℝ) = delta q k M Y := by
    unfold delta; push_cast; ring
  rw [hd, curvMinorant_eq] at h1
  have h2 := kappa_eq hq0 hq1 M (k - Y)
  have h3 := binom_nonneg (M := M) hq0.le hq1.le (k - Y)
  have h4 : 0 ≤ (1 - 2 * q) ^ 2 / (q * (1 - q)) * binom M q (k - Y) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (mul_pos hq0 (by linarith)).le) h3
  linarith

/-- The pointwise kernel bound of the outer case: the central bound plus the drift term
`(9/40) b ≥ (9/1600ρ)(1 − 4(t − 1)² − (2/(3ρ²)) δ²)`. -/
theorem kappa_ge_outer (hF : FourierEstimates) {q m ρ : ℝ} (hq : 1 / 4 ≤ q ∧ q ≤ 7 / 10)
    (hm : 0 < m) (hρ : 0 < ρ) (hρs : ρ ^ 2 = q * (1 - q) * m) (hρ8 : 8 ≤ ρ) (hρ75 : 75 ≤ ρ ^ 2)
    {r : ℕ} (hr : m / 3 ≤ (r : ℝ) + 1) (hcb : 9 / 40 ≤ (1 - 2 * q) ^ 2 / (q * (1 - q)))
    (k : ℤ) (M Y : ℕ) :
    (lmA q ρ + 9 / (1600 * ρ)) + lmB q ρ * ((M : ℝ) / m - 1)
      - (lmC q ρ + 36 / (1600 * ρ)) * ((M : ℝ) / m - 1) ^ 2
      - (gaussA0 / ρ ^ 5 + 6 / (1600 * ρ ^ 3)) * delta q k M Y ^ 2
      - 2 * (if M ≤ r then 1 else 0) ≤ kappa q M (k - Y) := by
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : q < 1 := by linarith [hq.2]
  have h1 := fC_ge_curvMinorant_sub hF hq0 hq1 hm hρ hρs hρ75 hr M (k - Y)
  have hd : ((k - (Y : ℤ) : ℤ) : ℝ) - q * (M : ℝ) = delta q k M Y := by
    unfold delta; push_cast; ring
  rw [hd, curvMinorant_eq] at h1
  have h2 := kappa_eq hq0 hq1 M (k - Y)
  have h3 := binom_nonneg (M := M) hq0.le hq1.le (k - Y)
  have h4 := mul_le_mul_of_nonneg_right hcb h3
  have h5 := binom_ge_good hF hq hm hρ hρs hρ8 hρ75 M (k - Y)
  rw [hd] at h5
  have hρne : ρ ≠ 0 := hρ.ne'
  have e : 9 / 40 * (1 / (40 * ρ) * (1 - 4 * ((M : ℝ) / m - 1) ^ 2
      - 2 / (3 * ρ ^ 2) * delta q k M Y ^ 2)) =
      9 / (1600 * ρ) - 36 / (1600 * ρ) * ((M : ℝ) / m - 1) ^ 2
      - 6 / (1600 * ρ ^ 3) * delta q k M Y ^ 2 := by
    field_simp
    ring
  linarith

/-- The central case is positive (source §5, `E f_C > 0`): with `ε = D/m` and
`E₀ = e^{−m/30}`, `lmA − lmC ε − (a₀/ρ⁵)(θρ²) − 2E₀ > 0`. -/
theorem central_final {q ρ θ ε E0 : ℝ} (hρ8 : 8 ≤ ρ) (hρ75 : 75 ≤ ρ ^ 2)
    (hA : |1 - 2 * q| ≤ 1 / 4) (hθ : θ ≤ 7 / 10) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 250)
    (hE : 2 * E0 * ρ ^ 3 ≤ 1 / 250) :
    0 < lmA q ρ - lmC q ρ * ε - gaussA0 / ρ ^ 5 * (θ * ρ ^ 2) - 2 * E0 := by
  have hρ0 : 0 < ρ := by linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hM := central_margin gaussA0_gt.le hθ hε0 hε hρ8 hρ75 hA hE
  have hid : (lmA q ρ - lmC q ρ * ε - gaussA0 / ρ ^ 5 * (θ * ρ ^ 2) - 2 * E0) * ρ ^ 3 =
      gaussA0 * (1 - θ - 20 * ε) - 2 / 3 * |1 - 2 * q| * (1 + 15 * ε) / ρ
        - (1 + 30 * ε) / ρ ^ 2 - 2 * E0 * ρ ^ 3 := by
    unfold lmA lmC
    field_simp
    ring
  have hρ3 : 0 < ρ ^ 3 := by positivity
  by_contra hcon
  push_neg at hcon
  have := mul_nonpos_of_nonneg_of_nonpos hρ3.le hcon
  linarith

/-- The outer case is positive (source §6): the binomial drift beats the curvature deficit. -/
theorem outer_final {q ρ θ ε E0 : ℝ} (hρ8 : 8 ≤ ρ) (hρ75 : 75 ≤ ρ ^ 2)
    (hA : |1 - 2 * q| ≤ 1 / 2) (hθ : θ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 250)
    (hE : 2 * E0 * ρ ^ 3 ≤ 1 / 250) :
    0 < (lmA q ρ + 9 / (1600 * ρ)) - (lmC q ρ + 36 / (1600 * ρ)) * ε
      - (gaussA0 / ρ ^ 5 + 6 / (1600 * ρ ^ 3)) * (θ * ρ ^ 2) - 2 * E0 := by
  have hρ0 : 0 < ρ := by linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hM := outer_margin gaussA0_pos.le gaussA0_lt.le hθ hε0 hε hρ8 hρ75 hA hE
  have hid : ((lmA q ρ + 9 / (1600 * ρ)) - (lmC q ρ + 36 / (1600 * ρ)) * ε
      - (gaussA0 / ρ ^ 5 + 6 / (1600 * ρ ^ 3)) * (θ * ρ ^ 2) - 2 * E0) * ρ ^ 3 =
      gaussA0 * (1 - θ - 20 * ε) - 2 / 3 * |1 - 2 * q| * (1 + 15 * ε) / ρ
        - (1 + 30 * ε) / ρ ^ 2 - 2 * E0 * ρ ^ 3
        + 9 / 1600 * ρ ^ 2 * (1 - 4 * ε - 2 * θ / 3) := by
    unfold lmA lmC
    field_simp
    ring
  have hρ3 : 0 < ρ ^ 3 := by positivity
  by_contra hcon
  push_neg at hcon
  have := mul_nonpos_of_nonneg_of_nonpos hρ3.le hcon
  linarith

end Erdos993Lean.Analytic.LargeMean

namespace Erdos993Lean.Analytic

open LargeMean in
/-- **The large-mean no-valley theorem** (Soul's `LARGE_MEAN_400_PROOF.md`), conditional on the
binomial Fourier estimates `FourierEstimates` (lane F1): for `q ∈ [1/4, 7/10]`, `m ≥ 400`,
`0 ≤ D ≤ 8/5`, either `q ∈ [3/8, 8/13]` with `θ ≤ 7/10` or `q ∉ (3/8, 8/13)` with `θ ≤ 1`, and a
tail cutoff `r < M1` with `m/3 ≤ r + 1` and `T r ≤ e^{−m/30}`, every probability mixture with the
moment and tail inputs of `NoValleyAt` has no weak valley. -/
theorem noValleyAt_of_largeMean (hF : FourierEstimates)
    {q m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ}
    (hq : 1 / 4 ≤ q ∧ q ≤ 7 / 10) (hm : 400 ≤ m) (hD : D ≤ 8 / 5)
    (hθ : (3 / 8 ≤ q ∧ q ≤ 8 / 13 ∧ θ ≤ 7 / 10) ∨ ((q ≤ 3 / 8 ∨ 8 / 13 ≤ q) ∧ θ ≤ 1))
    (hθ0 : 0 ≤ θ) (hD0 : 0 ≤ D)
    (htail : ∃ r : ℕ, r < M1 ∧ m / 3 ≤ (r : ℝ) + 1 ∧ T r ≤ Real.exp (-(m / 30))) :
    NoValleyAt q m θ D T M1 := by
  intro ι X k hP hmean _ hδ2 hvar hT hV
  obtain ⟨r, hrM1, hr3, hTr⟩ := htail
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : q < 1 := by linarith [hq.2]
  have h1q : 0 < 1 - q := by linarith
  have hm0 : 0 < m := by linarith
  obtain ⟨ρ, hρ0, hρs⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = q * (1 - q) * m :=
    ⟨Real.sqrt (q * (1 - q) * m), Real.sqrt_pos.mpr (mul_pos (mul_pos hq0 h1q) hm0),
      Real.sq_sqrt (mul_pos (mul_pos hq0 h1q) hm0).le⟩
  obtain ⟨hρ75, hρ8, hρm⟩ := rho_bounds hq hm hρ0 hρs
  have hcdf : X.cdfM r ≤ Real.exp (-(m / 30)) := (hT r hrM1).trans hTr
  have hκ := expect_kappa_nonpos X hq0 hq1 hV
  have hvarm : X.varM / m ^ 2 ≤ D / m := by
    rw [div_le_div_iff₀ (by positivity) hm0]
    linarith [mul_le_mul_of_nonneg_right hvar hm0.le]
  have hε0 : 0 ≤ D / m := div_nonneg hD0 hm0.le
  have hε : D / m ≤ 1 / 250 := by rw [div_le_iff₀ hm0]; linarith
  have hE := tail_term_le hm hρ0 hρm
  have hδ2' : X.expect (fun M Y => delta q k M Y ^ 2) ≤ θ * ρ ^ 2 := by rw [hρs]; linarith
  have hμ0 : 0 ≤ gaussA0 / ρ ^ 5 := by have := gaussA0_pos; positivity
  rcases hθ with ⟨hq38, hq813, hθ7⟩ | ⟨hqout, hθ1⟩
  · -- the central band: already `E f_C > 0`
    have hA : |1 - 2 * q| ≤ 1 / 4 := by rw [abs_le]; constructor <;> linarith
    have hE' := expect_ge_of_pointwise X hP hmean hm0.ne' (fun M Y => kappa q M (k - Y))
      (fun M Y => delta q k M Y ^ 2) r (lmA q ρ) (lmB q ρ) (lmC q ρ) (gaussA0 / ρ ^ 5) 2
      (fun σ _ => kappa_ge_central hF hq0 hq1 hm0 hρ0 hρs hρ75 hr3 k (X.M σ) (X.Y σ))
    have t1 := mul_le_mul_of_nonneg_left hvarm (lmC_nonneg q hρ0)
    have t2 := mul_le_mul_of_nonneg_left hδ2' hμ0
    have hX := central_final hρ8 hρ75 hA hθ7 hε0 hε hE
    linarith
  · -- the outer bands: the binomial drift term
    have hA : |1 - 2 * q| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [hq.1, hq.2]
    have hcb := outer_coeff hq hqout
    have hE' := expect_ge_of_pointwise X hP hmean hm0.ne' (fun M Y => kappa q M (k - Y))
      (fun M Y => delta q k M Y ^ 2) r (lmA q ρ + 9 / (1600 * ρ)) (lmB q ρ)
      (lmC q ρ + 36 / (1600 * ρ)) (gaussA0 / ρ ^ 5 + 6 / (1600 * ρ ^ 3)) 2
      (fun σ _ => kappa_ge_outer hF hq hm0 hρ0 hρs hρ8 hρ75 hr3 hcb k (X.M σ) (X.Y σ))
    have hc0 : 0 ≤ lmC q ρ + 36 / (1600 * ρ) := by
      have := lmC_nonneg q hρ0; positivity
    have hν0 : 0 ≤ gaussA0 / ρ ^ 5 + 6 / (1600 * ρ ^ 3) := add_nonneg hμ0 (by positivity)
    have t1 := mul_le_mul_of_nonneg_left hvarm hc0
    have t2 := mul_le_mul_of_nonneg_left hδ2' hν0
    have hX := outer_final hρ8 hρ75 hA hθ1 hε0 hε hE
    linarith

end Erdos993Lean.Analytic
