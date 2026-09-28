import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Binom

/-!
# T1's explicit threshold as a finite check (extra E1)

Source: T1 (`ProofRuns/2026-09-27_zhang_review/reports/T1.md`), §5 (last line: "for large `M` one
uses `h(M) ≥ −c²/(4aμ̃) − max_j |κ(M, j)|` (bounded) while `π → −∞`") and §10 (iii) ("the large-`M`
tail of Lemma 5.1 in closed form; routine").  The threshold condition is `ExplicitThreshold` of
`Erdos993Lean/Analytic/Defs.lean` (with `ν = a μ̃`).

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

* **Finite range of the kernel.** `kappa_of_lt`, `kappa_of_gt`, `kappa_eq_zero_of_not_mem`:
  `κ(M, j) = 0` for `j < −1` and for `j > M + 1`.
* **Finite-range reduction** (`pointwise_of_range`): the pointwise fibre condition
  `h(M) ≤ κ(M, j) + cδ + νδ²` (`δ = j − qM`) holds for every `j ∈ ℤ` as soon as it holds for
  `−1 ≤ j ≤ M + 1` and `h(M) ≤ −c²/(4ν)` (because `cδ + νδ² ≥ −c²/(4ν)`, `quad_lower_bound`).
* **Closed-form large-`M` fallback.** `abs_kappa_le`: `|κ(M, j)| ≤ 1/q + 1/(1 − q)`; hence
  `fibreFallback q c ν = −c²/(4ν) − 1/q − 1/(1 − q)` is a valid pointwise fibre bound for every `M`
  (`fibreFallback_le`).
* **Explicit `M_big`** (`quadBig`, `quad_le_of_quadBig_le`): for `γ > 0`,
  `π(x) = α + β(x − m) − γ(x − m)² ≤ H` for every real `x ≥ M_big := m + 1 + 2(|β| + |α − H|)/γ`.
* **The threshold with the fallback** (`explicitThreshold_of_pointwise`): with `h = h₀` below an
  integer `Mb ≥ M_big(α, β, γ, m; fibreFallback)` and `h = fibreFallback` from `Mb` on, the
  condition `ExplicitThreshold` follows from conditions on `M < Mb` only.
* **The threshold as a finite check** (`explicitThreshold_of_finite`): the same from finitely many
  inequalities: the pointwise condition for `M < Mb`, `−1 ≤ j ≤ M + 1`; `h₀(M) ≤ −c²/(4ν)` for
  `M < Mb`; `π ≤ h₀` on `[M1, Mb)`; the tail prices on `[0, M1)`; and the strict threshold
  inequality.
-/

namespace Erdos993Lean.Analytic.NoValley

open Finset

/-! ## The kernel vanishes outside `[−1, M + 1]` -/

theorem kappa_of_lt {q : ℝ} {M : ℕ} {j : ℤ} (hj : j < -1) : kappa q M j = 0 := by
  unfold kappa
  rw [binom_of_neg (by omega : j < 0), binom_of_neg (by omega : j - 1 < 0),
    binom_of_neg (by omega : j + 1 < 0)]
  ring

theorem kappa_of_gt {q : ℝ} {M : ℕ} {j : ℤ} (hj : (M : ℤ) + 1 < j) : kappa q M j = 0 := by
  unfold kappa
  rw [binom_of_gt (by omega : (M : ℤ) < j), binom_of_gt (by omega : (M : ℤ) < j - 1),
    binom_of_gt (by omega : (M : ℤ) < j + 1)]
  ring

theorem kappa_eq_zero_of_not_mem {q : ℝ} {M : ℕ} {j : ℤ} (hj : ¬ (-1 ≤ j ∧ j ≤ (M : ℤ) + 1)) :
    kappa q M j = 0 := by
  rcases lt_or_ge j (-1) with h | h
  · exact kappa_of_lt h
  · exact kappa_of_gt (by omega)

/-! ## The quadratic penalty and the finite-range reduction -/

/-- `cδ + νδ² ≥ −c²/(4ν)` for `ν > 0`. -/
theorem quad_lower_bound {ν : ℝ} (hν : 0 < ν) (c x : ℝ) : -c ^ 2 / (4 * ν) ≤ c * x + ν * x ^ 2 := by
  have h0 : 0 ≤ ν * (x + c / (2 * ν)) ^ 2 := mul_nonneg hν.le (sq_nonneg _)
  have e : ν * (x + c / (2 * ν)) ^ 2 = c * x + ν * x ^ 2 - (-c ^ 2 / (4 * ν)) := by
    field_simp
    ring
  linarith

/-- **Finite-range reduction of the pointwise fibre condition (E1).**  Since `κ(M, j) = 0` for
`j < −1` and `j > M + 1`, the pointwise condition `h(M) ≤ κ(M, j) + cδ + νδ²` holds for every integer
`j` as soon as it holds for `−1 ≤ j ≤ M + 1` and `h(M) ≤ −c²/(4ν)`. -/
theorem pointwise_of_range {q ν c : ℝ} (hν : 0 < ν) {M : ℕ} {hM : ℝ}
    (hout : hM ≤ -c ^ 2 / (4 * ν))
    (hin : ∀ j : ℤ, -1 ≤ j → j ≤ (M : ℤ) + 1 →
      hM ≤ kappa q M j + c * ((j : ℝ) - q * M) + ν * ((j : ℝ) - q * M) ^ 2) (j : ℤ) :
    hM ≤ kappa q M j + c * ((j : ℝ) - q * M) + ν * ((j : ℝ) - q * M) ^ 2 := by
  by_cases hj : -1 ≤ j ∧ j ≤ (M : ℤ) + 1
  · exact hin j hj.1 hj.2
  · rw [kappa_eq_zero_of_not_mem hj, zero_add]
    have := quad_lower_bound hν c ((j : ℝ) - q * M)
    linarith

/-! ## The closed-form large-`M` fallback -/

/-- `|κ(M, j)| ≤ 1/q + 1/(1 − q)`: both `f_L` and `f_R` are differences of two numbers in `[0, 1]`. -/
theorem abs_kappa_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) (j : ℤ) :
    |kappa q M j| ≤ 1 / q + 1 / (1 - q) := by
  have hq1' : 0 < 1 - q := sub_pos.mpr hq1
  have b0 := binom_nonneg (M := M) hq0.le hq1.le j
  have b1 := binom_le_one (M := M) hq0.le hq1.le j
  have bm0 := binom_nonneg (M := M) hq0.le hq1.le (j - 1)
  have bm1 := binom_le_one (M := M) hq0.le hq1.le (j - 1)
  have bp0 := binom_nonneg (M := M) hq0.le hq1.le (j + 1)
  have bp1 := binom_le_one (M := M) hq0.le hq1.le (j + 1)
  have t1 : 0 ≤ (1 - q) * binom M q j := mul_nonneg hq1'.le b0
  have t2 : (1 - q) * binom M q j ≤ 1 := by nlinarith
  have t3 : 0 ≤ q * binom M q (j - 1) := mul_nonneg hq0.le bm0
  have t4 : q * binom M q (j - 1) ≤ 1 := by nlinarith
  have t5 : 0 ≤ q * binom M q j := mul_nonneg hq0.le b0
  have t6 : q * binom M q j ≤ 1 := by nlinarith
  have t7 : 0 ≤ (1 - q) * binom M q (j + 1) := mul_nonneg hq1'.le bp0
  have t8 : (1 - q) * binom M q (j + 1) ≤ 1 := by nlinarith
  have hL : |(1 - q) * binom M q j - q * binom M q (j - 1)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hR : |q * binom M q j - (1 - q) * binom M q (j + 1)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  unfold kappa
  calc |((1 - q) * binom M q j - q * binom M q (j - 1)) / q +
        (q * binom M q j - (1 - q) * binom M q (j + 1)) / (1 - q)|
      ≤ |((1 - q) * binom M q j - q * binom M q (j - 1)) / q| +
          |(q * binom M q j - (1 - q) * binom M q (j + 1)) / (1 - q)| := abs_add_le _ _
    _ = |(1 - q) * binom M q j - q * binom M q (j - 1)| / q +
          |q * binom M q j - (1 - q) * binom M q (j + 1)| / (1 - q) := by
        rw [abs_div, abs_div, abs_of_pos hq0, abs_of_pos hq1']
    _ ≤ 1 / q + 1 / (1 - q) := by
        gcongr

/-- The closed-form fibre bound `−c²/(4ν) − 1/q − 1/(1 − q)` (T1 §5, last line; §10 (iii)). -/
noncomputable def fibreFallback (q c ν : ℝ) : ℝ := -c ^ 2 / (4 * ν) - 1 / q - 1 / (1 - q)

/-- **The fallback is a valid pointwise fibre bound for every `M`.** -/
theorem fibreFallback_le {q ν : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hν : 0 < ν) (c : ℝ) (M : ℕ)
    (j : ℤ) :
    fibreFallback q c ν ≤ kappa q M j + c * ((j : ℝ) - q * M) + ν * ((j : ℝ) - q * M) ^ 2 := by
  have h1 := quad_lower_bound hν c ((j : ℝ) - q * M)
  have h2 := neg_abs_le (kappa q M j)
  have h3 := abs_kappa_le hq0 hq1 M j
  unfold fibreFallback
  linarith

/-! ## The explicit `M_big` -/

/-- `M_big(α, β, γ, m; H) = m + 1 + 2(|β| + |α − H|)/γ`: beyond it the quadratic minorant
`π(x) = α + β(x − m) − γ(x − m)²` is below the level `H` (for `γ > 0`). -/
noncomputable def quadBig (α β γ m H : ℝ) : ℝ := m + 1 + 2 * (|β| + |α - H|) / γ

/-- **The quadratic minorant lies below any level from the explicit `M_big` on.** -/
theorem quad_le_of_quadBig_le {α β γ m H x : ℝ} (hγ : 0 < γ) (hx : quadBig α β γ m H ≤ x) :
    α + β * (x - m) - γ * (x - m) ^ 2 ≤ H := by
  set A := |α - H| with hA
  set B := |β| with hB
  have hA0 : 0 ≤ A := abs_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have hAα : α - H ≤ A := le_abs_self _
  have hBβ : β ≤ B := le_abs_self _
  set y := x - m with hy
  have hfrac : 0 ≤ 2 * (B + A) / γ := div_nonneg (by linarith) hγ.le
  have hy1 : 1 + 2 * (B + A) / γ ≤ y := by
    unfold quadBig at hx
    rw [hy]
    linarith
  have hy0 : 1 ≤ y := by linarith
  have hγy : γ + 2 * (B + A) ≤ γ * y := by
    have := mul_le_mul_of_nonneg_left hy1 hγ.le
    rwa [mul_add, mul_one, mul_div_cancel₀ _ hγ.ne'] at this
  have p1 : (γ + 2 * (B + A)) * y ≤ γ * y * y := mul_le_mul_of_nonneg_right hγy (by linarith)
  have p2 : 0 ≤ A * (y - 1) := mul_nonneg hA0 (by linarith)
  have p3 : 0 ≤ (B - β) * y := mul_nonneg (by linarith) (by linarith)
  have p4 : 0 ≤ γ * y := mul_nonneg hγ.le (by linarith)
  nlinarith

/-! ## The threshold condition as a finite check -/

/-- **T1's explicit threshold with the fallback beyond `Mb`.**  Let `Mb` be an integer with
`M1 ≤ Mb` and `Mb ≥ M_big(α, β, γ, m; fibreFallback q c ν)`, and use the fibre bound `h(M) = h₀(M)` for
`M < Mb`, `h(M) = −c²/(4ν) − 1/q − 1/(1 − q)` for `M ≥ Mb`.  Then `ExplicitThreshold q m θ D T M1`
follows from: the pointwise condition for `M < Mb` (all `j`); `π ≤ h₀` on `[M1, Mb)`; the tail prices
on `[0, M1)` (`π − h₀ ≤ S`, `S ≥ 0`, `S` nonincreasing); and the strict threshold inequality. -/
theorem explicitThreshold_of_pointwise {q m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ} (hq0 : 0 < q)
    (hq1 : q < 1) {ν c α β γ : ℝ} (h₀ S : ℕ → ℝ) (Mb : ℕ) (hν : 0 < ν) (hγ : 0 < γ)
    (hMb : quadBig α β γ m (fibreFallback q c ν) ≤ Mb) (hM1 : M1 ≤ Mb)
    (hpt : ∀ M : ℕ, M < Mb → ∀ j : ℤ,
      h₀ M ≤ kappa q M j + c * ((j : ℝ) - q * M) + ν * ((j : ℝ) - q * M) ^ 2)
    (hquad : ∀ M : ℕ, M1 ≤ M → M < Mb →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 ≤ h₀ M)
    (hS : ∀ M : ℕ, M < M1 → α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - h₀ M ≤ S M)
    (hS0 : ∀ M : ℕ, M < M1 → 0 ≤ S M) (hSmono : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M)
    (hthr : ν * θ * (q * (1 - q)) * m <
      α - γ * D * m - ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1))) :
    ExplicitThreshold q m θ D T M1 := by
  refine ⟨ν, c, α, β, γ, fun M => if M < Mb then h₀ M else fibreFallback q c ν, S, hν, hγ.le,
    ?_, ?_, ?_, hS0, hSmono, hthr⟩
  · intro M j
    by_cases hM : M < Mb
    · simp only [if_pos hM]
      exact hpt M hM j
    · simp only [if_neg hM]
      exact fibreFallback_le hq0 hq1 hν c M j
  · intro M hM
    by_cases hMb' : M < Mb
    · simp only [if_pos hMb']
      exact hquad M hM hMb'
    · simp only [if_neg hMb']
      refine quad_le_of_quadBig_le hγ (le_trans hMb ?_)
      exact_mod_cast not_lt.mp hMb'
  · intro M hM
    simp only [if_pos (lt_of_lt_of_le hM hM1)]
    exact hS M hM

/-- **T1's explicit threshold as a finite check (E1).**  As `explicitThreshold_of_pointwise`, with
the pointwise condition required only for `M < Mb` and `−1 ≤ j ≤ M + 1`, plus
`h₀(M) ≤ −c²/(4ν)` for `M < Mb` (finite range reduction, `pointwise_of_range`): every hypothesis is
a finite set of inequalities. -/
theorem explicitThreshold_of_finite {q m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    {ν c α β γ : ℝ} (h₀ S : ℕ → ℝ) (Mb : ℕ) (hν : 0 < ν) (hγ : 0 < γ)
    (hMb : quadBig α β γ m (fibreFallback q c ν) ≤ Mb) (hM1 : M1 ≤ Mb)
    (hin : ∀ M : ℕ, M < Mb → ∀ j : ℤ, -1 ≤ j → j ≤ (M : ℤ) + 1 →
      h₀ M ≤ kappa q M j + c * ((j : ℝ) - q * M) + ν * ((j : ℝ) - q * M) ^ 2)
    (hout : ∀ M : ℕ, M < Mb → h₀ M ≤ -c ^ 2 / (4 * ν))
    (hquad : ∀ M : ℕ, M1 ≤ M → M < Mb →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 ≤ h₀ M)
    (hS : ∀ M : ℕ, M < M1 → α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - h₀ M ≤ S M)
    (hS0 : ∀ M : ℕ, M < M1 → 0 ≤ S M) (hSmono : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M)
    (hthr : ν * θ * (q * (1 - q)) * m <
      α - γ * D * m - ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1))) :
    ExplicitThreshold q m θ D T M1 :=
  explicitThreshold_of_pointwise hq0 hq1 h₀ S Mb hν hγ hMb hM1
    (fun M hM j => pointwise_of_range hν (hout M hM) (hin M hM) j) hquad hS hS0 hSmono hthr

end Erdos993Lean.Analytic.NoValley
