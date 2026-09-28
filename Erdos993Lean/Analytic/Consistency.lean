import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.Translate

/-!
# Monotonicity of T1's explicit threshold condition in `θ` and `D`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A5; interface `Analytic/Defs.lean`
(`ExplicitThreshold`, `ThresholdNumerics`).  Source: T1's explicit threshold (campaign report
`ProofRuns/2026-09-27_zhang_review/reports/T1.md`, Theorem 3.1, Lemma 5.1, Theorem 6.1).

In `ExplicitThreshold q m θ D T M1` the parameters `θ` (the second-moment ratio of `δ`) and `D`
(the variance ratio of the free count `M`) enter only the final strict inequality
`ν θ q(1 − q) m < α − γ D m − ∑ …`, on the side where decreasing them helps (`ν > 0`, `γ ≥ 0`), as
long as `q(1 − q) m ≥ 0` and `m ≥ 0`.  So a certificate at `(θ, D)` is a certificate at every
smaller `(θ', D')`, with the same witnesses:

* `thresholdNumerics_mono`: `ExplicitThreshold q m θ D T M1 → θ' ≤ θ → D' ≤ D → 0 ≤ q → q ≤ 1 →
  0 ≤ m → ExplicitThreshold q m θ' D' T M1`;
* `thresholdNumerics_mono_profile`: the profile form, `ThresholdNumerics P → ThresholdNumerics P'`
  when `P'` has pointwise smaller `θb`, `Db` on the range, a pointwise larger nonnegative
  `mfloor`, and the same tail data `Tb`, `M1b`.
-/

namespace Erdos993Lean.Analytic

/-- **Monotonicity of T1's explicit threshold in `θ` and `D`.**  For `0 ≤ q ≤ 1` and `m ≥ 0`, the
explicit threshold condition at `(θ, D)` implies it at every `(θ', D')` with `θ' ≤ θ` and `D' ≤ D`
(same multipliers, fibre bound, minorant and tail prices). -/
theorem thresholdNumerics_mono {q m θ D θ' D' : ℝ} {T : ℕ → ℝ} {M1 : ℕ}
    (h : ExplicitThreshold q m θ D T M1) (hθ : θ' ≤ θ) (hD : D' ≤ D)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hm : 0 ≤ m) : ExplicitThreshold q m θ' D' T M1 := by
  obtain ⟨ν, c, α, β, γ, hf, S, hν, hγ, hfib, hmin, hS, hS0, hSmono, hlt⟩ := h
  refine ⟨ν, c, α, β, γ, hf, S, hν, hγ, hfib, hmin, hS, hS0, hSmono, ?_⟩
  have hqq : 0 ≤ q * (1 - q) * m := by
    have : 0 ≤ 1 - q := by linarith
    positivity
  have h1 : ν * θ' * (q * (1 - q)) * m ≤ ν * θ * (q * (1 - q)) * m := by
    have e1 : ν * θ' * (q * (1 - q)) * m = (ν * θ') * (q * (1 - q) * m) := by ring
    have e2 : ν * θ * (q * (1 - q)) * m = (ν * θ) * (q * (1 - q) * m) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ hν.le) hqq
  have h2 : γ * D' * m ≤ γ * D * m :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hγ) hm
  linarith

/-- **Profile form of `thresholdNumerics_mono`.**  The threshold numerics (O4) for a profile `P`
give them for a profile `P'` with the same tail data, smaller `θb` and `Db` on the range, and a
larger nonnegative floor `mfloor`. -/
theorem thresholdNumerics_mono_profile {P P' : Profile} (h : ThresholdNumerics P)
    (hθ : ∀ t, InRange t → P'.θb t ≤ P.θb t) (hD : ∀ t, InRange t → P'.Db t ≤ P.Db t)
    (hT : P'.Tb = P.Tb) (hM1 : P'.M1b = P.M1b)
    (hmf : ∀ t, InRange t → P.mfloor t ≤ P'.mfloor t)
    (hmf0 : ∀ t, InRange t → 0 ≤ P'.mfloor t) : ThresholdNumerics P' := by
  intro t hR m hm
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  have hET := h t hR m (le_trans (hmf t hR) hm)
  rw [hT, hM1]
  exact thresholdNumerics_mono hET (hθ t hR) (hD t hR) (actQ_pos ht).le (actQ_lt_one ht.le).le
    (le_trans (hmf0 t hR) hm)

/-- **The bounded-`m` route to O4**: T1 (`T1Core`) turns the threshold numerics into the no-valley
property on the whole parameter domain of the profile. -/
theorem thresholdNoValley_of_numerics (hT1 : T1Core) {P : Profile} (h : ThresholdNumerics P) :
    ThresholdNoValley P := by
  intro t hR m hm
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  exact hT1 _ _ _ _ _ _ (by unfold actQ; positivity)
    (by unfold actQ; rw [div_lt_one (by linarith)]; linarith) (h t hR m hm)

end Erdos993Lean.Analytic
