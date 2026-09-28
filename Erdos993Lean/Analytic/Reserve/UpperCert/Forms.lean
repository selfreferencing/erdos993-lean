import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperDefs
import Erdos993Lean.Analytic.Reserve.Cert.Real

/-!
# O1's upper finite box: the normalized forms behind the cell checker (lane A15)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  Sources: the referee's independent replay of Astra's upper
certificate (`LEAN/referee/REVIEW_ASTRA_O1_UPPER_REPLAY.md`, `review_upper_replay/upcore.py`: the normalized forms
`Z/p = γ + J(γ/R − hY)`, the CB additions `σ[βγ + Lσ(γ + βT)]/(Z/p)` and `[(A − β)p − H]/Y = p(3q/5 − β + p − γρ)/Y`),
and lane A12's forms for `β = 0` (`Erdos993Lean/Analytic/Reserve/Cert/Real.lean`, whose `φ`, `yF`, `Rf` lemmas are
reused).  The quantities are those of `Erdos993Lean/Analytic/Reserve/Step.lean` (`cH`, `cL`, `cZ`, `compCB`, `compBC`)
with a general `γ` (the upper band has `γ = 31λ/100`, `Reserve/UpperDefs.lean`).

With `p = msg λ Y`, `y₀ = lmass λ Y`, `R = λ e^{−Y}`, `s = msg λ T`, `y = lmass λ T`, `σ = s/y`, `δ = s − p`:
* `hU`, `LpU`, `ZbU`: `h = 1 − p + γ p/y₀`, `L/p = γ/R − h Y`, `Z̄ = Z/p = γ + J · L/p`;
* `cH_eq` (`H = p h`), `cL_eq` (`L = p · L/p`), `cL_eq'`, `cZ_eq` (`Z = p Z̄`);
* **`compCB_eq`**: `CB = α E − β² δ² T/(4 y Z) + σ[βγ + L σ (γ + β T)]/Z̄`;
* **`compBC_eq`** (the regrouping that removes the cancellation along `T` between `α p T/y` and the square):
  `BC = α(1 − p − y₀/Y) + p(k − β + p − γρ)/Y + (T/y)[p(α Z̄ − h² s²) − h β δ s]/Z̄ − β² δ² T/(4 y Z)` for the cap
  `A = 1 + k` (the upper band has `k = 3q/5`);
* `phiF_log` (`φ(log(1 + w)) = (1 − 1/(1 + w))/log(1 + w)`) and `one_sub_inv_mono`, for the enclosures of `σ` and
  `ρ = p/y₀` from the point values of `s/y` at the ends of a cell.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert

open Real Erdos993Lean.Analytic Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.Reserve.Cert

/-! ## `φ` at a log-mass -/

/-- `φ(log(1 + w)) = (1 − 1/(1 + w))/log(1 + w)`. -/
theorem phiF_log {w : ℝ} (hw : 0 < 1 + w) : phiF (log (1 + w)) = (1 - 1 / (1 + w)) / log (1 + w) := by
  unfold phiF
  rw [exp_neg, exp_log hw, one_div]

/-- `1 − 1/(1 + w)` increases on `w > −1`. -/
theorem one_sub_inv_mono {w w' : ℝ} (hw : 0 < 1 + w) (hww : w ≤ w') :
    1 - 1 / (1 + w) ≤ 1 - 1 / (1 + w') := by
  have := one_div_le_one_div_of_le hw (by linarith : 1 + w ≤ 1 + w')
  linarith

/-! ## The normalized forms -/

section Forms

variable (γ lam : ℝ)

/-- `h = 1 − p + γ ρ`, `ρ = p/y₀` (`H = p h`). -/
noncomputable def hU (Y : ℝ) : ℝ := (1 - msg lam Y) + γ * (msg lam Y / lmass lam Y)

/-- `L/p = γ/R − h Y`, `R = λ e^{−Y}`. -/
noncomputable def LpU (Y : ℝ) : ℝ := γ / (lam * exp (-Y)) - hU γ lam Y * Y

/-- `Z̄ = Z/p = γ + J L/p`. -/
noncomputable def ZbU (T Y : ℝ) : ℝ := γ + coefJ lam T * LpU γ lam Y

theorem cH_eq (Y : ℝ) : cH γ lam Y = msg lam Y * hU γ lam Y := by
  unfold cH hU; ring

theorem cL_eq (Y : ℝ) (hlam : 0 < lam) : cL γ lam Y = msg lam Y * LpU γ lam Y := by
  have h1 := msg_div_R lam Y hlam
  unfold cL LpU
  rw [cH_eq]
  linear_combination (-γ) * h1

theorem cL_eq' (Y : ℝ) : cL γ lam Y = γ * (1 - msg lam Y) - msg lam Y * hU γ lam Y * Y := by
  unfold cL; rw [cH_eq]

theorem cZ_eq (T Y : ℝ) (hlam : 0 < lam) : cZ γ lam T Y = msg lam Y * ZbU γ lam T Y := by
  unfold cZ ZbU
  rw [cL_eq γ lam Y hlam]
  ring

/-- **CB in normalized form**: `CB = α E − β² δ² T/(4 y Z) + σ[βγ + L σ (γ + β T)]/Z̄`, `Z = p Z̄`. -/
theorem compCB_eq (α β T Y : ℝ) (hlam : 0 < lam) (hy : 0 < lmass lam T) (hZb : ZbU γ lam T Y ≠ 0) :
    compCB γ lam α β T Y = α * coefE lam T Y -
      β ^ 2 * (msg lam T - msg lam Y) ^ 2 * T / (lmass lam T * (msg lam Y * ZbU γ lam T Y) * 4) +
      msg lam T / lmass lam T * (β * γ + cL γ lam Y * (msg lam T / lmass lam T) * (γ + β * T)) /
        ZbU γ lam T Y := by
  have hp : msg lam Y ≠ 0 := (msg_pos hlam Y).ne'
  have hy' : lmass lam T ≠ 0 := hy.ne'
  unfold compCB
  rw [cZ_eq γ lam T Y hlam]
  unfold coefJ
  field_simp
  ring

/-- **BC in regrouped form** (cap `A = 1 + k`):
`BC = α(1 − p − y₀/Y) + p(k − β + p − γρ)/Y + (T/y)[p(α Z̄ − h² s²) − h β δ s]/Z̄ − β² δ² T/(4 y Z)`. -/
theorem compBC_eq (α β k T Y : ℝ) (hlam : 0 < lam) (hy : 0 < lmass lam T) (hY : Y ≠ 0)
    (hy0 : lmass lam Y ≠ 0) (hZb : ZbU γ lam T Y ≠ 0) :
    compBC γ lam α β (1 + k) T Y =
      α * ((1 - msg lam Y) - lmass lam Y / Y) +
        msg lam Y * (k - β + msg lam Y - γ * (msg lam Y / lmass lam Y)) / Y +
        T / lmass lam T * (msg lam Y * (α * ZbU γ lam T Y - (hU γ lam Y * msg lam T) ^ 2) -
          hU γ lam Y * β * ((msg lam T - msg lam Y) * msg lam T)) / ZbU γ lam T Y -
      β ^ 2 * (msg lam T - msg lam Y) ^ 2 * T / (lmass lam T * (msg lam Y * ZbU γ lam T Y) * 4) := by
  have hp : msg lam Y ≠ 0 := (msg_pos hlam Y).ne'
  have hy' : lmass lam T ≠ 0 := hy.ne'
  unfold compBC coefE
  rw [cZ_eq γ lam T Y hlam, cH_eq]
  unfold hU
  field_simp
  ring

end Forms

end Erdos993Lean.Analytic.Reserve.UpperCert
