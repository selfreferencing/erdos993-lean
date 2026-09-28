import Erdos993Lean.Analytic.Reserve.TailGeneric

/-!
# The analytic tails of the reserve comparisons on the four bands (`TailOK band0 … band3`)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A13 (O1 by the two-generation reserve).
Sources: `LEAN/referee/astra_o1/snapshot_0730/SHARP_FIRST_FOUR_RESERVE_PROOF.md` (bands 1–3:
`α = 23q/50`, `γ = λ(3+λ)/13`; "Complete parent tail Y>=4", "Complete child tail T>=6, Y<=4"),
`LOWER_SHARP_ALTERNATE_PROOF.md` (band 0: `D = 8/5`, `α = q/2`, `γ = λ(3+λ)/11`, reusing the D = 2
4/6 tails of `TWO_GENERATION_RESERVE_PROOF.md`); referee check `LEAN/referee/REVIEW_ASTRA_O1_PROOF.md`,
TASK 4 (73 exact rational claims recomputed in `review_proof/r4_tails_exact.py`).

`tailOK_of` reduces `TailOK c` to rational envelopes of the band's coefficient profile, computed
from the band's fields: `λ ≤ Λ` (`Λ ≥ hi`), `λ/γ ≤ gDen/(3 + lo) ≤ R`, `γ ≤ hi(3 + hi)/gDen ≤ Γ`,
`α ≥ aCoef · lo/(1 + lo) ≥ α₀ ≥ 0`, `A ≥ 1` (`D ≥ 1`), and the rational conditions of the two
generic tails (`Tails.compOK_parent` on `Y ≥ 4`, `Tails.compOK_child` on `T ≥ 6`, `Y < 4`). The four
headline theorems instantiate it with exact rationals checked by `norm_num`:

| band | `λ` | `Λ` | `R` | `Γ` | `α₀` |
|---|---|---|---|---|---|
| `band0` | `[1/3, 3/5]` | `3/5` | `33/10` | `54/275` | `1/8` |
| `band1` | `[3/5, 4/5]` | `4/5` | `65/18` | `76/325` | `69/400` |
| `band2` | `[4/5, 13/10]` | `13/10` | `65/19` | `43/100` | `46/225` |
| `band3` | `[13/10, 8/5]` | `8/5` | `130/43` | `184/325` | `13/50` |

Margins (exact rationals, recomputed by `LEAN/lanes/A13/scratch/side_conditions.py`): on the parent
tail the two (QB) costs are below `5%` of `α₀ (1 − Λ/40)` on every band; on the child tail the (QC)
and (QB) conditions hold with a factor at least `25` and `500` to spare.

Scalarity: the envelopes are inputs (per band, from the band's exact fields); the margins are
outputs; the consumer is lane A11's `bandVar_of_ok` through `TailOK`.
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

namespace Tails

variable (c : Band) {lam : ℝ}

theorem gamma_pos_of (hlam : 0 < lam) (hg : 0 < (c.gDen : ℝ)) : 0 < gamma c lam :=
  div_pos (mul_pos hlam (by linarith)) hg

/-- `λ ≤ (gDen/(3 + lo)) γ` for `λ ≥ lo`, i.e. `λ/γ ≤ gDen/(3 + lo)`. -/
theorem lam_le_mul_gamma (hlam : 0 < lam) (hg : 0 < (c.gDen : ℝ)) (hlo : (c.lo : ℝ) ≤ lam)
    (hlo0 : 0 ≤ (c.lo : ℝ)) : lam ≤ (c.gDen : ℝ) / (3 + c.lo) * gamma c lam := by
  have h3 : 0 < 3 + (c.lo : ℝ) := by linarith
  have e : (c.gDen : ℝ) / (3 + c.lo) * gamma c lam = lam * (3 + lam) / (3 + c.lo) := by
    unfold gamma; field_simp
  rw [e, le_div_iff₀ h3]
  have := mul_le_mul_of_nonneg_left hlo hlam.le
  linarith

/-- `γ ≤ hi (3 + hi)/gDen` for `λ ≤ hi`. -/
theorem gamma_le_of (hlam : 0 < lam) (hg : 0 < (c.gDen : ℝ)) (hhi : lam ≤ c.hi) :
    gamma c lam ≤ (c.hi : ℝ) * (3 + c.hi) / c.gDen := by
  unfold gamma
  apply div_le_div_of_nonneg_right _ hg.le
  exact mul_le_mul hhi (by linarith) (by linarith) (by linarith)

/-- `α ≥ aCoef · lo/(1 + lo)` for `λ ≥ lo ≥ 0`. -/
theorem alpha_ge_of (hlam : 0 < lam) (ha : 0 ≤ (c.aCoef : ℝ)) (hlo : (c.lo : ℝ) ≤ lam)
    (hlo0 : 0 ≤ (c.lo : ℝ)) : (c.aCoef : ℝ) * ((c.lo : ℝ) / (1 + c.lo)) ≤ alpha c lam := by
  unfold alpha actQ
  apply mul_le_mul_of_nonneg_left _ ha
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- **`TailOK` from rational envelopes** of the band's coefficient profile. -/
theorem tailOK_of {Λ R Γ α₀ : ℝ}
    (hlo : 0 < (c.lo : ℝ)) (hg : 0 < (c.gDen : ℝ)) (ha : 0 ≤ (c.aCoef : ℝ)) (hD : 1 ≤ (c.D : ℝ))
    (hΛ : (c.hi : ℝ) ≤ Λ) (hR : (c.gDen : ℝ) / (3 + c.lo) ≤ R)
    (hΓ : (c.hi : ℝ) * (3 + c.hi) / c.gDen ≤ Γ)
    (hα : α₀ ≤ (c.aCoef : ℝ) * ((c.lo : ℝ) / (1 + c.lo))) (hα₀ : 0 ≤ α₀)
    (hℓ : 0 < 1 - Λ / 50 - (R + Λ) * (2 / 25))
    (hm : Γ * Λ / 200 + (1 + Γ) ^ 2 * Λ * R / (2500 * (1 - Λ / 50 - (R + Λ) * (2 / 25))) ≤
      α₀ * (1 - Λ / 40))
    (hΛ5 : Λ ≤ 5) (hm0 : Γ ≤ α₀ * (5 - Λ))
    (hκ : 0 < 1 - 3 / 50 * (1 + Γ) * R)
    (hC : 4 * (1 + Γ) ≤ α₀ * (5 - Λ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R))
    (hB : (1 + Γ) ^ 2 * (3 * R / 200) ≤
      (α₀ * (5 - Λ) - Γ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R)) :
    TailOK c := by
  intro lam T Y hlo' hhi' hT hTY hcase
  have hlam : 0 < lam := lt_of_lt_of_le hlo hlo'
  have hγ := gamma_pos_of c hlam hg
  have hlamΛ : lam ≤ Λ := hhi'.trans hΛ
  have hlamR : lam ≤ R * gamma c lam :=
    (lam_le_mul_gamma c hlam hg hlo' hlo.le).trans (mul_le_mul_of_nonneg_right hR hγ.le)
  have hγΓ : gamma c lam ≤ Γ := (gamma_le_of c hlam hg hhi').trans hΓ
  have hαα : α₀ ≤ alpha c lam := hα.trans (alpha_ge_of c hlam ha hlo' hlo.le)
  have hA : 1 ≤ capA c lam := capA_ge_one c hD hlam
  rcases le_or_gt 4 Y with hY | hY
  · exact compOK_parent c hlam hT hTY hY hlamΛ hlamR hγ hγΓ hαα hα₀ hA hℓ hm
  · have hT6 : 6 ≤ T := by
      rcases hcase with h | h
      · exact absurd h (not_le.mpr hY)
      · exact h
    exact compOK_child c hlam hT6 hTY hY.le hlamΛ hlamR hγ hγΓ hαα hα₀ hA hΛ5 hm0 hκ hC hB

end Tails

open Tails

/-- **The analytic tails on band 0** (`λ ∈ [1/3, 3/5]`, `D = 8/5`, `α = q/2`, `γ = λ(3+λ)/11`). -/
theorem tailOK_band0 : TailOK band0 :=
  tailOK_of band0 (Λ := 3 / 5) (R := 33 / 10) (Γ := 54 / 275) (α₀ := 1 / 8)
    (by norm_num [band0]) (by norm_num [band0]) (by norm_num [band0]) (by norm_num [band0])
    (by norm_num [band0]) (by norm_num [band0]) (by norm_num [band0]) (by norm_num [band0])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **The analytic tails on band 1** (`λ ∈ [3/5, 4/5]`, `D = 7/5`, `α = 23q/50`,
`γ = λ(3+λ)/13`). -/
theorem tailOK_band1 : TailOK band1 :=
  tailOK_of band1 (Λ := 4 / 5) (R := 65 / 18) (Γ := 76 / 325) (α₀ := 69 / 400)
    (by norm_num [band1]) (by norm_num [band1]) (by norm_num [band1]) (by norm_num [band1])
    (by norm_num [band1]) (by norm_num [band1]) (by norm_num [band1]) (by norm_num [band1])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **The analytic tails on band 2** (`λ ∈ [4/5, 13/10]`, `D = 6/5`, `α = 23q/50`,
`γ = λ(3+λ)/13`). -/
theorem tailOK_band2 : TailOK band2 :=
  tailOK_of band2 (Λ := 13 / 10) (R := 65 / 19) (Γ := 43 / 100) (α₀ := 46 / 225)
    (by norm_num [band2]) (by norm_num [band2]) (by norm_num [band2]) (by norm_num [band2])
    (by norm_num [band2]) (by norm_num [band2]) (by norm_num [band2]) (by norm_num [band2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **The analytic tails on band 3** (`λ ∈ [13/10, 8/5]`, `D = 7/5`, `α = 23q/50`,
`γ = λ(3+λ)/13`). -/
theorem tailOK_band3 : TailOK band3 :=
  tailOK_of band3 (Λ := 8 / 5) (R := 130 / 43) (Γ := 184 / 325) (α₀ := 13 / 50)
    (by norm_num [band3]) (by norm_num [band3]) (by norm_num [band3]) (by norm_num [band3])
    (by norm_num [band3]) (by norm_num [band3]) (by norm_num [band3]) (by norm_num [band3])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Erdos993Lean.Analytic.Reserve
