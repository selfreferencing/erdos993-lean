import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperStep
import Erdos993Lean.Analytic.Reserve.Tail
import Erdos993Lean.Analytic.Atlas.Profile

/-!
# O1 for the certified profile: `VarianceBound Profile30.P` (lane A14)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lane A14).  Sources: Astra's
`FULL_PROFILE30_O1_ASSEMBLY.md` (snapshot `LEAN/referee/astra_o1/snapshot_0845`) and the referee's bookkeeping
check `LEAN/referee/REVIEW_ASTRA_O1_UPPER_PROOF.md`, TASK 6 (`review_upper_proof/u7_assembly_bookkeeping.py`).

The five O1 bands (closed activity intervals) and their caps:

| O1 band | `λ` | `D` | Lean |
|---|---|---|---|
| `band0` | `[1/3, 3/5]` | `8/5` | `bandVar_band0` (lane A11) with `tailOK_band0` (lane A13) |
| `band1` | `[3/5, 4/5]` | `7/5` | `bandVar_band1`, `tailOK_band1` |
| `band2` | `[4/5, 13/10]` | `6/5` | `bandVar_band2`, `tailOK_band2` |
| `band3` | `[13/10, 8/5]` | `7/5` | `bandVar_band3`, `tailOK_band3` |
| upper | `[8/5, 7/3]` | `8/5` | `bandVar_upper` (this lane) |

`Profile30.P.Db t = Dt[bandOf t]`, where the 30 Lean bands are left-open, `(λ_i, λ_{i+1}]` (band 0 also
contains `1/3`), and `Dt` is `8/5` on bands 0–5 (`[1/3, 3/5]`), `7/5` on 6–9 (`(3/5, 4/5]`), `6/5` on 10–21
(`(4/5, 13/10]`), `7/5` on 22–24 (`(13/10, 8/5]`), `8/5` on 25–29 (`(8/5, 7/3]`).  An activity `t` in range
lies in the closure `[λ_i, λ_{i+1}]` of its Lean band `i = bandOf t` (lane A9's `Atlas.bandOf_spec`), and that
closure lies in the closed O1 band whose cap equals `Dt[i]` (`profile30_bands0` … `profile30_bandsU`, checked by `decide +kernel`
on Profile30's rational lists).  At a shared edge the closed O1 band on the left is used (at `t = 8/5`,
`bandOf t = 24` and the band `[13/10, 8/5]` gives `7/5`, which is what `Db` asks).

Main results:
* **`varianceBound_profile30`**: `VarianceBound Profile30.P` from `EntropyOK`, the finite boxes and leaf
  bases of `band0 … band3` (lane A12) and the finite box of the upper band (lane A15); the hypotheses
  `61 ≤ F.n` and `AtInteriorRank` of `VarianceBound` are not used (the band theorems hold for every
  forest, every activity of the band and every maximum-weight `B`);
* `varianceBound_profile30_of_boxes`: the same with `EntropyOK` discharged (lane A13's `entropyOK`).

Scalarity: `Db` (the variance-ratio cap of the free count `M`, `Var M ≤ D · E M`) is the output of the five
band theorems; the band edges are the exact domains of the profile (inputs); the consumer is `VarianceBound`
in the analytic assembly (O4's no-valley numerics through `Profile30.P`).
-/

namespace Erdos993Lean.Analytic.Reserve

open Erdos993Lean.Analytic.Profile30

/-! ### The band table of `Profile30`

For each of the 30 Lean bands, the closure `[λ_i, λ_{i+1}]` lies in one closed O1 band, and `Dt[i]` is that
band's cap (checked by the kernel on Profile30's rational lists). -/

/-- Lean bands 0–5 lie in `[1/3, 3/5]` (`band0`) and have `Dt = 8/5`. -/
theorem profile30_bands0 : ∀ i < 30, i ≤ 5 →
    1 / 3 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 3 / 5 ∧ Dt.getD i (8 / 5) = 8 / 5 := by
  decide +kernel

/-- Lean bands 6–9 lie in `[3/5, 4/5]` (`band1`) and have `Dt = 7/5`. -/
theorem profile30_bands1 : ∀ i < 30, 6 ≤ i → i ≤ 9 →
    3 / 5 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 4 / 5 ∧ Dt.getD i (8 / 5) = 7 / 5 := by
  decide +kernel

/-- Lean bands 10–21 lie in `[4/5, 13/10]` (`band2`) and have `Dt = 6/5`. -/
theorem profile30_bands2 : ∀ i < 30, 10 ≤ i → i ≤ 21 →
    4 / 5 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 13 / 10 ∧ Dt.getD i (8 / 5) = 6 / 5 := by
  decide +kernel

/-- Lean bands 22–24 lie in `[13/10, 8/5]` (`band3`) and have `Dt = 7/5`. -/
theorem profile30_bands3 : ∀ i < 30, 22 ≤ i → i ≤ 24 →
    13 / 10 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 8 / 5 ∧ Dt.getD i (8 / 5) = 7 / 5 := by
  decide +kernel

/-- Lean bands 25–29 lie in `[8/5, 7/3]` (the upper band) and have `Dt = 8/5`. -/
theorem profile30_bandsU : ∀ i < 30, 25 ≤ i →
    8 / 5 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 7 / 3 ∧ Dt.getD i (8 / 5) = 8 / 5 := by
  decide +kernel

/-- **O1 for the certified profile** (`VarianceBound Profile30.P`): the five band theorems cover
`[1/3, 7/3]` with the caps `Profile30.P.Db`.  Hypotheses: the entropy facts, the finite boxes and leaf
bases of `band0 … band3` (lane A12) and the finite box of the upper band (lane A15); the analytic tails of
all five bands and the upper leaf base are proved (lanes A13, A14). -/
theorem varianceBound_profile30 (hE : EntropyOK) (hbox0 : BoxOK band0) (hbox1 : BoxOK band1)
    (hbox2 : BoxOK band2) (hbox3 : BoxOK band3) (hleaf0 : LeafOK band0) (hleaf1 : LeafOK band1)
    (hleaf2 : LeafOK band2) (hleaf3 : LeafOK band3) (hboxU : UpperBoxOK) :
    VarianceBound Profile30.P := by
  intro F _ t ht _ B hB
  obtain ⟨hi, hlo, hhi⟩ := Atlas.bandOf_spec ht
  have hlo' : ((edges.getD (bandOf t) 0 : ℚ) : ℝ) ≤ t := hlo
  have hhi' : t ≤ ((edges.getD (bandOf t + 1) 0 : ℚ) : ℝ) := hhi
  have hDb : Profile30.P.Db t = ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ) := rfl
  rw [hDb]
  have b0 := profile30_bands0 (bandOf t) hi
  have b1 := profile30_bands1 (bandOf t) hi
  have b2 := profile30_bands2 (bandOf t) hi
  have b3 := profile30_bands3 (bandOf t) hi
  have b4 := profile30_bandsU (bandOf t) hi
  rcases (show bandOf t ≤ 5 ∨ (6 ≤ bandOf t ∧ bandOf t ≤ 9) ∨ (10 ≤ bandOf t ∧ bandOf t ≤ 21) ∨
      (22 ≤ bandOf t ∧ bandOf t ≤ 24) ∨ 25 ≤ bandOf t by omega) with h | h | h | h | h
  · obtain ⟨e1, e2, e3⟩ := b0 h
    rw [e3]
    exact bandVar_band0 hE hbox0 tailOK_band0 hleaf0 F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b1 h.1 h.2
    rw [e3]
    exact bandVar_band1 hE hbox1 tailOK_band1 hleaf1 F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b2 h.1 h.2
    rw [e3]
    exact bandVar_band2 hE hbox2 tailOK_band2 hleaf2 F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b3 h.1 h.2
    rw [e3]
    exact bandVar_band3 hE hbox3 tailOK_band3 hleaf3 F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b4 h
    rw [e3]
    have c1 : (((8 / 5 : ℚ)) : ℝ) = 8 / 5 := by norm_num
    have c2 : (((7 / 3 : ℚ)) : ℝ) = 7 / 3 := by norm_num
    have h1 : ((8 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((7 / 3 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    rw [c1] at h1 ⊢
    rw [c2] at h2
    exact bandVar_upper hE hboxU F t h1 h2 B hB

/-- `varianceBound_profile30` with the entropy facts discharged (lane A13's `entropyOK`): O1 for the
certified profile from the finite boxes and leaf bases of `band0 … band3` and the upper finite box. -/
theorem varianceBound_profile30_of_boxes (hbox0 : BoxOK band0) (hbox1 : BoxOK band1)
    (hbox2 : BoxOK band2) (hbox3 : BoxOK band3) (hleaf0 : LeafOK band0) (hleaf1 : LeafOK band1)
    (hleaf2 : LeafOK band2) (hleaf3 : LeafOK band3) (hboxU : UpperBoxOK) :
    VarianceBound Profile30.P :=
  varianceBound_profile30 entropyOK hbox0 hbox1 hbox2 hbox3 hleaf0 hleaf1 hleaf2 hleaf3 hboxU

end Erdos993Lean.Analytic.Reserve
