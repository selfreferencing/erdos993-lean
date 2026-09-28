import Erdos993Lean.Analytic.Atlas.Hyps
import Erdos993Lean.Analytic.Assembly
import Erdos993Lean.Analytic.Atlas.Data.Lower
import Erdos993Lean.Analytic.Atlas.Data.Upper
import Erdos993Lean.Analytic.Atlas.Checks.L01
import Erdos993Lean.Analytic.Atlas.Checks.L02
import Erdos993Lean.Analytic.Atlas.Checks.L03
import Erdos993Lean.Analytic.Atlas.Checks.L04
import Erdos993Lean.Analytic.Atlas.Checks.L05
import Erdos993Lean.Analytic.Atlas.Checks.L06
import Erdos993Lean.Analytic.Atlas.Checks.L07
import Erdos993Lean.Analytic.Atlas.Checks.L08
import Erdos993Lean.Analytic.Atlas.Checks.L09
import Erdos993Lean.Analytic.Atlas.Checks.L10
import Erdos993Lean.Analytic.Atlas.Checks.L11
import Erdos993Lean.Analytic.Atlas.Checks.L12
import Erdos993Lean.Analytic.Atlas.Checks.L13
import Erdos993Lean.Analytic.Atlas.Checks.L14
import Erdos993Lean.Analytic.Atlas.Checks.L15
import Erdos993Lean.Analytic.Atlas.Checks.L16
import Erdos993Lean.Analytic.Atlas.Checks.L17
import Erdos993Lean.Analytic.Atlas.Checks.L18
import Erdos993Lean.Analytic.Atlas.Checks.L19
import Erdos993Lean.Analytic.Atlas.Checks.L20
import Erdos993Lean.Analytic.Atlas.Checks.L21
import Erdos993Lean.Analytic.Atlas.Checks.L22
import Erdos993Lean.Analytic.Atlas.Checks.L23
import Erdos993Lean.Analytic.Atlas.Checks.L24
import Erdos993Lean.Analytic.Atlas.Checks.L25
import Erdos993Lean.Analytic.Atlas.Checks.L26
import Erdos993Lean.Analytic.Atlas.Checks.L27
import Erdos993Lean.Analytic.Atlas.Checks.L28
import Erdos993Lean.Analytic.Atlas.Checks.L29
import Erdos993Lean.Analytic.Atlas.Checks.L30
import Erdos993Lean.Analytic.Atlas.Checks.U01
import Erdos993Lean.Analytic.Atlas.Checks.U02
import Erdos993Lean.Analytic.Atlas.Checks.U03
import Erdos993Lean.Analytic.Atlas.Checks.U04
import Erdos993Lean.Analytic.Atlas.Checks.U05
import Erdos993Lean.Analytic.Atlas.Checks.U06
import Erdos993Lean.Analytic.Atlas.Checks.U07
import Erdos993Lean.Analytic.Atlas.Checks.U08
import Erdos993Lean.Analytic.Atlas.Checks.U09
import Erdos993Lean.Analytic.Atlas.Checks.U10
import Erdos993Lean.Analytic.Atlas.Checks.U11
import Erdos993Lean.Analytic.Atlas.Checks.U12
import Erdos993Lean.Analytic.Atlas.Checks.U13
import Erdos993Lean.Analytic.Atlas.Checks.U14
import Erdos993Lean.Analytic.Atlas.Checks.U15
import Erdos993Lean.Analytic.Atlas.Checks.U16
import Erdos993Lean.Analytic.Atlas.Checks.U17
import Erdos993Lean.Analytic.Atlas.Checks.U18
import Erdos993Lean.Analytic.Atlas.Checks.U19
import Erdos993Lean.Analytic.Atlas.Checks.U20
import Erdos993Lean.Analytic.Atlas.Checks.U21
import Erdos993Lean.Analytic.Atlas.Checks.U22
import Erdos993Lean.Analytic.Atlas.Checks.U23
import Erdos993Lean.Analytic.Atlas.Checks.U24
import Erdos993Lean.Analytic.Atlas.Checks.U25
import Erdos993Lean.Analytic.Atlas.Checks.U26
import Erdos993Lean.Analytic.Atlas.Checks.U27
import Erdos993Lean.Analytic.Atlas.Checks.U28
import Erdos993Lean.Analytic.Atlas.Checks.U29
import Erdos993Lean.Analytic.Atlas.Checks.U30

/-!
# The O4 atlas (lane A9): O4 on bounded `m` for the certified profile

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  Soul's O4 atlas of rational dual boxes
(`SOUL/O4/atlas_50/band_XX/box_*.json`, 1,502 boxes, `m ≤ 50`, 78 of them split in `m` into two halves;
the frozen upper atlas `SOUL/O4/atlas_50_400_final/band_XX/box_*.json`, 215 boxes, `50 ≤ m ≤ 400`, freeze
file `SOUL/O4/ATLAS_50_400_VERIFIED.json`), checked by the exact rational checker of
`Erdos993Lean/Analytic/Atlas/Checker.lean` with the tail base of `Profile30.tailFn`.

The 60 band checks (`lowerChecks`, `upperChecks`) are the `native_decide` theorems of
`Erdos993Lean/Analytic/Atlas/Checks/L01.lean` … `U30.lean` (they trust the Lean compiler:
`Lean.ofReduceBool`); everything else is proved on standard axioms (`Atlas/Kernel.lean` …
`Atlas/Profile.lean`).

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* `lowerChecks`, `upperChecks`: the 30 + 30 band checks.
* **`explicitThreshold_small_lower`**: T1's explicit threshold for `Profile30.P` at every activity in
  range and every `m` from the band floor to 50.
* **`explicitThreshold_small_upper`**: the same for every `50 ≤ m ≤ 400`.
* **`explicitThreshold_small`**: the same for every `P.mfloor t ≤ m < 400`: the `hsmall` hypothesis of
  `thresholdNoValley_of_split` (`Analytic/Assembly.lean`), hence **`thresholdNoValley_P30_of`**
  (O4 for `Profile30.P` from the profile's `D`, `θ` and third-mean tail hypotheses of the large-mean
  theorem), and **`thresholdNoValley_P30`**: O4 for `Profile30.P` (those hypotheses are
  `Atlas/Hyps.lean`).
* `explicitThreshold_small_of_atlasProfile`: the same for every `AtlasProfile` (e.g. `P30act`, the
  profile with the actual-activity tail).
-/

namespace Erdos993Lean.Analytic.Atlas

open Erdos993Lean.Analytic Erdos993Lean.Analytic.Atlas.Data Erdos993Lean.Analytic.Atlas.Checks

/-- **The 30 lower band checks** (`m ≤ 50`, band-edge tail base). -/
theorem lowerChecks : ∀ i < 30, bandOK (bandAt i) (fun _ => (bandAt i).lamHi) 50 (lowerBoxes i)
    (lowerSlabs i) = true := by
  intro i hi
  interval_cases i
  exacts [checkL01, checkL02, checkL03, checkL04, checkL05, checkL06, checkL07, checkL08, checkL09,
  checkL10, checkL11, checkL12, checkL13, checkL14, checkL15, checkL16, checkL17, checkL18,
  checkL19, checkL20, checkL21, checkL22, checkL23, checkL24, checkL25, checkL26, checkL27,
  checkL28, checkL29, checkL30]

/-- **The 30 upper band checks** (`50 ≤ m ≤ 400`, band-edge tail base). -/
theorem upperChecks : ∀ i < 30, bandOK { bandAt i with mmin := 50 } (fun _ => (bandAt i).lamHi) 400
    (upperBoxes i) (upperSlabs i) = true := by
  intro i hi
  interval_cases i
  exacts [checkU01, checkU02, checkU03, checkU04, checkU05, checkU06, checkU07, checkU08, checkU09,
  checkU10, checkU11, checkU12, checkU13, checkU14, checkU15, checkU16, checkU17, checkU18,
  checkU19, checkU20, checkU21, checkU22, checkU23, checkU24, checkU25, checkU26, checkU27,
  checkU28, checkU29, checkU30]

/-- **O4 on `m ≤ 50` (the lower atlas) for the certified profile `Profile30.P`**: T1's explicit
threshold condition holds at every activity in range and every `m` from the band floor to 50. -/
theorem explicitThreshold_small_lower :
    ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m ≤ 50 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m) :=
  explicitThreshold_small_lower_P30_of_checks lowerBoxes lowerSlabs lowerChecks

/-- **O4 on `50 ≤ m ≤ 400` (the upper atlas) for `Profile30.P`.** -/
theorem explicitThreshold_small_upper :
    ∀ t, InRange t → ∀ m, 50 ≤ m → m ≤ 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m) :=
  explicitThreshold_small_upper_P30_of_checks upperBoxes upperSlabs upperChecks

/-- **O4 on bounded `m` for `Profile30.P`**: T1's explicit threshold condition at every activity in
range and every `P.mfloor t ≤ m < 400` (the `hsmall` hypothesis of `thresholdNoValley_of_split`). -/
theorem explicitThreshold_small :
    ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m) :=
  explicitThreshold_small_P30_of_checks lowerBoxes lowerSlabs upperBoxes upperSlabs lowerChecks
    upperChecks

/-- **O4 on bounded `m` for every `AtlasProfile`** (e.g. `P30act`). -/
theorem explicitThreshold_small_of_atlasProfile {P : Profile} (hP : AtlasProfile P) :
    ∀ t, InRange t → ∀ m, P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P.θb t) (P.Db t) (P.Tb t m) (P.M1b t m) :=
  explicitThreshold_small_of_checks lowerBoxes lowerSlabs upperBoxes upperSlabs lowerChecks upperChecks
    hP

/-- **O4 for `Profile30.P`** (`ThresholdNoValley`) from the atlas (`m < 400`, T1) and the large-mean
theorem (`m ≥ 400`), given the profile's `D ≤ 8/5`, its `θ` targets and the third-mean tail. -/
theorem thresholdNoValley_P30_of
    (hD : ∀ t, InRange t → 0 ≤ Profile30.P.Db t ∧ Profile30.P.Db t ≤ 8 / 5)
    (hθ : ∀ t, InRange t → 0 ≤ Profile30.P.θb t ∧
      ((3 / 8 ≤ actQ t ∧ actQ t ≤ 8 / 13 ∧ Profile30.P.θb t ≤ 7 / 10) ∨
        ((actQ t ≤ 3 / 8 ∨ 8 / 13 ≤ actQ t) ∧ Profile30.P.θb t ≤ 1)))
    (htail : ∀ t, InRange t → ∀ m, 400 ≤ m →
      ∃ r : ℕ, r < Profile30.P.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧
        Profile30.P.Tb t m r ≤ Real.exp (-(m / 30))) :
    ThresholdNoValley Profile30.P :=
  thresholdNoValley_of_split explicitThreshold_small hD hθ htail

/-- **O4 for the certified profile `Profile30.P`** (`ThresholdNoValley`): T1 with Soul's atlas on
`m < 400`, the large-mean theorem on `m ≥ 400`. -/
theorem thresholdNoValley_P30 : ThresholdNoValley Profile30.P :=
  thresholdNoValley_P30_of profile30_hD profile30_hθ profile30_htail

end Erdos993Lean.Analytic.Atlas
