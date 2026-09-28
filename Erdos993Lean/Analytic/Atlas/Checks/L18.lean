import Erdos993Lean.Analytic.Atlas.Params
import Erdos993Lean.Analytic.Atlas.Data.L18

/-!
# Atlas check: lower atlas (`atlas_50`, `m ≤ 50`), band 18 (`native_decide`)

Activity band `[27/25, 28/25]` (0-based band 17).  The one `native_decide` of this module
evaluates the checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on Soul's boxes of this band,
with the band's upper edge as tail base (the base of `Profile30.tailFn`): every box passes and the boxes cover
`[q(λ_17), q(λ_18)] × [floor, cap]` (m ≤ 50).  This trusts the Lean compiler (`Lean.ofReduceBool`); what
the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`.
-/

namespace Erdos993Lean.Analytic.Atlas.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.Atlas.Data

set_option profiler true
set_option profiler.threshold 500

/-- The lower atlas (`atlas_50`, `m ≤ 50`), band 18: every box and the cover pass. -/
theorem checkL18 :
    bandOK (bandAt 17) (fun _ => (bandAt 17).lamHi) 50 boxesL18 slabsL18 =
      true := by
  native_decide

end Erdos993Lean.Analytic.Atlas.Checks
