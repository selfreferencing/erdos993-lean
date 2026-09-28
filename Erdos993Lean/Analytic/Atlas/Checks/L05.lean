import Erdos993Lean.Analytic.Atlas.Params
import Erdos993Lean.Analytic.Atlas.Data.L05

/-!
# Atlas check: lower atlas (`atlas_50`, `m ≤ 50`), band 05 (`native_decide`)

Activity band `[1/2, 11/20]` (0-based band 4).  The one `native_decide` of this module
evaluates the checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on Soul's boxes of this band,
with the band's upper edge as tail base (the base of `Profile30.tailFn`): every box passes and the boxes cover
`[q(λ_4), q(λ_5)] × [floor, cap]` (m ≤ 50).  This trusts the Lean compiler (`Lean.ofReduceBool`); what
the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`.
-/

namespace Erdos993Lean.Analytic.Atlas.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.Atlas.Data

set_option profiler true
set_option profiler.threshold 500

/-- The lower atlas (`atlas_50`, `m ≤ 50`), band 05: every box and the cover pass. -/
theorem checkL05 :
    bandOK (bandAt 4) (fun _ => (bandAt 4).lamHi) 50 boxesL05 slabsL05 =
      true := by
  native_decide

end Erdos993Lean.Analytic.Atlas.Checks
