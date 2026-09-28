import Erdos993Lean.Analytic.Atlas.Params
import Erdos993Lean.Analytic.Atlas.Data.L30

/-!
# Atlas check: lower atlas (`atlas_50`, `m ≤ 50`), band 30 (`native_decide`)

Activity band `[9/4, 7/3]` (0-based band 29).  The one `native_decide` of this module
evaluates the checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on Soul's boxes of this band,
with the band's upper edge as tail base (the base of `Profile30.tailFn`): every box passes and the boxes cover
`[q(λ_29), q(λ_30)] × [floor, cap]` (m ≤ 50).  This trusts the Lean compiler (`Lean.ofReduceBool`); what
the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`.
-/

namespace Erdos993Lean.Analytic.Atlas.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.Atlas.Data

set_option profiler true
set_option profiler.threshold 500

/-- The lower atlas (`atlas_50`, `m ≤ 50`), band 30: every box and the cover pass. -/
theorem checkL30 :
    bandOK (bandAt 29) (fun _ => (bandAt 29).lamHi) 50 boxesL30 slabsL30 =
      true := by
  native_decide

end Erdos993Lean.Analytic.Atlas.Checks
