import Erdos993Lean.Analytic.Atlas.Params
import Erdos993Lean.Analytic.Atlas.Data.U17

/-!
# Atlas check: upper atlas (`atlas_50_400_final`, `50 ≤ m ≤ 400`), band 17 (`native_decide`)

Activity band `[26/25, 27/25]` (0-based band 16).  The one `native_decide` of this module
evaluates the checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on Soul's frozen upper boxes of
this band, with the band's upper edge as tail base (the base of `Profile30.tailFn`): every box passes and
the boxes cover `[q(λ_16), q(λ_17)] × [50, 400]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`.
-/

namespace Erdos993Lean.Analytic.Atlas.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.Atlas.Data

set_option profiler true
set_option profiler.threshold 500

/-- The upper atlas, band 17: every box and the cover pass. -/
theorem checkU17 :
    bandOK { bandAt 16 with mmin := 50 } (fun _ => (bandAt 16).lamHi) 400 boxesU17 slabsU17 =
      true := by
  native_decide

end Erdos993Lean.Analytic.Atlas.Checks
