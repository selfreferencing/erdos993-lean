import Erdos993Lean.Analytic.Atlas.Params
import Erdos993Lean.Analytic.Atlas.Data.U23

/-!
# Atlas check: upper atlas (`atlas_50_400_final`, `50 ≤ m ≤ 400`), band 23 (`native_decide`)

Activity band `[13/10, 7/5]` (0-based band 22).  The one `native_decide` of this module
evaluates the checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on Soul's frozen upper boxes of
this band, with the band's upper edge as tail base (the base of `Profile30.tailFn`): every box passes and
the boxes cover `[q(λ_22), q(λ_23)] × [50, 400]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`.
-/

namespace Erdos993Lean.Analytic.Atlas.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.Atlas.Data

set_option profiler true
set_option profiler.threshold 500

/-- The upper atlas, band 23: every box and the cover pass. -/
theorem checkU23 :
    bandOK { bandAt 22 with mmin := 50 } (fun _ => (bandAt 22).lamHi) 400 boxesU23 slabsU23 =
      true := by
  native_decide

end Erdos993Lean.Analytic.Atlas.Checks
