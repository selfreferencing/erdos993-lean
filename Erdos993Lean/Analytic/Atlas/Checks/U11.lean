import Erdos993Lean.Analytic.Atlas.Params
import Erdos993Lean.Analytic.Atlas.Data.U11

/-!
# Atlas check: upper atlas (`atlas_50_400_final`, `50 ≤ m ≤ 400`), band 11 (`native_decide`)

Activity band `[4/5, 21/25]` (0-based band 10).  The one `native_decide` of this module
evaluates the checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on Soul's frozen upper boxes of
this band, with the band's upper edge as tail base (the base of `Profile30.tailFn`): every box passes and
the boxes cover `[q(λ_10), q(λ_11)] × [50, 400]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`.
-/

namespace Erdos993Lean.Analytic.Atlas.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.Atlas.Data

set_option profiler true
set_option profiler.threshold 500

/-- The upper atlas, band 11: every box and the cover pass. -/
theorem checkU11 :
    bandOK { bandAt 10 with mmin := 50 } (fun _ => (bandAt 10).lamHi) 400 boxesU11 slabsU11 =
      true := by
  native_decide

end Erdos993Lean.Analytic.Atlas.Checks
