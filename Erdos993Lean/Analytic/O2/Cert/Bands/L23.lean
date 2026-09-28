import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R00
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R01
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R02
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R03
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R04
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R05
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R06
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R07
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R08
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R09
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R10
import Erdos993Lean.Analytic.O2.Cert.Checks.L23R11

/-!
# O2 certificates: the band `L23` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `L23` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `L23`, `γ = 17/10`): the checker's tables are A16's (`l23_matches`, `decide +kernel`), its range and sign facts
(`l23_facts`), the twelve root-box checks (`Checks/L23R00` … `Checks/L23R11`, one `native_decide` each), hence
**`localPaymentOK_L23`** and **`leafOK_L23`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `L23` are A16's. -/
theorem l23_matches : Matches l23SD L23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `L23`. -/
theorem l23_facts : BandFacts l23SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `L23` starts at `x = 2⁻¹⁶`. -/
theorem l23_xmin : L23.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `L23` pass. -/
theorem l23_checks : ∀ i < 12, checkRoot l23SD i (l23Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact l23_r00
  · exact l23_r01
  · exact l23_r02
  · exact l23_r03
  · exact l23_r04
  · exact l23_r05
  · exact l23_r06
  · exact l23_r07
  · exact l23_r08
  · exact l23_r09
  · exact l23_r10
  · exact l23_r11

/-- **The certified local payment of the band `L23`.** -/
theorem localPaymentOK_L23 : L23.LocalPaymentOK :=
  localPaymentOK_of_checks l23_matches l23_facts l23_xmin l23_checks

/-- **The leaf endpoint of the band `L23`.** -/
theorem leafOK_L23 : L23.LeafOK := leafOK_of_checks l23_matches l23_facts l23_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
