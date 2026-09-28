import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR00
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR01
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR02
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR03
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR04
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR05
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR06
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR07
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR08
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR09
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR10
import Erdos993Lean.Analytic.O2.Cert.Checks.L4eR11

/-!
# O2 certificates: the band `L4e` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `L4e` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `L4e`, `γ = 17/10`): the checker's tables are A16's (`l4e_matches`, `decide +kernel`), its range and sign facts
(`l4e_facts`), the twelve root-box checks (`Checks/L4eR00` … `Checks/L4eR11`, one `native_decide` each), hence
**`localPaymentOK_L4e`** and **`leafOK_L4e`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `L4e` are A16's. -/
theorem l4e_matches : Matches l4eSD L4e :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `L4e`. -/
theorem l4e_facts : BandFacts l4eSD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `L4e` starts at `x = 2⁻¹⁶`. -/
theorem l4e_xmin : L4e.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `L4e` pass. -/
theorem l4e_checks : ∀ i < 12, checkRoot l4eSD i (l4eToks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact l4e_r00
  · exact l4e_r01
  · exact l4e_r02
  · exact l4e_r03
  · exact l4e_r04
  · exact l4e_r05
  · exact l4e_r06
  · exact l4e_r07
  · exact l4e_r08
  · exact l4e_r09
  · exact l4e_r10
  · exact l4e_r11

/-- **The certified local payment of the band `L4e`.** -/
theorem localPaymentOK_L4e : L4e.LocalPaymentOK :=
  localPaymentOK_of_checks l4e_matches l4e_facts l4e_xmin l4e_checks

/-- **The leaf endpoint of the band `L4e`.** -/
theorem leafOK_L4e : L4e.LeafOK := leafOK_of_checks l4e_matches l4e_facts l4e_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
