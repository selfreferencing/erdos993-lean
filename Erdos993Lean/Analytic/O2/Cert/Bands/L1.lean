import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R00
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R01
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R02
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R03
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R04
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R05
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R06
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R07
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R08
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R09
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R10
import Erdos993Lean.Analytic.O2.Cert.Checks.L1R11

/-!
# O2 certificates: the band `L1` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `L1` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `L1`, `γ = 17/10`): the checker's tables are A16's (`l1_matches`, `decide +kernel`), its range and sign facts
(`l1_facts`), the twelve root-box checks (`Checks/L1R00` … `Checks/L1R11`, one `native_decide` each), hence
**`localPaymentOK_L1`** and **`leafOK_L1`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `L1` are A16's. -/
theorem l1_matches : Matches l1SD L1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `L1`. -/
theorem l1_facts : BandFacts l1SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `L1` starts at `x = 2⁻¹⁶`. -/
theorem l1_xmin : L1.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `L1` pass. -/
theorem l1_checks : ∀ i < 12, checkRoot l1SD i (l1Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact l1_r00
  · exact l1_r01
  · exact l1_r02
  · exact l1_r03
  · exact l1_r04
  · exact l1_r05
  · exact l1_r06
  · exact l1_r07
  · exact l1_r08
  · exact l1_r09
  · exact l1_r10
  · exact l1_r11

/-- **The certified local payment of the band `L1`.** -/
theorem localPaymentOK_L1 : L1.LocalPaymentOK :=
  localPaymentOK_of_checks l1_matches l1_facts l1_xmin l1_checks

/-- **The leaf endpoint of the band `L1`.** -/
theorem leafOK_L1 : L1.LeafOK := leafOK_of_checks l1_matches l1_facts l1_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
