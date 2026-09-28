import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R00
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R01
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R02
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R03
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R04
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R05
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R06
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R07
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R08
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R09
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R10
import Erdos993Lean.Analytic.O2.Cert.Checks.Central3R11

/-!
# O2 certificates: the band `central3` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `central3` of `Erdos993Lean/Analytic/O2/Defs.lean`
(R2 `central_3`, `γ = 8/5`): the checker's tables are A16's (`central3_matches`, `decide +kernel`), its range and sign facts
(`central3_facts`), the twelve root-box checks (`Checks/Central3R00` … `Checks/Central3R11`, one `native_decide` each), hence
**`localPaymentOK_central3`** and **`leafOK_central3`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `central3` are A16's. -/
theorem central3_matches : Matches central3SD central3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `central3`. -/
theorem central3_facts : BandFacts central3SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `central3` starts at `x = 2⁻¹⁶`. -/
theorem central3_xmin : central3.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `central3` pass. -/
theorem central3_checks : ∀ i < 12, checkRoot central3SD i (central3Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact central3_r00
  · exact central3_r01
  · exact central3_r02
  · exact central3_r03
  · exact central3_r04
  · exact central3_r05
  · exact central3_r06
  · exact central3_r07
  · exact central3_r08
  · exact central3_r09
  · exact central3_r10
  · exact central3_r11

/-- **The certified local payment of the band `central3`.** -/
theorem localPaymentOK_central3 : central3.LocalPaymentOK :=
  localPaymentOK_of_checks central3_matches central3_facts central3_xmin central3_checks

/-- **The leaf endpoint of the band `central3`.** -/
theorem leafOK_central3 : central3.LeafOK := leafOK_of_checks central3_matches central3_facts central3_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
