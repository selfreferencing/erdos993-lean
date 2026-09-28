import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R00
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R01
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R02
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R03
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R04
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R05
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R06
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R07
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R08
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R09
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R10
import Erdos993Lean.Analytic.O2.Cert.Checks.Central2R11

/-!
# O2 certificates: the band `central2` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `central2` of `Erdos993Lean/Analytic/O2/Defs.lean`
(R2 `central_2`, `γ = 8/5`): the checker's tables are A16's (`central2_matches`, `decide +kernel`), its range and sign facts
(`central2_facts`), the twelve root-box checks (`Checks/Central2R00` … `Checks/Central2R11`, one `native_decide` each), hence
**`localPaymentOK_central2`** and **`leafOK_central2`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `central2` are A16's. -/
theorem central2_matches : Matches central2SD central2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `central2`. -/
theorem central2_facts : BandFacts central2SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `central2` starts at `x = 2⁻¹⁶`. -/
theorem central2_xmin : central2.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `central2` pass. -/
theorem central2_checks : ∀ i < 12, checkRoot central2SD i (central2Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact central2_r00
  · exact central2_r01
  · exact central2_r02
  · exact central2_r03
  · exact central2_r04
  · exact central2_r05
  · exact central2_r06
  · exact central2_r07
  · exact central2_r08
  · exact central2_r09
  · exact central2_r10
  · exact central2_r11

/-- **The certified local payment of the band `central2`.** -/
theorem localPaymentOK_central2 : central2.LocalPaymentOK :=
  localPaymentOK_of_checks central2_matches central2_facts central2_xmin central2_checks

/-- **The leaf endpoint of the band `central2`.** -/
theorem leafOK_central2 : central2.LeafOK := leafOK_of_checks central2_matches central2_facts central2_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
