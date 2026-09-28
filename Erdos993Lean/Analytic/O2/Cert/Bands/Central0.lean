import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R00
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R01
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R02
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R03
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R04
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R05
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R06
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R07
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R08
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R09
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R10
import Erdos993Lean.Analytic.O2.Cert.Checks.Central0R11

/-!
# O2 certificates: the band `central0` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `central0` of `Erdos993Lean/Analytic/O2/Defs.lean`
(R2 `central_0`, `γ = 8/5`): the checker's tables are A16's (`central0_matches`, `decide +kernel`), its range and sign facts
(`central0_facts`), the twelve root-box checks (`Checks/Central0R00` … `Checks/Central0R11`, one `native_decide` each), hence
**`localPaymentOK_central0`** and **`leafOK_central0`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `central0` are A16's. -/
theorem central0_matches : Matches central0SD central0 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `central0`. -/
theorem central0_facts : BandFacts central0SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `central0` starts at `x = 2⁻¹⁶`. -/
theorem central0_xmin : central0.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `central0` pass. -/
theorem central0_checks : ∀ i < 12, checkRoot central0SD i (central0Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact central0_r00
  · exact central0_r01
  · exact central0_r02
  · exact central0_r03
  · exact central0_r04
  · exact central0_r05
  · exact central0_r06
  · exact central0_r07
  · exact central0_r08
  · exact central0_r09
  · exact central0_r10
  · exact central0_r11

/-- **The certified local payment of the band `central0`.** -/
theorem localPaymentOK_central0 : central0.LocalPaymentOK :=
  localPaymentOK_of_checks central0_matches central0_facts central0_xmin central0_checks

/-- **The leaf endpoint of the band `central0`.** -/
theorem leafOK_central0 : central0.LeafOK := leafOK_of_checks central0_matches central0_facts central0_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
