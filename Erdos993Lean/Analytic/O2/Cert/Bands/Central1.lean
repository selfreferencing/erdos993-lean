import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R00
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R01
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R02
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R03
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R04
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R05
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R06
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R07
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R08
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R09
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R10
import Erdos993Lean.Analytic.O2.Cert.Checks.Central1R11

/-!
# O2 certificates: the band `central1` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `central1` of `Erdos993Lean/Analytic/O2/Defs.lean`
(R2 `central_1`, `γ = 8/5`): the checker's tables are A16's (`central1_matches`, `decide +kernel`), its range and sign facts
(`central1_facts`), the twelve root-box checks (`Checks/Central1R00` … `Checks/Central1R11`, one `native_decide` each), hence
**`localPaymentOK_central1`** and **`leafOK_central1`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `central1` are A16's. -/
theorem central1_matches : Matches central1SD central1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `central1`. -/
theorem central1_facts : BandFacts central1SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `central1` starts at `x = 2⁻¹⁶`. -/
theorem central1_xmin : central1.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `central1` pass. -/
theorem central1_checks : ∀ i < 12, checkRoot central1SD i (central1Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact central1_r00
  · exact central1_r01
  · exact central1_r02
  · exact central1_r03
  · exact central1_r04
  · exact central1_r05
  · exact central1_r06
  · exact central1_r07
  · exact central1_r08
  · exact central1_r09
  · exact central1_r10
  · exact central1_r11

/-- **The certified local payment of the band `central1`.** -/
theorem localPaymentOK_central1 : central1.LocalPaymentOK :=
  localPaymentOK_of_checks central1_matches central1_facts central1_xmin central1_checks

/-- **The leaf endpoint of the band `central1`.** -/
theorem leafOK_central1 : central1.LeafOK := leafOK_of_checks central1_matches central1_facts central1_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
