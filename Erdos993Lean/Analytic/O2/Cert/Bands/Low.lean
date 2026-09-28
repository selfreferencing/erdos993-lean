import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR00
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR01
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR02
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR03
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR04
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR05
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR06
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR07
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR08
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR09
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR10
import Erdos993Lean.Analytic.O2.Cert.Checks.LowR11

/-!
# O2 certificates: the band `low` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `low` of `Erdos993Lean/Analytic/O2/Defs.lean`
(R2 `low`, `[1/3, 3/5]`, `γ = 2`): the checker's tables are A16's (`low_matches`, `decide +kernel`), its range and sign facts
(`low_facts`), the twelve root-box checks (`Checks/LowR00` … `Checks/LowR11`, one `native_decide` each), hence
**`localPaymentOK_low`** and **`leafOK_low`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `low` are A16's. -/
theorem low_matches : Matches lowSD low :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `low`. -/
theorem low_facts : BandFacts lowSD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `low` starts at `x = 2⁻¹⁶`. -/
theorem low_xmin : low.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `low` pass. -/
theorem low_checks : ∀ i < 12, checkRoot lowSD i (lowToks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact low_r00
  · exact low_r01
  · exact low_r02
  · exact low_r03
  · exact low_r04
  · exact low_r05
  · exact low_r06
  · exact low_r07
  · exact low_r08
  · exact low_r09
  · exact low_r10
  · exact low_r11

/-- **The certified local payment of the band `low`.** -/
theorem localPaymentOK_low : low.LocalPaymentOK :=
  localPaymentOK_of_checks low_matches low_facts low_xmin low_checks

/-- **The leaf endpoint of the band `low`.** -/
theorem leafOK_low : low.LeafOK := leafOK_of_checks low_matches low_facts low_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
