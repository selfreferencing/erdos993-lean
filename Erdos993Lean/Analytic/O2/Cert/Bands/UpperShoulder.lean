import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR00
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR01
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR02
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR03
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR04
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR05
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR06
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR07
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR08
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR09
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR10
import Erdos993Lean.Analytic.O2.Cert.Checks.UpperShoulderR11

/-!
# O2 certificates: the band `upperShoulder` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `upperShoulder` of `Erdos993Lean/Analytic/O2/Defs.lean`
(R2 `upper_shoulder`, `γ = 17/10`): the checker's tables are A16's (`upperShoulder_matches`, `decide +kernel`), its range and sign facts
(`upperShoulder_facts`), the twelve root-box checks (`Checks/UpperShoulderR00` … `Checks/UpperShoulderR11`, one `native_decide` each), hence
**`localPaymentOK_upperShoulder`** and **`leafOK_upperShoulder`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `upperShoulder` are A16's. -/
theorem upperShoulder_matches : Matches upperShoulderSD upperShoulder :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `upperShoulder`. -/
theorem upperShoulder_facts : BandFacts upperShoulderSD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `upperShoulder` starts at `x = 2⁻¹⁶`. -/
theorem upperShoulder_xmin : upperShoulder.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `upperShoulder` pass. -/
theorem upperShoulder_checks : ∀ i < 12, checkRoot upperShoulderSD i (upperShoulderToks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact upperShoulder_r00
  · exact upperShoulder_r01
  · exact upperShoulder_r02
  · exact upperShoulder_r03
  · exact upperShoulder_r04
  · exact upperShoulder_r05
  · exact upperShoulder_r06
  · exact upperShoulder_r07
  · exact upperShoulder_r08
  · exact upperShoulder_r09
  · exact upperShoulder_r10
  · exact upperShoulder_r11

/-- **The certified local payment of the band `upperShoulder`.** -/
theorem localPaymentOK_upperShoulder : upperShoulder.LocalPaymentOK :=
  localPaymentOK_of_checks upperShoulder_matches upperShoulder_facts upperShoulder_xmin upperShoulder_checks

/-- **The leaf endpoint of the band `upperShoulder`.** -/
theorem leafOK_upperShoulder : upperShoulder.LeafOK := leafOK_of_checks upperShoulder_matches upperShoulder_facts upperShoulder_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
