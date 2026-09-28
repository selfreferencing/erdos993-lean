import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R00
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R01
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R02
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R03
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R04
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R05
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R06
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R07
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R08
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R09
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R10
import Erdos993Lean.Analytic.O2.Cert.Checks.H8R11

/-!
# O2 certificates: the band `H8` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `H8` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `H8`, `γ = 2`): the checker's tables are A16's (`h8_matches`, `decide +kernel`), its range and sign facts
(`h8_facts`), the twelve root-box checks (`Checks/H8R00` … `Checks/H8R11`, one `native_decide` each), hence
**`localPaymentOK_H8`** and **`leafOK_H8`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `H8` are A16's. -/
theorem h8_matches : Matches h8SD H8 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `H8`. -/
theorem h8_facts : BandFacts h8SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `H8` starts at `x = 2⁻¹⁶`. -/
theorem h8_xmin : H8.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `H8` pass. -/
theorem h8_checks : ∀ i < 12, checkRoot h8SD i (h8Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact h8_r00
  · exact h8_r01
  · exact h8_r02
  · exact h8_r03
  · exact h8_r04
  · exact h8_r05
  · exact h8_r06
  · exact h8_r07
  · exact h8_r08
  · exact h8_r09
  · exact h8_r10
  · exact h8_r11

/-- **The certified local payment of the band `H8`.** -/
theorem localPaymentOK_H8 : H8.LocalPaymentOK :=
  localPaymentOK_of_checks h8_matches h8_facts h8_xmin h8_checks

/-- **The leaf endpoint of the band `H8`.** -/
theorem leafOK_H8 : H8.LeafOK := leafOK_of_checks h8_matches h8_facts h8_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
