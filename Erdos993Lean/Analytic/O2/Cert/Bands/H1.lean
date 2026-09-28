import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R00
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R01
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R02
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R03
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R04
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R05
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R06
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R07
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R08
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R09
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R10
import Erdos993Lean.Analytic.O2.Cert.Checks.H1R11

/-!
# O2 certificates: the band `H1` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `H1` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `H1`, `γ = 2`): the checker's tables are A16's (`h1_matches`, `decide +kernel`), its range and sign facts
(`h1_facts`), the twelve root-box checks (`Checks/H1R00` … `Checks/H1R11`, one `native_decide` each), hence
**`localPaymentOK_H1`** and **`leafOK_H1`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `H1` are A16's. -/
theorem h1_matches : Matches h1SD H1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `H1`. -/
theorem h1_facts : BandFacts h1SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `H1` starts at `x = 2⁻¹⁶`. -/
theorem h1_xmin : H1.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `H1` pass. -/
theorem h1_checks : ∀ i < 12, checkRoot h1SD i (h1Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact h1_r00
  · exact h1_r01
  · exact h1_r02
  · exact h1_r03
  · exact h1_r04
  · exact h1_r05
  · exact h1_r06
  · exact h1_r07
  · exact h1_r08
  · exact h1_r09
  · exact h1_r10
  · exact h1_r11

/-- **The certified local payment of the band `H1`.** -/
theorem localPaymentOK_H1 : H1.LocalPaymentOK :=
  localPaymentOK_of_checks h1_matches h1_facts h1_xmin h1_checks

/-- **The leaf endpoint of the band `H1`.** -/
theorem leafOK_H1 : H1.LeafOK := leafOK_of_checks h1_matches h1_facts h1_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
