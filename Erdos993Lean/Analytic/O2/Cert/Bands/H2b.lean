import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR00
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR01
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR02
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR03
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR04
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR05
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR06
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR07
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR08
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR09
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR10
import Erdos993Lean.Analytic.O2.Cert.Checks.H2bR11

/-!
# O2 certificates: the band `H2b` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `H2b` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `H2b`, `γ = 2`): the checker's tables are A16's (`h2b_matches`, `decide +kernel`), its range and sign facts
(`h2b_facts`), the twelve root-box checks (`Checks/H2bR00` … `Checks/H2bR11`, one `native_decide` each), hence
**`localPaymentOK_H2b`** and **`leafOK_H2b`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `H2b` are A16's. -/
theorem h2b_matches : Matches h2bSD H2b :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `H2b`. -/
theorem h2b_facts : BandFacts h2bSD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `H2b` starts at `x = 2⁻¹⁶`. -/
theorem h2b_xmin : H2b.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `H2b` pass. -/
theorem h2b_checks : ∀ i < 12, checkRoot h2bSD i (h2bToks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact h2b_r00
  · exact h2b_r01
  · exact h2b_r02
  · exact h2b_r03
  · exact h2b_r04
  · exact h2b_r05
  · exact h2b_r06
  · exact h2b_r07
  · exact h2b_r08
  · exact h2b_r09
  · exact h2b_r10
  · exact h2b_r11

/-- **The certified local payment of the band `H2b`.** -/
theorem localPaymentOK_H2b : H2b.LocalPaymentOK :=
  localPaymentOK_of_checks h2b_matches h2b_facts h2b_xmin h2b_checks

/-- **The leaf endpoint of the band `H2b`.** -/
theorem leafOK_H2b : H2b.LeafOK := leafOK_of_checks h2b_matches h2b_facts h2b_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
