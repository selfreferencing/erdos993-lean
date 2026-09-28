import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR00
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR01
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR02
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR03
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR04
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR05
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR06
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR07
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR08
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR09
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR10
import Erdos993Lean.Analytic.O2.Cert.Checks.H3bR11

/-!
# O2 certificates: the band `H3b` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `H3b` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `H3b`, `γ = 2`): the checker's tables are A16's (`h3b_matches`, `decide +kernel`), its range and sign facts
(`h3b_facts`), the twelve root-box checks (`Checks/H3bR00` … `Checks/H3bR11`, one `native_decide` each), hence
**`localPaymentOK_H3b`** and **`leafOK_H3b`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `H3b` are A16's. -/
theorem h3b_matches : Matches h3bSD H3b :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `H3b`. -/
theorem h3b_facts : BandFacts h3bSD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `H3b` starts at `x = 2⁻¹⁶`. -/
theorem h3b_xmin : H3b.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `H3b` pass. -/
theorem h3b_checks : ∀ i < 12, checkRoot h3bSD i (h3bToks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact h3b_r00
  · exact h3b_r01
  · exact h3b_r02
  · exact h3b_r03
  · exact h3b_r04
  · exact h3b_r05
  · exact h3b_r06
  · exact h3b_r07
  · exact h3b_r08
  · exact h3b_r09
  · exact h3b_r10
  · exact h3b_r11

/-- **The certified local payment of the band `H3b`.** -/
theorem localPaymentOK_H3b : H3b.LocalPaymentOK :=
  localPaymentOK_of_checks h3b_matches h3b_facts h3b_xmin h3b_checks

/-- **The leaf endpoint of the band `H3b`.** -/
theorem leafOK_H3b : H3b.LeafOK := leafOK_of_checks h3b_matches h3b_facts h3b_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
