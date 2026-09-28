import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR00
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR01
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR02
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR03
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR04
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR05
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR06
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR07
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR08
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR09
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR10
import Erdos993Lean.Analytic.O2.Cert.Checks.H4bR11

/-!
# O2 certificates: the band `H4b` (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The band `H4b` of `Erdos993Lean/Analytic/O2/Defs.lean`
(gap row `H4b`, `γ = 2`): the checker's tables are A16's (`h4b_matches`, `decide +kernel`), its range and sign facts
(`h4b_facts`), the twelve root-box checks (`Checks/H4bR00` … `Checks/H4bR11`, one `native_decide` each), hence
**`localPaymentOK_H4b`** and **`leafOK_H4b`** by `localPaymentOK_of_checks`, `leafOK_of_checks`.
-/

namespace Erdos993Lean.Analytic.O2.Cert.Bands

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute
open Erdos993Lean.Analytic.O2.Cert.Checks

/-- The checker's tables of `H4b` are A16's. -/
theorem h4b_matches : Matches h4bSD H4b :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `H4b`. -/
theorem h4b_facts : BandFacts h4bSD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `H4b` starts at `x = 2⁻¹⁶`. -/
theorem h4b_xmin : H4b.xmin = 1 / 65536 := by decide +kernel

/-- The twelve root boxes of `H4b` pass. -/
theorem h4b_checks : ∀ i < 12, checkRoot h4bSD i (h4bToks.getD i "") = true := by
  intro i hi
  interval_cases i
  · exact h4b_r00
  · exact h4b_r01
  · exact h4b_r02
  · exact h4b_r03
  · exact h4b_r04
  · exact h4b_r05
  · exact h4b_r06
  · exact h4b_r07
  · exact h4b_r08
  · exact h4b_r09
  · exact h4b_r10
  · exact h4b_r11

/-- **The certified local payment of the band `H4b`.** -/
theorem localPaymentOK_H4b : H4b.LocalPaymentOK :=
  localPaymentOK_of_checks h4b_matches h4b_facts h4b_xmin h4b_checks

/-- **The leaf endpoint of the band `H4b`.** -/
theorem leafOK_H4b : H4b.LeafOK := leafOK_of_checks h4b_matches h4b_facts h4b_checks

end Erdos993Lean.Analytic.O2.Cert.Bands
