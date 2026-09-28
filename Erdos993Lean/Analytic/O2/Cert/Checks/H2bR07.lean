import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.H2b

/-!
# O2 certificate check: gap row `H2b`, root box 7 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot h2bSD 7 (h2bToks.getD 7 "") = true`, by the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Gap row `H2b`, root box 7, by `native_decide`. -/
theorem h2b_r07 : checkRoot h2bSD 7 (h2bToks.getD 7 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
