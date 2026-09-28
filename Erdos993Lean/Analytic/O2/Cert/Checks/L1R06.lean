import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.L1

/-!
# O2 certificate check: gap row `L1`, root box 6 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot l1SD 6 (l1Toks.getD 6 "") = true`, by the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Gap row `L1`, root box 6, by `native_decide`. -/
theorem l1_r06 : checkRoot l1SD 6 (l1Toks.getD 6 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
