import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.Low

/-!
# O2 certificate check: band `low`, root box 10 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot lowSD 10 (lowToks.getD 10 "") = true`: the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`) certifies the
root box `λ ∈ [lo, hi]`, `x ∈ [edges[10], edges[11]]` of the band.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Band `low`, root box 10, by `native_decide`. -/
theorem low_r10 : checkRoot lowSD 10 (lowToks.getD 10 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
