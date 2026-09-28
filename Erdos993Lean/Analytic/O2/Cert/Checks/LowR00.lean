import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.Low

/-!
# O2 certificate check: band `low`, root box 0 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot lowSD 0 (lowToks.getD 0 "") = true`: the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`) certifies the
root box `λ ∈ [lo, hi]`, `x ∈ [edges[0], edges[1]]` of the band.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Band `low`, root box 0, by `native_decide`. -/
theorem low_r00 : checkRoot lowSD 0 (lowToks.getD 0 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
