import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.Central3

/-!
# O2 certificate check: band `central_3`, root box 3 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot central3SD 3 (central3Toks.getD 3 "") = true`: the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`) certifies the
root box `λ ∈ [lo, hi]`, `x ∈ [edges[3], edges[4]]` of the band.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Band `central_3`, root box 3, by `native_decide`. -/
theorem central3_r03 : checkRoot central3SD 3 (central3Toks.getD 3 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
