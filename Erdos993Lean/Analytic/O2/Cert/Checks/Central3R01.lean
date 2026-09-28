import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.Central3

/-!
# O2 certificate check: band `central_3`, root box 1 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot central3SD 1 (central3Toks.getD 1 "") = true`: the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`) certifies the
root box `λ ∈ [lo, hi]`, `x ∈ [edges[1], edges[2]]` of the band.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Band `central_3`, root box 1, by `native_decide`. -/
theorem central3_r01 : checkRoot central3SD 1 (central3Toks.getD 1 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
