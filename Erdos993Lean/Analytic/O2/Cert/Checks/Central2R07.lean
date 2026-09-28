import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.Central2

/-!
# O2 certificate check: band `central_2`, root box 7 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot central2SD 7 (central2Toks.getD 7 "") = true`: the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`) certifies the
root box `λ ∈ [lo, hi]`, `x ∈ [edges[7], edges[8]]` of the band.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Band `central_2`, root box 7, by `native_decide`. -/
theorem central2_r07 : checkRoot central2SD 7 (central2Toks.getD 7 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
