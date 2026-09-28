import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.Central1

/-!
# O2 certificate check: band `central_1`, root box 11 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot central1SD 11 (central1Toks.getD 11 "") = true`: the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`) certifies the
root box `λ ∈ [lo, hi]`, `x ∈ [edges[11], edges[12]]` of the band.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Band `central_1`, root box 11, by `native_decide`. -/
theorem central1_r11 : checkRoot central1SD 11 (central1Toks.getD 11 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
