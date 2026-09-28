import Erdos993Lean.Analytic.O2.Cert.Compute.Tokens.UpperShoulder

/-!
# O2 certificate check: band `upper_shoulder`, root box 9 (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  `checkRoot upperShoulderSD 9 (upperShoulderToks.getD 9 "") = true`: the
cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `Cert.rootOK_sound`) certifies the
root box `λ ∈ [lo, hi]`, `x ∈ [edges[9], edges[10]]` of the band.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (this lane) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.O2.Cert.Checks

open Erdos993Lean.Analytic.O2.Cert.Compute

/-- Band `upper_shoulder`, root box 9, by `native_decide`. -/
theorem upperShoulder_r09 : checkRoot upperShoulderSD 9 (upperShoulderToks.getD 9 "") = true := by native_decide

end Erdos993Lean.Analytic.O2.Cert.Checks
