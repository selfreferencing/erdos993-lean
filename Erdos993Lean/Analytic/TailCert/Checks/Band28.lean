import Erdos993Lean.Analytic.TailCert.Compute.Bands

/-!
# Band certificate 28 of the repaired T3 potential (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  `checkRow 28 = true`: the cell checker
(`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`, sound by `TailCert.checkBand_sound`) certifies
`Tail.T3UNonneg λ t_j a(28, j) ℓ(28, j)` for every `λ ∈ [41/20, 9/4]` and the five Laplace
parameters `t_j ∈ {0, 1/20, 1/10, 1/5, 3/10}` (Soul's `SOUL/O3/repaired_band_29_t_*.json`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.TailCert.Checks

/-- The five certificates of band `28` (`λ ∈ [41/20, 9/4]`), by `native_decide`. -/
theorem band_28 : Compute.checkRow 28 = true := by native_decide

end Erdos993Lean.Analytic.TailCert.Checks
