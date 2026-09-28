import Erdos993Lean.Analytic.TailCert.Compute.Bands

/-!
# Band certificate 07 of the repaired T3 potential (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  `checkRow 7 = true`: the cell checker
(`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`, sound by `TailCert.checkBand_sound`) certifies
`Tail.T3UNonneg λ t_j a(7, j) ℓ(7, j)` for every `λ ∈ [13/20, 7/10]` and the five Laplace
parameters `t_j ∈ {0, 1/20, 1/10, 1/5, 3/10}` (Soul's `SOUL/O3/repaired_band_08_t_*.json`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.TailCert.Checks

/-- The five certificates of band `7` (`λ ∈ [13/20, 7/10]`), by `native_decide`. -/
theorem band_07 : Compute.checkRow 7 = true := by native_decide

end Erdos993Lean.Analytic.TailCert.Checks
