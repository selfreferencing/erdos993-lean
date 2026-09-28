import Erdos993Lean.Analytic.TailCert.Compute.Bands

/-!
# Band certificate 09 of the repaired T3 potential (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  `checkRow 9 = true`: the cell checker
(`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`, sound by `TailCert.checkBand_sound`) certifies
`Tail.T3UNonneg λ t_j a(9, j) ℓ(9, j)` for every `λ ∈ [3/4, 4/5]` and the five Laplace
parameters `t_j ∈ {0, 1/20, 1/10, 1/5, 3/10}` (Soul's `SOUL/O3/repaired_band_10_t_*.json`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.TailCert.Checks

/-- The five certificates of band `9` (`λ ∈ [3/4, 4/5]`), by `native_decide`. -/
theorem band_09 : Compute.checkRow 9 = true := by native_decide

end Erdos993Lean.Analytic.TailCert.Checks
