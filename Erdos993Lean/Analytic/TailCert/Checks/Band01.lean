import Erdos993Lean.Analytic.TailCert.Compute.Bands

/-!
# Band certificate 01 of the repaired T3 potential (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  `checkRow 1 = true`: the cell checker
(`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`, sound by `TailCert.checkBand_sound`) certifies
`Tail.T3UNonneg λ t_j a(1, j) ℓ(1, j)` for every `λ ∈ [9/25, 2/5]` and the five Laplace
parameters `t_j ∈ {0, 1/20, 1/10, 1/5, 3/10}` (Soul's `SOUL/O3/repaired_band_02_t_*.json`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.TailCert.Checks

/-- The five certificates of band `1` (`λ ∈ [9/25, 2/5]`), by `native_decide`. -/
theorem band_01 : Compute.checkRow 1 = true := by native_decide

end Erdos993Lean.Analytic.TailCert.Checks
