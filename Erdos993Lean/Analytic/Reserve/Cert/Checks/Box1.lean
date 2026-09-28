import Erdos993Lean.Analytic.Reserve.Cert.Compute.Cell
import Erdos993Lean.Analytic.Reserve.Cert.Compute.Trie1

/-!
# The finite box of band 1 checked natively (lane A12)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  `checkBand (3/5) (4/5) (7/5) (23/50) 13 trie1 = true`:
the cell checker (`Erdos993Lean/Analytic/Reserve/Cert/Compute/Cell.lean`, sound by `Cert.boxOK_of_check`) certifies
Astra's 79,158 cells of band 1 (`λ ∈ [3/5, 4/5]`, `D = 7/5`, `α = 23q/50`, `γ = λ(3 + λ)/13`;
`LEAN/referee/astra_o1/snapshot_0730/sharp_reserve_v4_band_1.json`) and their cover of the box `T ∈ [0, 6]`, `r ∈ [0, 1]`.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the natively
compiled library `Erdos993LeanReserveCertCompute` and lane A10's `Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Reserve.Cert.Checks

open Erdos993Lean.Analytic.Reserve.Cert.Compute

/-- The finite box of band 1 (`λ ∈ [3/5, 4/5]`): Astra's 79,158 cells pass the cell checker and cover the
box, by `native_decide`. -/
theorem box_1 : checkBand (3/5) (4/5) (7/5) (23/50) 13 trie1 = true := by native_decide

end Erdos993Lean.Analytic.Reserve.Cert.Checks
