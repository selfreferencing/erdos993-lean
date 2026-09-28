import Erdos993Lean.Analytic.Reserve.Cert.Compute.Cell
import Erdos993Lean.Analytic.Reserve.Cert.Compute.Trie0

/-!
# The finite box of band 0 checked natively (lane A12)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  `checkBand (1/3) (3/5) (8/5) (1/2) 11 trie0 = true`:
the cell checker (`Erdos993Lean/Analytic/Reserve/Cert/Compute/Cell.lean`, sound by `Cert.boxOK_of_check`) certifies
Astra's 33,267 cells of band 0 (`λ ∈ [1/3, 3/5]`, `D = 8/5`, `α = q/2`, `γ = λ(3 + λ)/11`;
`LEAN/referee/astra_o1/snapshot_0730/lower_alternate_reserve_band_0.json`) and their cover of the box `T ∈ [0, 6]`, `r ∈ [0, 1]`.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the natively
compiled library `Erdos993LeanReserveCertCompute` and lane A10's `Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Reserve.Cert.Checks

open Erdos993Lean.Analytic.Reserve.Cert.Compute

/-- The finite box of band 0 (`λ ∈ [1/3, 3/5]`): Astra's 33,267 cells pass the cell checker and cover the
box, by `native_decide`. -/
theorem box_0 : checkBand (1/3) (3/5) (8/5) (1/2) 11 trie0 = true := by native_decide

end Erdos993Lean.Analytic.Reserve.Cert.Checks
