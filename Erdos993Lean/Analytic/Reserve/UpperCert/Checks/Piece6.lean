import Erdos993Lean.Analytic.Reserve.UpperCert.Compute.Cell
import Erdos993Lean.Analytic.Reserve.UpperCert.Compute.Piece6

/-!
# The upper finite box, piece 6, checked natively (lane A15)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  `checkAt c piece6 = true` for the sub-box
`c = highHalf (highHalf (lowHalf (lowHalf (highHalf rootU 0) 1) 2) 0) 1`
of the root box `[8/5, 7/3] × [0, 6] × [0, 1]`: the cell checker
(`Erdos993Lean/Analytic/Reserve/UpperCert/Compute/Cell.lean`, sound by `UpperCert.covered_of_checkAt`) certifies the
24118 leaves of piece 6 of the refined upper trie and their cover of the sub-box.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the natively
compiled libraries `Erdos993LeanUpperCertCompute`, lane A12's `Erdos993LeanReserveCertCompute` and lane A10's
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert.Checks

open Erdos993Lean.Analytic.Reserve.Cert.Compute Erdos993Lean.Analytic.Reserve.UpperCert.Compute

/-- Piece 6 of the upper finite box: 24118 cells pass the cell checker and cover their sub-box, by
`native_decide`. -/
theorem piece_6 :
    checkAt (highHalf (highHalf (lowHalf (lowHalf (highHalf rootU 0) 1) 2) 0) 1)
      piece6 = true := by
  native_decide

end Erdos993Lean.Analytic.Reserve.UpperCert.Checks
