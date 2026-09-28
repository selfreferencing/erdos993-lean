import Erdos993Lean.Analytic.Reserve.UpperCert.Compute.Cell
import Erdos993Lean.Analytic.Reserve.UpperCert.Compute.Piece4

/-!
# The upper finite box, piece 4, checked natively (lane A15)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  `checkAt c piece4 = true` for the sub-box
`c = lowHalf (lowHalf (highHalf (lowHalf (lowHalf (highHalf rootU 0) 1) 2) 0) 1) 2`
of the root box `[8/5, 7/3] × [0, 6] × [0, 1]`: the cell checker
(`Erdos993Lean/Analytic/Reserve/UpperCert/Compute/Cell.lean`, sound by `UpperCert.covered_of_checkAt`) certifies the
46662 leaves of piece 4 of the refined upper trie and their cover of the sub-box.

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the natively
compiled libraries `Erdos993LeanUpperCertCompute`, lane A12's `Erdos993LeanReserveCertCompute` and lane A10's
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert.Checks

open Erdos993Lean.Analytic.Reserve.Cert.Compute Erdos993Lean.Analytic.Reserve.UpperCert.Compute

/-- Piece 4 of the upper finite box: 46662 cells pass the cell checker and cover their sub-box, by
`native_decide`. -/
theorem piece_4 :
    checkAt (lowHalf (lowHalf (highHalf (lowHalf (lowHalf (highHalf rootU 0) 1) 2) 0) 1) 2)
      piece4 = true := by
  native_decide

end Erdos993Lean.Analytic.Reserve.UpperCert.Checks
