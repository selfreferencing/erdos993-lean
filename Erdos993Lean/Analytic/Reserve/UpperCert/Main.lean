import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperCert.Sound
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece0
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece1
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece2
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece3
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece4
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece5
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece6
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece7
import Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece8

/-!
# O1's upper finite box `UpperBoxOK` (lane A15, optional target)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  Sources: Astra's upper-band certificate
(`LEAN/referee/astra_o1/snapshot_0845/upper_centered_derivative_certificate.json`, SHA-256 f56c5101…764d, 617,294 cells)
and the referee's independent replay (`LEAN/referee/REVIEW_ASTRA_O1_UPPER_REPLAY.md`).

**Theorem (`upperBoxOK : UpperBoxOK`).**  For `λ ∈ [8/5, 7/3]`, `0 ≤ T ≤ 6`, `lmass λ T ≤ Y ≤ 4`: `Z > 0`,
`β² T ≤ 8 α Z`, `CB ≥ 0`, `BC ≥ 0` with the upper coefficients `α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100`,
`A = 1 + 3q/5` (`Reserve/UpperDefs.lean`).  Proof: `upperBoxOK_of_covered` (`UpperCert/Sound.lean`, standard axioms)
and the cover of the root box `rootU = [8/5, 7/3] × [0, 6] × [0, 1]` of `(λ, T, r)` by the nine pieces of the refined
trie (`covered_rootU`: the halvings of `covered_split` down to the pieces, each piece covered by
`covered_of_checkAt` and its native check `Checks.piece_K`).

The trie: Astra's 617,294 cells (their paths, re-verified to be a complete binary partition of the root box), with the
28,367 cells that the cell checker `cellOKU` does not pass directly split greedily (at most 8 leaves per cell; 670,014
leaves in all, refined trie SHA-256 `1838d5ccc0be449ee03bc9635a1e99f63ed023717023c7736e39cbe0b24fa9af`), cut into
nine maximal subtrees of at most 120,000 leaves (100963, 66492, 113720, 73138, 46662, 85076, 24118, 81352 and 78493
leaves).  The cell checker encloses the four comparisons with lane A10's 64-bit fixed-point intervals (monotone
enclosures, the normalized forms of `UpperCert/Forms.lean`, the floor of `E` from lane A13's `entropyOK`); the checker
and its data are plain structural recursion in Lean core (no `partial`, `unsafe`, `implemented_by`, `extern`).

**Trust.**  `native_decide` is used exactly 9 times, once in each of
`Erdos993Lean/Analytic/Reserve/UpperCert/Checks/Piece0.lean` … `Piece8.lean`:
`Checks.piece_K : checkAt c_K pieceK = true`.  They trust the Lean compiler (`Lean.ofReduceBool`,
`Lean.trustCompiler`), here including the natively compiled libraries `Erdos993LeanUpperCertCompute` (this lane),
`Erdos993LeanReserveCertCompute` (lane A12) and `Erdos993LeanTailCertCompute` (lane A10's interval core), and the C
compiler used by Lake.  The soundness proofs (`Forms.lean`, `CellSound.lean`, `Sound.lean`) and this glue use only
`propext`, `Classical.choice`, `Quot.sound`.

**Build.**  Not part of the default target.  Build the check modules one at a time by name, then this module:
`lake build Erdos993Lean.Analytic.Reserve.UpperCert.Checks.Piece0` (… `Piece8`),
`lake build Erdos993Lean.Analytic.Reserve.UpperCert.Main`.
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert

open Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.Reserve.Cert.Compute
open Erdos993Lean.Analytic.Reserve.UpperCert.Compute

/-- **The root box of the upper band is covered**: the nine pieces of the refined trie, glued by the halvings of the
skeleton `012PPP120P12PPPPP` (preorder; `'0'`, `'1'`, `'2'` halve `λ`, `T`, `r`; `P` a piece). -/
theorem covered_rootU : Covered rootU :=
  covered_split _ 0
    (covered_split _ 1
      (covered_split _ 2
        (covered_of_checkAt Checks.piece_0)
        (covered_of_checkAt Checks.piece_1))
      (covered_of_checkAt Checks.piece_2))
    (covered_split _ 1
      (covered_split _ 2
        (covered_split _ 0
          (covered_of_checkAt Checks.piece_3)
          (covered_split _ 1
            (covered_split _ 2
              (covered_of_checkAt Checks.piece_4)
              (covered_of_checkAt Checks.piece_5))
            (covered_of_checkAt Checks.piece_6)))
        (covered_of_checkAt Checks.piece_7))
      (covered_of_checkAt Checks.piece_8))

/-- **O1's upper finite box** (Astra's certificate, refined, checked by the verified cell checker): for
`λ ∈ [8/5, 7/3]`, `0 ≤ T ≤ 6`, `lmass λ T ≤ Y ≤ 4`: `Z > 0`, `β² T ≤ 8 α Z`, `CB ≥ 0`, `BC ≥ 0`. -/
theorem upperBoxOK : UpperBoxOK := upperBoxOK_of_covered covered_rootU

end Erdos993Lean.Analytic.Reserve.UpperCert
