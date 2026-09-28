import Mathlib
import Erdos993Lean.Analytic.Reserve.Cert.Sound
import Erdos993Lean.Analytic.Reserve.Cert.Leaf
import Erdos993Lean.Analytic.Reserve.Cert.Checks.Box0
import Erdos993Lean.Analytic.Reserve.Cert.Checks.Box1
import Erdos993Lean.Analytic.Reserve.Cert.Checks.Box2
import Erdos993Lean.Analytic.Reserve.Cert.Checks.Box3

/-!
# O1's finite box `BoxOK` and the leaf base `LeafOK` on the four bands (lane A12, optional target)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  Sources: Astra's O1 cell certificates
(`LEAN/referee/astra_o1/snapshot_0730/lower_alternate_reserve_band_0.json`, `sharp_reserve_v4_band_{1,2,3}.json`) and
the referee's independent replay (`LEAN/referee/REVIEW_ASTRA_O1_REPLAY.md`).

**Theorems.**
* **`boxOK_band0 : BoxOK band0`**, …, **`boxOK_band3`**: the comparisons `CompOK` on the finite box
  `λ ∈ [lo, hi]`, `0 ≤ T ≤ 6`, `lmass λ T ≤ Y ≤ 4`, from `boxOK_of_check`
  (`Erdos993Lean/Analytic/Reserve/Cert/Sound.lean`, standard axioms) and the four band checks
  `Checks.box_0` … `box_3`: Astra's 33,267 / 79,158 / 186,304 / 107,872 cells pass the cell checker
  (`Erdos993Lean/Analytic/Reserve/Cert/Compute/Cell.lean`) and cover the box (two cells of band 2 pass after one
  bisection of the checker's fallback).  No hypothesis: the checker encloses `E` directly and does not use
  `EntropyOK` (its floors `E ≥ 0`, Pinsker are not needed).
* `leafOK_band0 … leafOK_band3` (re-exported from `Erdos993Lean/Analytic/Reserve/Cert/Leaf.lean`, kernel-checked,
  standard axioms).

**Trust.**  `native_decide` is used exactly 4 times, once in each of
`Erdos993Lean/Analytic/Reserve/Cert/Checks/Box0.lean` … `Box3.lean`:
`Checks.box_K : checkBand lo hi D aCoef gDen trieK = true`.  They trust the Lean compiler (`Lean.ofReduceBool`,
`Lean.trustCompiler`), here including the natively compiled libraries `Erdos993LeanReserveCertCompute` (this lane)
and `Erdos993LeanTailCertCompute` (lane A10's interval core), and the C compiler used by Lake.  The checker and its
data are plain structural recursion in Lean core (no `partial`, `unsafe`, `implemented_by`, `extern`); the
soundness proofs (`Real.lean`, `CellSound.lean`, `Sound.lean`), the leaf base and this glue use only `propext`,
`Classical.choice`, `Quot.sound`.

**Build.**  Not part of the default target.  Build the check modules one at a time by name, then this module:
`lake build Erdos993Lean.Analytic.Reserve.Cert.Checks.Box0` (… `Box3`), `lake build Erdos993Lean.Analytic.Reserve.Cert.Main`.
-/

namespace Erdos993Lean.Analytic.Reserve.Cert

open Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.Reserve.Cert.Compute

/-- **O1's finite box on band 0** (`λ ∈ [1/3, 3/5]`, `D = 8/5`, `α = q/2`, `γ = λ(3 + λ)/11`): Astra's 33,267
cells, checked by `native_decide` (`Checks.box_0`). -/
theorem boxOK_band0 : BoxOK band0 := boxOK_of_check band0 trie0 Checks.box_0

/-- **O1's finite box on band 1** (`λ ∈ [3/5, 4/5]`, `D = 7/5`, `α = 23q/50`, `γ = λ(3 + λ)/13`): Astra's 79,158
cells, checked by `native_decide` (`Checks.box_1`). -/
theorem boxOK_band1 : BoxOK band1 := boxOK_of_check band1 trie1 Checks.box_1

/-- **O1's finite box on band 2** (`λ ∈ [4/5, 13/10]`, `D = 6/5`, `α = 23q/50`, `γ = λ(3 + λ)/13`): Astra's
186,304 cells, checked by `native_decide` (`Checks.box_2`). -/
theorem boxOK_band2 : BoxOK band2 := boxOK_of_check band2 trie2 Checks.box_2

/-- **O1's finite box on band 3** (`λ ∈ [13/10, 8/5]`, `D = 7/5`, `α = 23q/50`, `γ = λ(3 + λ)/13`): Astra's
107,872 cells, checked by `native_decide` (`Checks.box_3`). -/
theorem boxOK_band3 : BoxOK band3 := boxOK_of_check band3 trie3 Checks.box_3

/-- The finite boxes and the leaf bases of the four bands together (the form consumed by lane A11's
`bandVar_of_ok`). -/
theorem box_and_leaf :
    (BoxOK band0 ∧ LeafOK band0) ∧ (BoxOK band1 ∧ LeafOK band1) ∧ (BoxOK band2 ∧ LeafOK band2) ∧
      (BoxOK band3 ∧ LeafOK band3) :=
  ⟨⟨boxOK_band0, leafOK_band0⟩, ⟨boxOK_band1, leafOK_band1⟩, ⟨boxOK_band2, leafOK_band2⟩,
    ⟨boxOK_band3, leafOK_band3⟩⟩

end Erdos993Lean.Analytic.Reserve.Cert
