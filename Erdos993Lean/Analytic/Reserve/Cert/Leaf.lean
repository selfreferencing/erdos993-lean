import Mathlib
import Erdos993Lean.Analytic.Reserve.Cert.Sound

/-!
# The selected-leaf base `LeafOK` on the four bands (lane A12)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  Source: `Reserve/Defs.lean` (`LeafOK`: the
selected-leaf base `α log(1+λ) + γ q²/log(1+λ) ≤ D q²`), the referee's leaf-base replay
(`LEAN/referee/REVIEW_ASTRA_O1_REPLAY.md` §LEAF BASE: thinnest margin 1.9e-3, at `λ = 13/10` in band 2).

**Theorems.**  `leafOK_band0 : LeafOK band0`, …, `leafOK_band3 : LeafOK band3`, each from `leafOK_of_check`
(`Erdos993Lean/Analytic/Reserve/Cert/Sound.lean`) and the leaf-base checker `checkLeaf`
(`Erdos993Lean/Analytic/Reserve/Cert/Compute/Cell.lean`: `aCoef ℓ/q + γ/ℓ ≤ D`, `ℓ = log(1 + λ)`, by bisection
in `λ`; it needs 2, 1, 10 and 2 cells on the four bands) **evaluated by the kernel** (`decide +kernel`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`).
-/

namespace Erdos993Lean.Analytic.Reserve.Cert

open Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.Reserve.Cert.Compute

/-- **The leaf base on band 0** (`λ ∈ [1/3, 3/5]`, `D = 8/5`, `α = q/2`, `γ = λ(3 + λ)/11`). -/
theorem leafOK_band0 : LeafOK band0 := leafOK_of_check band0 (by decide +kernel)

/-- **The leaf base on band 1** (`λ ∈ [3/5, 4/5]`, `D = 7/5`, `α = 23q/50`, `γ = λ(3 + λ)/13`). -/
theorem leafOK_band1 : LeafOK band1 := leafOK_of_check band1 (by decide +kernel)

/-- **The leaf base on band 2** (`λ ∈ [4/5, 13/10]`, `D = 6/5`, `α = 23q/50`, `γ = λ(3 + λ)/13`). -/
theorem leafOK_band2 : LeafOK band2 := leafOK_of_check band2 (by decide +kernel)

/-- **The leaf base on band 3** (`λ ∈ [13/10, 8/5]`, `D = 7/5`, `α = 23q/50`, `γ = λ(3 + λ)/13`). -/
theorem leafOK_band3 : LeafOK band3 := leafOK_of_check band3 (by decide +kernel)

end Erdos993Lean.Analytic.Reserve.Cert
