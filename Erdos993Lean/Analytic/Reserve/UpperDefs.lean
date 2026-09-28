import Mathlib
import Erdos993Lean.Analytic.Reserve.Defs
import Erdos993Lean.Analytic.Reserve.Step

/-!
# O1 on the upper band `[8/5, 7/3]`: the signed-port reserve (shared definitions, lanes A14 and A15)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  Source: Astra's upper band
(`ASTRA/O1/UPPER_SHARP_SIGNED_PORT_PROOF.md`, reviewed snapshot `LEAN/referee/astra_o1/snapshot_0845`), adopted by the
Lean lead on 2026-09-28 after the lead's recompute and two foreground Opus reviews
(`LEAN/referee/REVIEW_ASTRA_O1_UPPER_PROOF.md`, `LEAN/referee/REVIEW_ASTRA_O1_UPPER_REPLAY.md`).

On `λ ∈ [8/5, 7/3]` the reserve is `α y + β u + γ u²/y` with `α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100` and the cap
`A = 1 + 3q/5` (`D = 8/5`).  Lane A11's induction (`Reserve/Step.lean`, `Reserve/Assembly.lean`) consumes a per-activity
`StepCert γ λ α β A`; this file names the three obligations that produce it:
* `UpperBoxOK` — on the finite box `0 ≤ T ≤ 6`, `lmass λ T ≤ Y ≤ 4`: `Z > 0`, `β² T ≤ 8 α Z` (with the Pinsker half of
  `EntropyOK` this gives `CC ≥ 0`: `compCC_nonneg_of_entropy`), `CB ≥ 0`, `BC ≥ 0` (Astra's 617,294-cell certificate;
  lane A15);
* `UpperTailOK` — `Z > 0`, `CC ≥ 0`, `CB ≥ 0`, `BC ≥ 0` when `Y ≥ 4` or `T ≥ 6` (analytic; lane A14);
* `UpperLeafOK` — the selected-leaf base, in `StepCert`'s form (lane A14).
Do not change this file in a lane; ask the lead.
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

/-- `α = q/2` on the upper band. -/
noncomputable def uAlpha (lam : ℝ) : ℝ := actQ lam / 2
/-- `β = (λ − 1)/27` on the upper band. -/
noncomputable def uBeta (lam : ℝ) : ℝ := (lam - 1) / 27
/-- `γ = 31λ/100` on the upper band. -/
noncomputable def uGamma (lam : ℝ) : ℝ := 31 * lam / 100
/-- `A = 1 + 3q/5` (`D = 8/5`) on the upper band. -/
noncomputable def uCapA (lam : ℝ) : ℝ := 1 + 3 / 5 * actQ lam

/-- **The finite box of the upper band** (Astra's centered-derivative cell certificate): for `λ ∈ [8/5, 7/3]`,
`0 ≤ T ≤ 6`, `lmass λ T ≤ Y ≤ 4`: `Z > 0`, `β² T ≤ 8 α Z`, `CB ≥ 0`, `BC ≥ 0`. -/
def UpperBoxOK : Prop :=
  ∀ lam T Y : ℝ, 8 / 5 ≤ lam → lam ≤ 7 / 3 → 0 ≤ T → T ≤ 6 → lmass lam T ≤ Y → Y ≤ 4 →
    0 < cZ (uGamma lam) lam T Y ∧
      uBeta lam ^ 2 * T ≤ 8 * uAlpha lam * cZ (uGamma lam) lam T Y ∧
      0 ≤ compCB (uGamma lam) lam (uAlpha lam) (uBeta lam) T Y ∧
      0 ≤ compBC (uGamma lam) lam (uAlpha lam) (uBeta lam) (uCapA lam) T Y

/-- **The analytic tails of the upper band**: for `λ ∈ [8/5, 7/3]`, `T ≥ 0`, `Y ≥ lmass λ T`, and `Y ≥ 4` or
`T ≥ 6`: `Z > 0`, `CC ≥ 0`, `CB ≥ 0`, `BC ≥ 0`. -/
def UpperTailOK : Prop :=
  ∀ lam T Y : ℝ, 8 / 5 ≤ lam → lam ≤ 7 / 3 → 0 ≤ T → lmass lam T ≤ Y → (4 ≤ Y ∨ 6 ≤ T) →
    0 < cZ (uGamma lam) lam T Y ∧
      0 ≤ compCC (uGamma lam) lam (uAlpha lam) (uBeta lam) T Y ∧
      0 ≤ compCB (uGamma lam) lam (uAlpha lam) (uBeta lam) T Y ∧
      0 ≤ compBC (uGamma lam) lam (uAlpha lam) (uBeta lam) (uCapA lam) T Y

/-- **The selected-leaf base of the upper band**, in `StepCert`'s form. -/
def UpperLeafOK : Prop :=
  ∀ lam : ℝ, 8 / 5 ≤ lam → lam ≤ 7 / 3 →
    uAlpha lam * lmass lam 0 + uBeta lam * msg lam 0 + uGamma lam * msg lam 0 ^ 2 / lmass lam 0 ≤
      uCapA lam * msg lam 0 - msg lam 0 * (1 - msg lam 0)

end Erdos993Lean.Analytic.Reserve
