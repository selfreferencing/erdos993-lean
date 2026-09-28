import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Core
import Erdos993Lean.Analytic.NoValley.FiniteRange
import Erdos993Lean.Analytic.NoValley.LossForm
import Erdos993Lean.Analytic.NoValley.FibreHalf

/-!
# T1 Theorem 6.1 with the explicit fibre bound `h = P − L̄`

Source: T1 (`ProofRuns/2026-09-27_zhang_review/reports/T1.md`), §6, Theorem 6.1 ("With `h = P − L̄`
(Props 4.2/4.3) ... If (H1)–(H3) hold with `θ < Θ`, there is no weak valley at `k`.  Proof:
Theorem 3.1 + Lemma 5.1"), and §5 last line / §10 (iii) (the large-`M` tail in closed form).

This module assembles the pieces: the loss form (Theorem 3.1, `NoValley/LossForm.lean`) gives the
fibre bound `h(M) = P(M) − L(M)` with `ν = aμ̃` whenever `Φ_M ≤ L(M)` on the integers; beyond an
integer `Mb ≥ M_big` the closed-form fallback of `NoValley/FiniteRange.lean` takes over; `t1Core`
(`NoValley/Core.lean`) turns the threshold condition into the no-valley property.

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

* `explicitThreshold_of_lossForm`: `ExplicitThreshold q m θ D T M1` from multipliers `μ̃ > 0`, `c`,
  loss bounds `L(M) ≥ Φ_M(i)` (all integers `i`, `M < Mb`), and the Lemma 5.1 data for
  `h = P − L` on `[0, Mb)`, with the threshold `aμ̃ θ q(1 − q) m < α − γDm − ∑ S ΔT`.
  (For all `q`, `L(M)` is supplied by `prop43_max`, `NoValley/FibreGeneral.lean`.)
* `noValleyAt_of_lossForm`: **T1 Theorem 6.1 (explicit fibre bound)**, the no-valley property.
* `explicitThreshold_half`, `noValleyAt_half`: the same at `q = 1/2` with the closed-form fibre
  bound of T1 Proposition 4.2 (`fibreHalf`, `c = 0`, `ν = μ`).
-/

namespace Erdos993Lean.Analytic.NoValley

open Finset

/-- **T1 Theorem 6.1 with `h = P − L` (threshold form).**  Let `0 < q < 1`, `μ̃ > 0`, `γ > 0`, and
`L(M) ≥ Φ_M(i)` for all integers `i` and all `M < Mb`, where `Mb ≥ M1` is an integer with
`Mb ≥ M_big(α, β, γ, m; −c²/(4aμ̃) − 1/q − 1/(1 − q))`.  If the quadratic minorant `π` lies below
`P − L` on `[M1, Mb)`, the tail prices `S` dominate `π − (P − L)` on `[0, M1)` (`S ≥ 0`, nonincreasing)
and `aμ̃ θ q(1 − q) m < α − γDm − ∑_{M' < M1} S(M')(T(M') − T(M' − 1))`, then T1's explicit threshold
condition holds. -/
theorem explicitThreshold_of_lossForm {q m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ} (hq0 : 0 < q)
    (hq1 : q < 1) {μ c α β γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (L S : ℕ → ℝ) (Mb : ℕ)
    (hMb : quadBig α β γ m (fibreFallback q c (lossA q * μ)) ≤ Mb) (hM1 : M1 ≤ Mb)
    (hL : ∀ M : ℕ, M < Mb → ∀ i : ℤ, lossPhi q μ c M i ≤ L M)
    (hquad : ∀ M : ℕ, M1 ≤ M → M < Mb →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 ≤ chebP q μ c M - L M)
    (hS : ∀ M : ℕ, M < M1 →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - (chebP q μ c M - L M) ≤ S M)
    (hS0 : ∀ M : ℕ, M < M1 → 0 ≤ S M) (hSmono : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M)
    (hthr : lossA q * μ * θ * (q * (1 - q)) * m <
      α - γ * D * m - ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1))) :
    ExplicitThreshold q m θ D T M1 :=
  explicitThreshold_of_pointwise hq0 hq1 (fun M => chebP q μ c M - L M) S Mb
    (mul_pos (lossA_pos q) hμ) hγ hMb hM1
    (fun M hM j => by
      rw [loss_form hq0.ne' hq1.ne μ c M j]
      linarith [hL M hM (j + 1)])
    hquad hS hS0 hSmono hthr

/-- **T1 Theorem 6.1 (explicit fibre bound `h = P − L`).**  Under the hypotheses of
`explicitThreshold_of_lossForm`, no probability mixture with `E M = m`, `E δ = 0`,
`E δ² ≤ θ q(1 − q) m`, `Var M ≤ D m` and `P(M ≤ M') ≤ T(M')` (`M' < M1`) has a weak valley. -/
theorem noValleyAt_of_lossForm {q m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    {μ c α β γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (L S : ℕ → ℝ) (Mb : ℕ)
    (hMb : quadBig α β γ m (fibreFallback q c (lossA q * μ)) ≤ Mb) (hM1 : M1 ≤ Mb)
    (hL : ∀ M : ℕ, M < Mb → ∀ i : ℤ, lossPhi q μ c M i ≤ L M)
    (hquad : ∀ M : ℕ, M1 ≤ M → M < Mb →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 ≤ chebP q μ c M - L M)
    (hS : ∀ M : ℕ, M < M1 →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - (chebP q μ c M - L M) ≤ S M)
    (hS0 : ∀ M : ℕ, M < M1 → 0 ≤ S M) (hSmono : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M)
    (hthr : lossA q * μ * θ * (q * (1 - q)) * m <
      α - γ * D * m - ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1))) :
    NoValleyAt q m θ D T M1 :=
  t1Core q m θ D T M1 hq0 hq1
    (explicitThreshold_of_lossForm hq0 hq1 hμ hγ L S Mb hMb hM1 hL hquad hS hS0 hSmono hthr)

/-- **T1 Theorem 6.1 at `q = 1/2` with the closed-form fibre bound of Proposition 4.2 (threshold
form)**: `h = fibreHalf μ` below `Mb`, `c = 0`, `ν = μ`. -/
theorem explicitThreshold_half {m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ} {μ α β γ : ℝ} (hμ : 0 < μ)
    (hγ : 0 < γ) (S : ℕ → ℝ) (Mb : ℕ)
    (hMb : quadBig α β γ m (fibreFallback (1 / 2) 0 μ) ≤ Mb) (hM1 : M1 ≤ Mb)
    (hquad : ∀ M : ℕ, M1 ≤ M → M < Mb →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 ≤ fibreHalf μ M)
    (hS : ∀ M : ℕ, M < M1 →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - fibreHalf μ M ≤ S M)
    (hS0 : ∀ M : ℕ, M < M1 → 0 ≤ S M) (hSmono : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M)
    (hthr : μ * θ * ((1 / 2 : ℝ) * (1 - 1 / 2)) * m <
      α - γ * D * m - ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1))) :
    ExplicitThreshold (1 / 2) m θ D T M1 :=
  explicitThreshold_of_pointwise (by norm_num) (by norm_num) (fibreHalf μ) S Mb hμ hγ hMb hM1
    (fun M _ j => fibreHalf_le hμ M j) hquad hS hS0 hSmono hthr

/-- **T1 Theorem 6.1 at `q = 1/2` (closed-form fibre bound, Proposition 4.2): no weak valley.** -/
theorem noValleyAt_half {m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ} {μ α β γ : ℝ} (hμ : 0 < μ)
    (hγ : 0 < γ) (S : ℕ → ℝ) (Mb : ℕ)
    (hMb : quadBig α β γ m (fibreFallback (1 / 2) 0 μ) ≤ Mb) (hM1 : M1 ≤ Mb)
    (hquad : ∀ M : ℕ, M1 ≤ M → M < Mb →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 ≤ fibreHalf μ M)
    (hS : ∀ M : ℕ, M < M1 →
      α + β * ((M : ℝ) - m) - γ * ((M : ℝ) - m) ^ 2 - fibreHalf μ M ≤ S M)
    (hS0 : ∀ M : ℕ, M < M1 → 0 ≤ S M) (hSmono : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M)
    (hthr : μ * θ * ((1 / 2 : ℝ) * (1 - 1 / 2)) * m <
      α - γ * D * m - ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1))) :
    NoValleyAt (1 / 2) m θ D T M1 :=
  t1Core (1 / 2) m θ D T M1 (by norm_num) (by norm_num)
    (explicitThreshold_half hμ hγ S Mb hMb hM1 hquad hS hS0 hSmono hthr)

end Erdos993Lean.Analytic.NoValley
