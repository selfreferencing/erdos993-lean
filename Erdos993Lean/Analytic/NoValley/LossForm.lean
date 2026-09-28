import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Identities
import Erdos993Lean.Analytic.NoValley.Core

/-!
# The exact loss form (T1 Theorem 3.1; extra E3)

Source: T1 (`ProofRuns/2026-09-27_zhang_review/reports/T1.md`), §3 (lines 146–171): Theorem 3.1 and
the definitions preceding it.  Notation: `N = M + 2`, `v = q(1 − q)`, `W(i) = b_N(i)/(N(N − 1)v²)`
(`kappaWeight`, zero off `[0, N]`), `Q_κ(i) = Nv + (1 − 2q)e − e² + (1 − 2q)² i(N − i)`, `e = i − qN`
(`kappaQuad`), both from `NoValley/Identities.lean`.

* `a = 1 + (1 − 2q)²` (`lossA`);
* `i_v(M) = (N(1 − 2q + 4q²) + (1 − 2q))/(2a)` (`vertexI`), the vertex of `Q_κ`, so that
  `Q_κ(i) = G_κ − a(i − i_v)²` with `G_κ = Q_κ(i_v)` (`vertexG`, `kappaQuad_eq_vertex`);
* `d(M) = i_v − 1 − qM = (1 − 2q)((1 − 2q)²M − 1)/(2a)` (`driftD`, `driftD_eq`);
* `Q_κ(1 + qM) = (M + 2)v + (1 − 2q)²(1 + M + vM²)` (`kappaQuad_one_add`);
* for multipliers `μ̃` (T1 takes `μ̃ > 0`) and `c`: `c'_M = 2aμ̃ d(M) + c` (`slopeC`),
  `P(M) = μ̃[(M + 2)v + (1 − 2q)²(1 + M + vM²)] + c'_M d(M)` (`chebP`),
  `Φ_M(i) = (μ̃ − W(i)) Q_κ(i) − c'_M (i − i_v)` (`lossPhi`).

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

* **T1 Theorem 3.1** (`loss_form`): for every `M`, every integer `j` and `δ = j − qM`,
  `κ(M, j) + cδ + aμ̃δ² = P(M) − Φ_M(j + 1)` (for `q ≠ 0, 1`; no condition on `μ̃, c`).
* `loss_form_fibre_bound`: if `Φ_M(i) ≤ L(M)` for all integers `i`, then `h(M) = P(M) − L(M)` is a
  pointwise fibre bound with `δ²`-multiplier `ν = aμ̃`, as required by `ExplicitThreshold`.
* `not_weakValley_of_loss_form` (T1 Theorem 3.1, "consequently"): if `Φ_M ≤ L(M)`, `E δ = 0`,
  `E δ² ≤ θ v m` and `aμ̃ θ v m < E[P(M) − L(M)]` (T1: `θ < E[P(M) − L_M]/(aμ̃ v m)`), `μ̃ ≥ 0`, then
  there is no weak valley at `k`.
-/

namespace Erdos993Lean.Analytic.NoValley

open Finset

/-! ## The objects of T1 §3 -/

/-- `a = 1 + (1 − 2q)²`. -/
noncomputable def lossA (q : ℝ) : ℝ := 1 + (1 - 2 * q) ^ 2

theorem lossA_pos (q : ℝ) : 0 < lossA q := by
  unfold lossA
  positivity

/-- The vertex `i_v(M) = (N(1 − 2q + 4q²) + (1 − 2q))/(2a)` of `Q_κ`, `N = M + 2`. -/
noncomputable def vertexI (q : ℝ) (M : ℕ) : ℝ :=
  (((M : ℝ) + 2) * (1 - 2 * q + 4 * q ^ 2) + (1 - 2 * q)) / (2 * lossA q)

/-- The vertex value `G_κ = Q_κ(i_v)`. -/
noncomputable def vertexG (q : ℝ) (M : ℕ) : ℝ := kappaQuad q M (vertexI q M)

/-- The drift `d(M) = i_v(M) − 1 − qM`. -/
noncomputable def driftD (q : ℝ) (M : ℕ) : ℝ := vertexI q M - 1 - q * M

/-- `c'_M = 2aμ̃ d(M) + c`. -/
noncomputable def slopeC (q μ c : ℝ) (M : ℕ) : ℝ := 2 * lossA q * μ * driftD q M + c

/-- The Chebyshev value `P(M) = μ̃[(M + 2)v + (1 − 2q)²(1 + M + vM²)] + c'_M d(M)`, `v = q(1 − q)`. -/
noncomputable def chebP (q μ c : ℝ) (M : ℕ) : ℝ :=
  μ * (((M : ℝ) + 2) * (q * (1 - q)) + (1 - 2 * q) ^ 2 * (1 + M + q * (1 - q) * (M : ℝ) ^ 2)) +
    slopeC q μ c M * driftD q M

/-- The Chebyshev-failure loss `Φ_M(i) = (μ̃ − W(i)) Q_κ(i) − c'_M (i − i_v)`. -/
noncomputable def lossPhi (q μ c : ℝ) (M : ℕ) (i : ℤ) : ℝ :=
  (μ - kappaWeight q M i) * kappaQuad q M i - slopeC q μ c M * ((i : ℝ) - vertexI q M)

/-! ## Elementary facts -/

/-- `d(M) = (1 − 2q)((1 − 2q)²M − 1)/(2a)`. -/
theorem driftD_eq (q : ℝ) (M : ℕ) :
    driftD q M = (1 - 2 * q) * ((1 - 2 * q) ^ 2 * M - 1) / (2 * lossA q) := by
  have ha := (lossA_pos q).ne'
  unfold driftD vertexI
  field_simp
  unfold lossA
  ring

/-- **The vertex form** `Q_κ(i) = G_κ − a(i − i_v)²`. -/
theorem kappaQuad_eq_vertex (q : ℝ) (M : ℕ) (i : ℝ) :
    kappaQuad q M i = vertexG q M - lossA q * (i - vertexI q M) ^ 2 := by
  have ha := (lossA_pos q).ne'
  unfold vertexG kappaQuad vertexI
  field_simp
  unfold lossA
  ring

/-- `Q_κ(1 + qM) = (M + 2)v + (1 − 2q)²(1 + M + vM²)`. -/
theorem kappaQuad_one_add (q : ℝ) (M : ℕ) :
    kappaQuad q M (1 + q * M) =
      ((M : ℝ) + 2) * (q * (1 - q)) + (1 - 2 * q) ^ 2 * (1 + M + q * (1 - q) * (M : ℝ) ^ 2) := by
  unfold kappaQuad
  ring

/-! ## T1 Theorem 3.1 -/

/-- **T1 Theorem 3.1 (the exact loss form).**  For `q ≠ 0, 1`, all multipliers `μ̃, c`, every `M`
and every integer `j`, with `δ = j − qM`: `κ(M, j) + cδ + aμ̃δ² = P(M) − Φ_M(j + 1)`. -/
theorem loss_form {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (μ c : ℝ) (M : ℕ) (j : ℤ) :
    kappa q M j + c * ((j : ℝ) - q * M) + lossA q * μ * ((j : ℝ) - q * M) ^ 2 =
      chebP q μ c M - lossPhi q μ c M (j + 1) := by
  rw [kappa_eq_kappaWeight_mul_kappaQuad hq0 hq1 M j]
  have hv := kappaQuad_eq_vertex q M ((j : ℝ) + 1)
  have hv1 := kappaQuad_eq_vertex q M (1 + q * M)
  rw [kappaQuad_one_add] at hv1
  unfold lossPhi chebP slopeC driftD
  push_cast
  linear_combination μ * hv - μ * hv1

/-- **The loss form as a fibre bound.**  If `Φ_M(i) ≤ L(M)` for every integer `i`, then
`P(M) − L(M) ≤ κ(M, j) + cδ + (aμ̃)δ²` for every integer `j` (`δ = j − qM`): the pointwise condition
of `ExplicitThreshold` with `h = P − L` and `ν = aμ̃`. -/
theorem loss_form_fibre_bound {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (μ c : ℝ) (L : ℕ → ℝ)
    (hL : ∀ (M : ℕ) (i : ℤ), lossPhi q μ c M i ≤ L M) (M : ℕ) (j : ℤ) :
    chebP q μ c M - L M ≤
      kappa q M j + c * ((j : ℝ) - q * M) + lossA q * μ * ((j : ℝ) - q * M) ^ 2 := by
  rw [loss_form hq0 hq1 μ c M j]
  linarith [hL M (j + 1)]

/-- **T1 Theorem 3.1, the consequence for mixtures.**  Let `0 < q < 1`, `μ̃ ≥ 0`, and
`Φ_M(i) ≤ L(M)` for all `M` and all integers `i`.  If a probability mixture has `E δ = 0`,
`E δ² ≤ θ v m` at the rank `k`, and `aμ̃ θ v m < E[P(M) − L(M)]`, then it has no weak valley at `k`. -/
theorem not_weakValley_of_loss_form {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {μ c θ m : ℝ}
    (hμ : 0 ≤ μ) (L : ℕ → ℝ) (hL : ∀ (M : ℕ) (i : ℤ), lossPhi q μ c M i ≤ L M)
    {ι : Type*} (X : Mixture ι) (k : ℤ) (hX : X.IsProb)
    (hδ : X.expect (fun M Y => delta q k M Y) = 0)
    (hδ2 : X.expect (fun M Y => delta q k M Y ^ 2) ≤ θ * (q * (1 - q)) * m)
    (hθ : lossA q * μ * (θ * (q * (1 - q)) * m) <
      X.expect (fun M _ => chebP q μ c M - L M)) :
    ¬ X.WeakValley q k := by
  intro hvalley
  have hw : ∀ σ ∈ X.S, 0 ≤ X.w σ := hX.1
  have hEκ := X.sum_kappa_nonpos hq0 hq1 hvalley
  have hEh : X.expect (fun M _ => chebP q μ c M - L M) ≤
      ∑ σ ∈ X.S, X.w σ * kappa q (X.M σ) (k - X.Y σ) +
        c * X.expect (fun M Y => delta q k M Y) +
          lossA q * μ * X.expect (fun M Y => delta q k M Y ^ 2) := by
    unfold Mixture.expect
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun σ hσ => ?_
    have hp := loss_form_fibre_bound hq0.ne' hq1.ne μ c L hL (X.M σ) (k - X.Y σ)
    have hcast : (((k - (X.Y σ : ℤ) : ℤ) : ℝ) - q * (X.M σ : ℝ)) = delta q k (X.M σ) (X.Y σ) := by
      unfold delta
      push_cast
      ring
    rw [hcast] at hp
    have := mul_le_mul_of_nonneg_left hp (hw σ hσ)
    have e : X.w σ * (kappa q (X.M σ) (k - X.Y σ) + c * delta q k (X.M σ) (X.Y σ) +
        lossA q * μ * delta q k (X.M σ) (X.Y σ) ^ 2) =
        X.w σ * kappa q (X.M σ) (k - X.Y σ) + c * (X.w σ * delta q k (X.M σ) (X.Y σ)) +
          lossA q * μ * (X.w σ * delta q k (X.M σ) (X.Y σ) ^ 2) := by ring
    linarith
  have haμ : 0 ≤ lossA q * μ := mul_nonneg (lossA_pos q).le hμ
  have h2 := mul_le_mul_of_nonneg_left hδ2 haμ
  rw [hδ, mul_zero, add_zero] at hEh
  linarith

end Erdos993Lean.Analytic.NoValley
