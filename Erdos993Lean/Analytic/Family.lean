import Erdos993Lean.Analytic.Assembly
import Erdos993Lean.Analytic.Profile30

/-!
# The analytic route on a family of forests; Soul's core-union family

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  The route's inputs O3–O5 are universal
(every forest), while O1 and O2 are proved by Soul only on a family (`SOUL/SUMMARY.md`,
`SOUL/RESULTS/CORE_UNION_UNIMODALITY.md`).  This file restricts O1 and O2 to a family `Φ` and proves
that the route then gives unimodality for every forest of `Φ`:

* `VarianceBoundOn Φ P`, `VarianceRatioBoundOn Φ P`: O1 and O2 for the forests of `Φ` only;
* `AnalyticInputsOn Φ P`: O1, O2 on `Φ` with the universal O3 (`TailBound`), O4 (`ThresholdNoValley`),
  O5 (`DensityBound`);
* `unimodal_of_analyticInputsOn`: every forest of `Φ` has a unimodal independence sequence (forests
  with at most 60 vertices by the kernel-checked finite part, the others by the no-valley argument).

Soul's family (`CoreUnion`): in each component, the internal vertices (degree `≥ 2`) with no leaf
neighbour (`IsExceptional`) form an independent set or exactly one adjacent pair.  Equivalently: for
every edge `xy` between exceptional vertices, every exceptional vertex reachable from `x` is `x` or `y`.
`coreUnion_unimodal_of_inputs` states Soul's family theorem as a Lean implication whose hypotheses are
exactly the family O1/O2 bounds for the certified profile and the universal O3–O5 for that profile.
-/

namespace Erdos993Lean.Analytic

open Finset

section OnFamily

variable (Φ : FiniteForest → Prop) (P : Profile)

/-- **O1 on a family.** -/
def VarianceBoundOn : Prop :=
  ∀ F : FiniteForest, Φ F → 61 ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    (forestMixture F B t).varM ≤ P.Db t * (forestMixture F B t).meanM

/-- **O2 on a family.** -/
def VarianceRatioBoundOn : Prop :=
  ∀ F : FiniteForest, Φ F → 61 ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    hardCoreVar F t ≤ (1 + P.θb t) * (1 - actQ t) * weightW F t B

/-- **The analytic inputs on a family**: O1 and O2 for the forests of `Φ`; O3–O5 universal. -/
structure AnalyticInputsOn : Prop where
  o1 : VarianceBoundOn Φ P
  o2 : VarianceRatioBoundOn Φ P
  o3 : TailBound P
  o4 : ThresholdNoValley P
  o5 : DensityBound P

variable {Φ P}

/-- The universal inputs restrict to every family. -/
theorem AnalyticInputs.on (h : AnalyticInputs P) : AnalyticInputsOn Φ P :=
  ⟨fun F _ => h.o1 F, fun F _ => h.o2 F, h.o3, h.o4, h.o5⟩

/-- No weak valley at the interior ranks of a forest of the family. -/
theorem noWeakValley_of_analyticInputsOn (h : AnalyticInputsOn Φ P) (F : FiniteForest) (hF : Φ F)
    (hn : 61 ≤ F.n) (k : ℕ) (hk1 : (F.n + 3) / 4 < k) (hk2 : k < hB F) :
    ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
        independenceCount F k ≤ independenceCount F (k + 1)) := by
  have hmix := mixtureFacts
  obtain ⟨t, hR, ht, hI, hμ⟩ := exists_activity_inRange F k hk1 hk2
  obtain ⟨B, hBmax⟩ := hmix.exists_maxWeight F t ht
  have hBind : F.graph.IsIndepSet (B : Set (Fin F.n)) := hBmax.1
  have hNV := h.o4 t hR (forestMixture F B t).meanM (h.o5 F hn t hR hI B hBmax)
  have hδ2 : (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
      P.θb t * (actQ t * (1 - actQ t)) * (forestMixture F B t).meanM := by
    rw [hmix.var_delta F t B ht hBind k hμ]
    have hO2 := h.o2 F hF hn t hR hI B hBmax
    rw [← hmix.weight_eq F t B ht hBind] at hO2
    linarith
  have hnv : ¬ (forestMixture F B t).WeakValley (actQ t) k :=
    hNV (Finset (Fin F.n)) (forestMixture F B t) k (hmix.isProb F t B ht hBind) rfl
      (hmix.mean_delta F t B ht hBind k hμ) hδ2 (h.o1 F hF hn t hR hI B hBmax)
      (h.o3 F hn t hR hI B hBmax)
  exact not_valley_of_not_weakValley F (forestMixture F B t) ht (by omega)
    (hmix.prob_eq F t B ht hBind (k - 1)) (hmix.prob_eq F t B ht hBind k)
    (hmix.prob_eq F t B ht hBind (k + 1)) hnv

/-- **Unimodality on a family, from the analytic inputs on that family** (standard axioms; the
finite part is `Zhang.forest_unimodal_of_card_le_sixty_kernel`). -/
theorem unimodal_of_analyticInputsOn (h : AnalyticInputsOn Φ P) (F : FiniteForest) (hF : Φ F) :
    independenceSequenceUnimodal F := by
  rcases le_or_gt F.n 60 with hn | hn
  · exact Zhang.forest_unimodal_of_card_le_sixty_kernel F hn
  · unfold independenceSequenceUnimodal
    exact unimodalUpTo_of_unimodal (unimodal_of_noWeakValley_window F
      (fun k hk1 hk2 => noWeakValley_of_analyticInputsOn h F hF (by omega) k hk1 hk2))

end OnFamily

/-! ## Soul's core-union family -/

/-- A vertex is **exceptional** (Soul's `E`): it is internal (degree at least 2) and has no leaf
neighbour (no neighbour of degree 1). -/
def IsExceptional (F : FiniteForest) (v : Fin F.n) : Prop := by
  classical
  exact 2 ≤ F.graph.degree v ∧ ∀ w, F.graph.Adj v w → F.graph.degree w ≠ 1

/-- **Soul's core-union family** (`SOUL/RESULTS/CORE_UNION_UNIMODALITY.md`): in each component the
exceptional vertices form an independent set or exactly one adjacent pair; equivalently, for every edge
`xy` between exceptional vertices, every exceptional vertex in the component of `x` is `x` or `y`. -/
def CoreUnion (F : FiniteForest) : Prop :=
  ∀ x y : Fin F.n, IsExceptional F x → IsExceptional F y → F.graph.Adj x y →
    ∀ z : Fin F.n, IsExceptional F z → F.graph.Reachable x z → z = x ∨ z = y

/-- **Soul's family theorem as a Lean implication.**  Every forest of the core-union family has a
unimodal independence sequence, given the family O1/O2 bounds for the certified profile (Soul's
mixed-core and adjacent-pair constructors) and the universal O3–O5 for that profile (lanes A10, A9 with
F1/F2, A8). -/
theorem coreUnion_unimodal_of_inputs
    (h1 : VarianceBoundOn CoreUnion Profile30.P) (h2 : VarianceRatioBoundOn CoreUnion Profile30.P)
    (h3 : TailBound Profile30.P) (h4 : ThresholdNoValley Profile30.P) (h5 : DensityBound Profile30.P)
    (F : FiniteForest) (hF : CoreUnion F) : independenceSequenceUnimodal F :=
  unimodal_of_analyticInputsOn ⟨h1, h2, h3, h4, h5⟩ F hF

end Erdos993Lean.Analytic
