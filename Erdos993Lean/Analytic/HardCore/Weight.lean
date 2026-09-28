import Mathlib
import Erdos993Lean.Analytic.HardCore.Mixture

/-!
# Maximum-weight independent sets: `W ≥ μ/2`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A1, extra E1.  Source: T. Zhang, *Exact
Certificates for Unimodality of Forest Independence Polynomials*, v1.1, Section 3 (before (45)):
"Bipartiteness gives `W ≥ µ/2`".

* `isIndepSet_colourClass`: the colour classes of Mathlib's 2-colouring of a forest are independent;
* **`two_mul_weightW_ge`**: for a maximum-weight independent set `B` (at any activity),
  `μ_F(t) ≤ 2 W(B)`.  A forest is properly 2-coloured (Mathlib's
  `SimpleGraph.IsAcyclic.coloringTwo`); both colour classes are independent, their weights add up to
  `Σ_v π_v = μ`, and each is at most `W(B)`;
* `two_mul_actQ_mul_meanM_ge`: with `qm = W` (`forestMixture_weight_eq`), `μ_F(t) ≤ 2 q m` for a
  maximum-weight `B` at `t > 0`, i.e. `m ≥ μ/(2q)` (a lower bound on the expected free count, the
  object of the density input O5).

Namespaces: `two_mul_weightW_ge` and `two_mul_actQ_mul_meanM_ge` are in `Erdos993Lean.Analytic`;
`isIndepSet_colourClass` is in `Erdos993Lean.Analytic.HardCore`.

Grade: PROVED IN LEAN (standard axioms only).
-/

namespace Erdos993Lean.Analytic

open Finset

namespace HardCore

variable (F : FiniteForest)

/-- The two colour classes of the forest's 2-colouring are independent. -/
theorem isIndepSet_colourClass (i : Fin 2) :
    F.graph.IsIndepSet
      ((univ.filter fun v => F.isForest.coloringTwo v = i : Finset (Fin F.n)) : Set (Fin F.n)) := by
  rw [isIndepSet_coe_iff]
  intro v hv w hw hvw
  rw [Finset.mem_filter] at hv hw
  exact F.isForest.coloringTwo.valid hvw (hv.2.trans hw.2.symm)

end HardCore

open HardCore

variable (F : FiniteForest)

/-- **E1 (Zhang §3: "bipartiteness gives `W ≥ µ/2`").**  For a maximum-weight independent set `B`
at activity `t`, `μ_F(t) ≤ 2 W(B)`. -/
theorem two_mul_weightW_ge {t : ℝ} {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    hardCoreMean F t ≤ 2 * weightW F t B := by
  classical
  have h01 : ∀ v : Fin F.n, ¬ F.isForest.coloringTwo v = 0 → F.isForest.coloringTwo v = 1 := by
    intro v hv
    have key : ∀ a : Fin 2, ¬ a = 0 → a = 1 := by decide
    exact key _ hv
  have hsplit : hardCoreMean F t =
      weightW F t (univ.filter fun v => F.isForest.coloringTwo v = 0) +
        weightW F t (univ.filter fun v => F.isForest.coloringTwo v = 1) := by
    rw [← sum_univ_marginal]
    unfold weightW
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => F.isForest.coloringTwo v = 0)]
    congr 2
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h01 v, fun h h0 => absurd (h.symm.trans h0) (by decide)⟩
  rw [hsplit]
  have h0 := hB.2 _ (isIndepSet_colourClass F 0)
  have h1 := hB.2 _ (isIndepSet_colourClass F 1)
  linarith

/-- **`m ≥ μ/(2q)`.**  For a maximum-weight independent set `B` at `t > 0`,
`μ_F(t) ≤ 2 q m` with `m = E M` the expected free count (E1 and `qm = W`). -/
theorem two_mul_actQ_mul_meanM_ge {t : ℝ} (ht : 0 < t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) :
    hardCoreMean F t ≤ 2 * actQ t * (forestMixture F B t).meanM := by
  have h1 := two_mul_weightW_ge F hB
  rw [← forestMixture_weight_eq F hB.1 ht] at h1
  linarith

end Erdos993Lean.Analytic
