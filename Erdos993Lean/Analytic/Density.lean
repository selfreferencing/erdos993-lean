import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.HardCore.Weight
import Erdos993Lean.Ceiling.Join
import Erdos993Lean.Ceiling.Prefix

/-!
# The elementary floor of the expected free count (open object O5, elementary part)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead); sources: Soul's `SOUL/RESULTS/O5.md` §1
(adjudicated CORRECT, `LEAN/referee/REVIEW_SOUL_ROUND1.md`).

For a forest `F` with `n ≥ 61` vertices, an activity `t > 0` at an interior rank (`μ_F(t) = k`,
`⌈n/4⌉ < k < h_B`) and a maximum-weight independent set `B`, the expected free count
`m = E M = W/q` satisfies

    m ≥ max (17 / (2q), 61 / (2 (1 + 2q))),   q = t/(1 + t).

* `17/(2q)`: `k ≥ ⌈61/4⌉ + 1 = 17` and `μ ≤ 2W = 2qm` (`two_mul_actQ_mul_meanM_ge`, lane A1);
* `61/(2(1 + 2q))`: the rising-prefix inequality `(n − 3j) c_j ≤ (j + 1) c_{j+1}` (`prefix_inequality`,
  L394), summed against `t^(j+1)`, gives `n t ≤ μ_F(t) (1 + 3t)` (`mul_le_hardCoreMean_mul`), and
  `n t/((1 + 3t)·2q) = n/(2(1 + 2q))`.

Results: `mul_le_hardCoreMean_mul`, `meanM_ge_mfloorElem`, `densityBound_of_le_mfloorElem`.
-/

namespace Erdos993Lean.Analytic

open Finset

/-- No independent set has more than `n` vertices: `i_{n+1} = 0`. -/
theorem independenceCount_succ_n (F : FiniteForest) : independenceCount F (F.n + 1) = 0 := by
  classical
  unfold independenceCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [SimpleGraph.mem_indepSetFinset_iff] at hs
  have h1 := Finset.card_le_univ s
  rw [hs.card_eq, Fintype.card_fin] at h1
  omega

/-- **The prefix lower bound on the hard-core mean**: `n t ≤ μ_F(t) (1 + 3t)` for every `t ≥ 0`
(sum of L394 against `t^(j+1)`). -/
theorem mul_le_hardCoreMean_mul (F : FiniteForest) {t : ℝ} (ht : 0 ≤ t) :
    (F.n : ℝ) * t ≤ hardCoreMean F t * (1 + 3 * t) := by
  classical
  have hZ := Join.one_le_partitionFn F ht
  have hcount : independenceCount F = fun k => (F.graph.indepSetFinset k).card := by
    funext k
    unfold independenceCount
    rfl
  -- the prefix inequality in `ℝ`
  have hpre : ∀ k : ℕ, ((F.n : ℝ) - 3 * k) * (independenceCount F k : ℝ) ≤
      ((k : ℝ) + 1) * (independenceCount F (k + 1) : ℝ) := by
    intro k
    have h := prefix_inequality F.isForest (Finset.univ : Finset (Fin F.n)) k
    rw [indepCount_univ, indepCount_univ, Finset.card_univ, Fintype.card_fin] at h
    rw [hcount]
    have h' : ((((F.n : ℤ) - 3 * k) * ((F.graph.indepSetFinset k).card : ℤ) : ℤ) : ℝ) ≤
        ((((k : ℤ) + 1) * ((F.graph.indepSetFinset (k + 1)).card : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    simpa using h'
  set S0 := partitionFn F t with hS0
  set S1 := ∑ k ∈ range (F.n + 1), (k : ℝ) * (independenceCount F k : ℝ) * t ^ k with hS1
  have e1 : t * ((F.n : ℝ) * S0 - 3 * S1) =
      ∑ k ∈ range (F.n + 1), ((F.n : ℝ) - 3 * k) * (independenceCount F k : ℝ) * t ^ (k + 1) := by
    rw [hS0, hS1, partitionFn, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : S1 = ∑ k ∈ range (F.n + 1),
      ((k : ℝ) + 1) * (independenceCount F (k + 1) : ℝ) * t ^ (k + 1) := by
    rw [hS1, Finset.sum_range_succ', Finset.sum_range_succ (fun k => ((k : ℝ) + 1) *
      (independenceCount F (k + 1) : ℝ) * t ^ (k + 1)), independenceCount_succ_n]
    push_cast
    simp
  have key : t * ((F.n : ℝ) * S0 - 3 * S1) ≤ S1 := by
    rw [e1, e2]
    refine Finset.sum_le_sum fun k _ => ?_
    exact mul_le_mul_of_nonneg_right (hpre k) (by positivity)
  have hmean : hardCoreMean F t = S1 / S0 := rfl
  rw [hmean, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- The elementary floor `max (17/(2q), 61/(2(1 + 2q)))`, `q = t/(1 + t)`. -/
noncomputable def mfloorElem (t : ℝ) : ℝ :=
  max (17 / (2 * actQ t)) (61 / (2 * (1 + 2 * actQ t)))

/-- **The elementary floor of `m` (O5, elementary part).**  For a forest with at least 61
vertices, an activity `t > 0` at an interior rank and a maximum-weight independent set `B`,
`m = E M ≥ max (17/(2q), 61/(2(1 + 2q)))`. -/
theorem meanM_ge_mfloorElem (F : FiniteForest) (hn : 61 ≤ F.n) {t : ℝ} (ht : 0 < t)
    (hI : AtInteriorRank F t) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    mfloorElem t ≤ (forestMixture F B t).meanM := by
  obtain ⟨k, hk1, _, hμ⟩ := hI
  have hq : 0 < actQ t := by unfold actQ; positivity
  have h2 := two_mul_actQ_mul_meanM_ge F ht hB
  set m := (forestMixture F B t).meanM with hm
  have hk17 : (17 : ℝ) ≤ k := by
    have : 17 ≤ k := by omega
    exact_mod_cast this
  unfold mfloorElem
  refine max_le ?_ ?_
  · -- `17 ≤ k = μ ≤ 2 q m`
    rw [div_le_iff₀ (by positivity)]
    rw [hμ] at h2
    linarith
  · -- `n t ≤ μ (1 + 3t)`, `μ ≤ 2 q m`, and `n ≥ 61`
    have hpre := mul_le_hardCoreMean_mul F ht.le
    have hn' : (61 : ℝ) ≤ F.n := by exact_mod_cast hn
    have hqdef : actQ t * (1 + t) = t := by unfold actQ; field_simp
    have hμ0 : 0 ≤ hardCoreMean F t := by rw [hμ]; positivity
    -- 61 t ≤ μ (1 + 3t) ≤ 2 q m (1 + 3t), and (1 + 3t) = (1 + 2q)(1 + t)
    have h3 : (61 : ℝ) * t ≤ 2 * actQ t * m * (1 + 3 * t) := by
      have h4 : hardCoreMean F t * (1 + 3 * t) ≤ 2 * actQ t * m * (1 + 3 * t) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      nlinarith
    have h13 : 1 + 3 * t = (1 + 2 * actQ t) * (1 + t) := by
      have : 2 * actQ t * (1 + t) = 2 * t := by rw [mul_assoc, hqdef]
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    rw [h13] at h3
    -- 61 t ≤ 2 q m (1 + 2q)(1 + t) = 2 m (1 + 2q) · t
    have h5 : 2 * actQ t * m * ((1 + 2 * actQ t) * (1 + t)) = m * (2 * (1 + 2 * actQ t)) * t := by
      calc 2 * actQ t * m * ((1 + 2 * actQ t) * (1 + t))
          = 2 * m * (1 + 2 * actQ t) * (actQ t * (1 + t)) := by ring
        _ = m * (2 * (1 + 2 * actQ t)) * t := by rw [hqdef]; ring
    rw [h5] at h3
    exact le_of_mul_le_mul_right h3 ht

/-- **O5 from the elementary floor**: every profile whose floor lies below the elementary floor
satisfies `DensityBound`. -/
theorem densityBound_of_le_mfloorElem {P : Profile}
    (h : ∀ t, InRange t → P.mfloor t ≤ mfloorElem t) : DensityBound P := by
  intro F hn t hR hI B hB
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  exact le_trans (h t hR) (meanM_ge_mfloorElem F hn ht hI hB)

end Erdos993Lean.Analytic
