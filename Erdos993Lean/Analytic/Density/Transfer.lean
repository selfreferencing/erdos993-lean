import Erdos993Lean.Analytic.Density

/-!
# The activity transfer of the hard-core mean: `μ_F(λ)² / q(λ)` is nondecreasing

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Source: Soul's
`SOUL/RESULTS/O5.md` §4 (adjudicated CORRECT, `LEAN/referee/REVIEW_SOUL_ROUND1.md`, O5(iv)).

For a forest `F` and `t > 0`, `q = t/(1 + t)`:

* `two_mul_hardCoreVar_ge`: `(1 − q) μ ≤ 2 V` (`V = Var K`).  For an independent set `B`, the law
  of total variance over the conditional binomial mixture (`hardCoreVar_eq_expect`) gives
  `V ≥ q(1 − q) m = (1 − q) W(B)`; the two colour classes of the forest are independent and their
  weights add up to `μ`.
* `hasDerivAt_hardCoreMean`: `μ` is differentiable at `t > 0` with `t μ'(t) = V(t)`.
* **`actQ_mul_sq_le`** (the transfer): for `0 < x ≤ t`,
  `q(t) μ_F(x)² ≤ q(x) μ_F(t)²`, i.e. `μ_F(t) ≥ √(q(t)/q(x)) μ_F(x)`; the function
  `μ²/q = μ² (1 + t)/t` has derivative `μ (2V(1 + t) − μ)/t² ≥ 0`.
* **`le_of_transfer`**: the integer form used on the bands.  If `μ_F(x) ≥ L ≥ 0`, `x ≤ a ≤ t`,
  `μ_F(t) = k` is an integer and `(K − 1)² < (q(a)/q(x)) L²` with `K ≥ 1`, then `K ≤ k`.

Scalarity: no new scalar; `V` is the variance of the size `K` of the hard-core set, `μ` its mean.
-/

namespace Erdos993Lean.Analytic.Density

open Finset

variable (F : FiniteForest)

/-! ## `2V ≥ (1 − q) μ` -/

/-- For an independent set `B` and `t > 0`: `(1 − q) W(B) ≤ V` (law of total variance over the
conditional binomial mixture: `V ≥ E Var(K | σ) = q(1 − q) m` and `q m = W`). -/
theorem weightW_mul_le_hardCoreVar {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) :
    (1 - actQ t) * weightW F t B ≤ hardCoreVar F t := by
  rw [HardCore.hardCoreVar_eq_expect F hB ht, ← HardCore.forestMixture_weight_eq F hB ht]
  have h0 : 0 ≤ (forestMixture F B t).expect
      (fun M Y => ((Y : ℝ) + actQ t * M - hardCoreMean F t) ^ 2) :=
    Mixture.expect_nonneg _ (HardCore.forestMixture_isProb F hB ht).1 fun _ _ => sq_nonneg _
  nlinarith

/-- **`2V ≥ (1 − q) μ`** for every forest and every `t > 0` (the two colour classes of the forest
are independent and their weights add up to `μ`). -/
theorem two_mul_hardCoreVar_ge {t : ℝ} (ht : 0 < t) :
    (1 - actQ t) * hardCoreMean F t ≤ 2 * hardCoreVar F t := by
  classical
  have h01 : ∀ v : Fin F.n, ¬ F.isForest.coloringTwo v = 0 → F.isForest.coloringTwo v = 1 := by
    intro v hv
    have key : ∀ a : Fin 2, ¬ a = 0 → a = 1 := by decide
    exact key _ hv
  have hsplit : hardCoreMean F t =
      weightW F t (univ.filter fun v => F.isForest.coloringTwo v = 0) +
        weightW F t (univ.filter fun v => F.isForest.coloringTwo v = 1) := by
    rw [← HardCore.sum_univ_marginal]
    unfold weightW
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => F.isForest.coloringTwo v = 0)]
    congr 2
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h01 v, fun h h0 => absurd (h.symm.trans h0) (by decide)⟩
  have h0 := weightW_mul_le_hardCoreVar F (HardCore.isIndepSet_colourClass F 0) ht
  have h1 := weightW_mul_le_hardCoreVar F (HardCore.isIndepSet_colourClass F 1) ht
  rw [hsplit]
  linarith

/-! ## The derivative of the mean -/

/-- `N(t) = Σ_k k i_k t^k`, the numerator of `μ_F(t)`. -/
noncomputable def meanNum (t : ℝ) : ℝ :=
  ∑ k ∈ range (F.n + 1), (k : ℝ) * (independenceCount F k : ℝ) * t ^ k

/-- `Σ_k k² i_k t^k`. -/
noncomputable def meanNum2 (t : ℝ) : ℝ :=
  ∑ k ∈ range (F.n + 1), (k : ℝ) ^ 2 * (independenceCount F k : ℝ) * t ^ k

theorem hardCoreMean_eq_div : hardCoreMean F = fun t => meanNum F t / partitionFn F t := rfl

/-- The derivative of a polynomial function `Σ_k c_k t^k`, multiplied by `t`. -/
theorem hasDerivAt_sum_pow (c : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (fun s => ∑ k ∈ range N, c k * s ^ k)
      (∑ k ∈ range N, c k * ((k : ℝ) * t ^ (k - 1))) t :=
  HasDerivAt.fun_sum fun k _ => (hasDerivAt_pow k t).const_mul (c k)

theorem mul_sum_deriv_pow (c : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    t * ∑ k ∈ range N, c k * ((k : ℝ) * t ^ (k - 1)) = ∑ k ∈ range N, (k : ℝ) * c k * t ^ k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases k with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel, pow_succ]
    push_cast
    ring

theorem hasDerivAt_partitionFn (t : ℝ) :
    ∃ Z' : ℝ, HasDerivAt (partitionFn F) Z' t ∧ t * Z' = meanNum F t := by
  refine ⟨_, hasDerivAt_sum_pow (fun k => (independenceCount F k : ℝ)) (F.n + 1) t, ?_⟩
  rw [mul_sum_deriv_pow]
  rfl

theorem hasDerivAt_meanNum (t : ℝ) :
    ∃ N' : ℝ, HasDerivAt (meanNum F) N' t ∧ t * N' = meanNum2 F t := by
  refine ⟨_, hasDerivAt_sum_pow (fun k => (k : ℝ) * (independenceCount F k : ℝ)) (F.n + 1) t, ?_⟩
  rw [mul_sum_deriv_pow]
  unfold meanNum2
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `V = Σ k² i_k t^k / Z − μ²`. -/
theorem hardCoreVar_eq_num2 {t : ℝ} (ht : 0 ≤ t) :
    hardCoreVar F t = meanNum2 F t / partitionFn F t - hardCoreMean F t ^ 2 := by
  have hZ := HardCore.partitionFn_pos F ht
  have hμ : hardCoreMean F t * partitionFn F t = meanNum F t := by
    rw [hardCoreMean_eq_div]
    field_simp
  unfold hardCoreVar
  rw [eq_sub_iff_add_eq, div_add' _ _ _ hZ.ne', div_left_inj' hZ.ne']
  have e : ∑ k ∈ range (F.n + 1),
      ((k : ℝ) - hardCoreMean F t) ^ 2 * (independenceCount F k : ℝ) * t ^ k =
      meanNum2 F t - 2 * hardCoreMean F t * meanNum F t +
        hardCoreMean F t ^ 2 * partitionFn F t := by
    unfold meanNum2 meanNum partitionFn
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e, ← hμ]
  ring

/-- **`t μ'(t) = V(t)`**: the mean is differentiable at `t > 0` with derivative `V(t)/t`. -/
theorem hasDerivAt_hardCoreMean {t : ℝ} (ht : 0 < t) :
    HasDerivAt (hardCoreMean F) (hardCoreVar F t / t) t := by
  obtain ⟨Z', hZ', hZt⟩ := hasDerivAt_partitionFn F t
  obtain ⟨N', hN', hNt⟩ := hasDerivAt_meanNum F t
  have hZ := HardCore.partitionFn_pos F ht.le
  have hd := hN'.div hZ' hZ.ne'
  rw [hardCoreMean_eq_div]
  convert hd using 1
  rw [hardCoreVar_eq_num2 F ht.le, hardCoreMean_eq_div]
  simp only
  field_simp
  rw [← hZt, ← hNt]
  ring

/-! ## The transfer -/

theorem hardCoreMean_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hardCoreMean F t := by
  rw [hardCoreMean_eq_div]
  exact div_nonneg (Finset.sum_nonneg fun k _ => by positivity) (HardCore.partitionFn_pos F ht).le

/-- `G(t) = μ_F(t)² (1 + t)/t = μ²/q`. -/
noncomputable def transferFn (t : ℝ) : ℝ := hardCoreMean F t ^ 2 * (1 + t) / t

theorem hasDerivAt_transferFn {t : ℝ} (ht : 0 < t) :
    HasDerivAt (transferFn F)
      (2 * hardCoreMean F t * (hardCoreVar F t / t) * ((1 + t) / t) +
        hardCoreMean F t ^ 2 * (-1 / t ^ 2)) t := by
  have h1 : HasDerivAt (fun s => hardCoreMean F s ^ 2)
      (2 * hardCoreMean F t * (hardCoreVar F t / t)) t := by
    convert (hasDerivAt_hardCoreMean F ht).pow 2 using 1
    ring
  have h2 : HasDerivAt (fun s : ℝ => (1 + s) / s) (-1 / t ^ 2) t := by
    have h3 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
    convert h3.div (hasDerivAt_id t) ht.ne' using 1
    simp only [id]
    ring
  have h4 := h1.mul h2
  unfold transferFn
  convert h4 using 1
  funext s
  rw [Pi.mul_apply]
  ring

theorem transferFn_deriv_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ 2 * hardCoreMean F t * (hardCoreVar F t / t) * ((1 + t) / t) +
        hardCoreMean F t ^ 2 * (-1 / t ^ 2) := by
  have hV := two_mul_hardCoreVar_ge F ht
  have hμ := hardCoreMean_nonneg F ht.le
  have hq : 1 - actQ t = 1 / (1 + t) := by
    unfold actQ
    field_simp
    ring
  rw [hq] at hV
  have hV' : hardCoreMean F t ≤ 2 * hardCoreVar F t * (1 + t) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at hV
    linarith
  have e : 2 * hardCoreMean F t * (hardCoreVar F t / t) * ((1 + t) / t) +
      hardCoreMean F t ^ 2 * (-1 / t ^ 2) =
      hardCoreMean F t * (2 * hardCoreVar F t * (1 + t) - hardCoreMean F t) / t ^ 2 := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (mul_nonneg hμ (by linarith)) (by positivity)

/-- `μ²/q` is nondecreasing on `t > 0`. -/
theorem transferFn_monotoneOn : MonotoneOn (transferFn F) (Set.Ioi 0) := by
  have hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt (transferFn F) _ t :=
    fun t ht => hasDerivAt_transferFn F ht
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro t ht
    rw [(hd t ht).deriv]
    exact transferFn_deriv_nonneg F ht

/-- **The activity transfer (O5 §4).**  For `0 < x ≤ t`: `q(t) μ_F(x)² ≤ q(x) μ_F(t)²`, i.e.
`μ_F(t) ≥ √(q(t)/q(x)) μ_F(x)`. -/
theorem actQ_mul_sq_le {x t : ℝ} (hx : 0 < x) (hxt : x ≤ t) :
    actQ t * hardCoreMean F x ^ 2 ≤ actQ x * hardCoreMean F t ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le hx hxt
  have hmono := transferFn_monotoneOn F (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr ht) hxt
  unfold transferFn at hmono
  unfold actQ
  rw [div_le_div_iff₀ hx ht] at hmono
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The integer form of the transfer.**  If `μ_F(x) ≥ L ≥ 0`, `0 < x ≤ a ≤ t`, `μ_F(t) = k` and
`(K − 1)² < (q(a)/q(x)) L²` with `K ≥ 1`, then `K ≤ k`. -/
theorem le_of_transfer {x a t : ℝ} (hx : 0 < x) (hxa : x ≤ a) (hat : a ≤ t) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ hardCoreMean F x) {k : ℕ} (hk : hardCoreMean F t = k) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : ((K : ℝ) - 1) ^ 2 < actQ a / actQ x * L ^ 2) : K ≤ k := by
  have hqx : 0 < actQ x := HardCore.actQ_pos hx
  have hqa : actQ a ≤ actQ t := by
    unfold actQ
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have htr := actQ_mul_sq_le F hx (hxa.trans hat)
  rw [hk] at htr
  have hL2 : L ^ 2 ≤ hardCoreMean F x ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have hqa0 : 0 ≤ actQ a := HardCore.actQ_nonneg (by linarith)
  have h1 : actQ a / actQ x * L ^ 2 ≤ (k : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hqx]
    nlinarith
  have h2 : ((K : ℝ) - 1) ^ 2 < (k : ℝ) ^ 2 := lt_of_lt_of_le hK h1
  have hK1' : (0 : ℝ) ≤ (K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith
  have h3 : (K : ℝ) - 1 < k := by
    by_contra hcon
    push_neg at hcon
    have := pow_le_pow_left₀ (Nat.cast_nonneg k) hcon 2
    linarith
  have h4 : (K : ℝ) < k + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h4)

end Erdos993Lean.Analytic.Density
