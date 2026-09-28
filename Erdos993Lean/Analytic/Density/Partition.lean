import Erdos993Lean.Ceiling.Occupation.Main

/-!
# Hard-core sums at a rational activity inside a fixed forest, and the surplus `Φ`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5, the density records).
Source: Soul's `SOUL/RESULTS/O5.md` §2–§3.  This file generalizes
`Ceiling/Occupation/Partition.lean` (activity `7/3`) to an arbitrary rational activity `x`.

For a vertex set `s` of a graph `G`, `Z(s) = Σ_{t ⊆ s indep} x^|t|` (`Zx`) and
`S(s) = Σ_t |t| x^|t|` (`Sx`); the hard-core mean of `G[s]` is `μ(s) = S(s)/Z(s)`.  The surplus
`Φ_c(s) = S(s) − (r|s| + c) Z(s)` (`Phi`) is `≥ 0` exactly when `μ(s) ≥ r|s| + c`.

* recurrences: `Zx_erase`, `Sx_erase`; products over edge-free unions `Zx_union`, `Sx_union`,
  `Zx_biUnion`; positivity and monotonicity `Zx_pos`, `Zx_mono`, `Zx_le_erase`;
* surplus calculus: `Phi_shift`, `Phi_anti`,
  `Phi_union` (`Φ_{a+b}(A ∪ B) = Φ_a(A) Z(B) + Z(A) Φ_b(B)`),
  `Phi_biUnion_nonneg`, and the vertex identity
  `Phi_erase`: `Φ_c(s) = Φ_{c+r}(s − v) + x Φ_{c+r+r·deg(v)−1}(s − N[v])`;
* the rooted decomposition `RootedAt G s v W C` (`s − v` is the edge-free union of the branches
  `C w`, `w ∈ W`, and `v` sees exactly the bases `w`), with `rootedAt_of_connectedIn` (every tree),
  `RootedAt.restrict` (dropping branches), `RootedAt.connectedIn`;
* graph helpers: `connectedIn_erase_of_card_le_one`, `exists_leaf`, `exists_split`;
* the bridge to `FiniteForest`: `hardCoreMean_eq_Sx_div_Zx`.
-/

namespace Erdos993Lean.Analytic.Density

open Finset Polynomial Erdos993Lean.Occupation

section Sums

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℚ)

/-- `Z(s) = Σ_{t ⊆ s independent} x^|t|`. -/
noncomputable def Zx (s : Finset V) : ℚ := Polynomial.aeval x (indepPoly G s)

/-- `S(s) = Σ_{t ⊆ s independent} |t| x^|t|`. -/
noncomputable def Sx (s : Finset V) : ℚ := Polynomial.aeval x (X * derivative (indepPoly G s))

/-- The surplus `Φ_c(s) = S(s) − (r|s| + c) Z(s)`. -/
noncomputable def Phi (r c : ℚ) (s : Finset V) : ℚ := Sx G x s - (r * s.card + c) * Zx G x s

omit [DecidableEq V] in
theorem Zx_eq_sum (s : Finset V) :
    Zx G x s = ∑ t ∈ s.powerset.filter (IsIndepFinset G), x ^ t.card := by
  simp [Zx, indepPoly, map_sum]

omit [DecidableEq V] in
theorem Sx_eq_sum (s : Finset V) :
    Sx G x s = ∑ t ∈ s.powerset.filter (IsIndepFinset G), (t.card : ℚ) * x ^ t.card := by
  simp only [Sx, indepPoly, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [derivative_X_pow]
  rcases Nat.eq_zero_or_pos t.card with h | h
  · simp [h]
  · have : (X : ℤ[X]) * (C (t.card : ℤ) * X ^ (t.card - 1)) = C (t.card : ℤ) * X ^ t.card := by
      rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel h]
    rw [this]
    simp

/-- `Z(s) = Z(s − v) + x Z(s − N[v])`. -/
theorem Zx_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    Zx G x s = Zx G x (s.erase v) + x * Zx G x (outsideClosedNbhd G s v) := by
  simp only [Zx]
  rw [indepPoly_erase_add G hv]
  simp [map_add, map_mul]

/-- `S(s) = S(s − v) + x (Z + S)(s − N[v])`. -/
theorem Sx_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    Sx G x s = Sx G x (s.erase v) +
      x * (Zx G x (outsideClosedNbhd G s v) + Sx G x (outsideClosedNbhd G s v)) := by
  simp only [Sx, Zx]
  rw [indepPoly_erase_add G hv]
  simp only [derivative_mul, derivative_X, one_mul, map_add, map_mul, aeval_X]
  ring

theorem Zx_union {s t : Finset V} (hst : Disjoint s t) (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    Zx G x (s ∪ t) = Zx G x s * Zx G x t := by
  simp only [Zx]
  rw [indepPoly_union G hst hno, map_mul]

theorem Sx_union {s t : Finset V} (hst : Disjoint s t) (hno : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    Sx G x (s ∪ t) = Sx G x s * Zx G x t + Zx G x s * Sx G x t := by
  simp only [Sx, Zx]
  rw [indepPoly_union G hst hno, derivative_mul]
  simp only [map_mul, map_add, aeval_X]
  ring

omit [DecidableEq V] in
theorem Zx_empty : Zx G x (∅ : Finset V) = 1 := by
  simp [Zx, indepPoly_empty]

omit [DecidableEq V] in
theorem Sx_empty : Sx G x (∅ : Finset V) = 0 := by
  simp [Sx, indepPoly_empty]

theorem Zx_singleton (v : V) : Zx G x {v} = 1 + x := by
  simp [Zx, indepPoly_singleton]

theorem Sx_singleton (v : V) : Sx G x {v} = x := by
  simp [Sx, indepPoly_singleton]

variable {x}

omit [DecidableEq V] in
theorem Zx_pos (hx : 0 ≤ x) (s : Finset V) : 0 < Zx G x s := by
  rw [Zx_eq_sum]
  have h0 : (∅ : Finset V) ∈ s.powerset.filter (IsIndepFinset G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
    exact fun v hv => absurd hv (Finset.notMem_empty v)
  calc (0 : ℚ) < x ^ (∅ : Finset V).card := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun t : Finset V => x ^ t.card)
        (fun t _ => pow_nonneg hx _) h0

omit [DecidableEq V] in
theorem Zx_mono (hx : 0 ≤ x) {s s' : Finset V} (h : s ⊆ s') : Zx G x s ≤ Zx G x s' := by
  rw [Zx_eq_sum, Zx_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.powerset_mono.mpr h)
  · intro t _ _
    exact pow_nonneg hx _

theorem outsideClosedNbhd_subset_erase (s : Finset V) (v : V) :
    outsideClosedNbhd G s v ⊆ s.erase v := by
  rw [outsideClosedNbhd_eq]
  exact Finset.sdiff_subset

/-- Removing one vertex decreases `Z` by a factor of at most `1 + x`. -/
theorem Zx_le_erase (hx : 0 ≤ x) {s : Finset V} {v : V} (hv : v ∈ s) :
    Zx G x s ≤ (1 + x) * Zx G x (s.erase v) := by
  rw [Zx_erase G x hv]
  have := Zx_mono G hx (outsideClosedNbhd_subset_erase G s v)
  nlinarith

variable (x)

omit [DecidableEq V] in
/-- `Z(s) = Σ_k i_k(s) x^k`. -/
theorem Zx_eq_sum_count (s : Finset V) :
    Zx G x s = ∑ k ∈ range (s.card + 1), (indepCount G s k : ℚ) * x ^ k := by
  rw [Zx_eq_sum]
  have hmaps : ∀ t ∈ s.powerset.filter (IsIndepFinset G), t.card ∈ range (s.card + 1) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card ht.1))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul]
  rfl

omit [DecidableEq V] in
/-- `S(s) = Σ_k k i_k(s) x^k`. -/
theorem Sx_eq_sum_count (s : Finset V) :
    Sx G x s = ∑ k ∈ range (s.card + 1), (k : ℚ) * (indepCount G s k : ℚ) * x ^ k := by
  rw [Sx_eq_sum]
  have hmaps : ∀ t ∈ s.powerset.filter (IsIndepFinset G), t.card ∈ range (s.card + 1) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card ht.1))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul]
  unfold indepCount
  ring

/-! ### The surplus -/

variable (r : ℚ)

omit [DecidableEq V] in
theorem Phi_shift (c c' : ℚ) (s : Finset V) :
    Phi G x r c s = Phi G x r c' s + (c' - c) * Zx G x s := by
  unfold Phi
  ring

omit [DecidableEq V] in
theorem Phi_anti (hx : 0 ≤ x) {c c' : ℚ} (h : c ≤ c') (s : Finset V) :
    Phi G x r c' s ≤ Phi G x r c s := by
  rw [Phi_shift G x r c c' s]
  have := Zx_pos G hx s
  nlinarith

/-- `Φ_{a+b}(A ∪ B) = Φ_a(A) Z(B) + Z(A) Φ_b(B)` over an edge-free disjoint union. -/
theorem Phi_union {A B : Finset V} (hAB : Disjoint A B) (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (a b : ℚ) :
    Phi G x r (a + b) (A ∪ B) = Phi G x r a A * Zx G x B + Zx G x A * Phi G x r b B := by
  unfold Phi
  rw [Sx_union G x hAB hno, Zx_union G x hAB hno, Finset.card_union_of_disjoint hAB]
  push_cast
  ring

/-- **The vertex identity.**  For `v ∈ s` of degree `d` in `s`:
`Φ_c(s) = Φ_{c+r}(s − v) + x Φ_{c+r+r d−1}(s − N[v])`. -/
theorem Phi_erase {s : Finset V} {v : V} (hv : v ∈ s) (c : ℚ) :
    Phi G x r c s = Phi G x r (c + r) (s.erase v) +
      x * Phi G x r (c + r + r * (nbrsIn G s v).card - 1) (outsideClosedNbhd G s v) := by
  have hsub : nbrsIn G s v ⊆ s.erase v := nbrsIn_subset_erase G s v
  have hcard1 : (s.erase v).card + 1 = s.card := Finset.card_erase_add_one hv
  have hcard2 : (outsideClosedNbhd G s v).card + (nbrsIn G s v).card = (s.erase v).card := by
    rw [outsideClosedNbhd_eq, Finset.card_sdiff_of_subset hsub]
    have := Finset.card_le_card hsub
    omega
  have e1 : (s.card : ℚ) = (s.erase v).card + 1 := by exact_mod_cast hcard1.symm
  have e2 : ((outsideClosedNbhd G s v).card : ℚ) = (s.erase v).card - (nbrsIn G s v).card := by
    have : ((outsideClosedNbhd G s v).card : ℚ) + (nbrsIn G s v).card = (s.erase v).card := by
      exact_mod_cast hcard2
    linarith
  unfold Phi
  rw [Sx_erase G x hv, Zx_erase G x hv, e1, e2]
  ring

/-! ### Finite edge-free unions -/

theorem Zx_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (D : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (D i) (D j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, ¬ G.Adj a b) :
    Zx G x (I.biUnion D) = ∏ i ∈ I, Zx G x (D i) := by
  simp only [Zx]
  rw [indepPoly_biUnion I D hdisj hno, map_prod]

/-- **`Φ` over a finite edge-free union** (the Leibniz rule):
`Φ_{Σ c_i}(⋃ D_i) = Σ_i Φ_{c_i}(D_i) Π_{j ≠ i} Z(D_j)`. -/
theorem Phi_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (D : ι → Finset V) (c : ι → ℚ)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (D i) (D j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, ¬ G.Adj a b) :
    Phi G x r (∑ i ∈ I, c i) (I.biUnion D) =
      ∑ i ∈ I, Phi G x r (c i) (D i) * ∏ j ∈ I.erase i, Zx G x (D j) := by
  induction I using Finset.induction_on with
  | empty => simp [Phi, Sx_empty, Zx_empty]
  | insert i I hiI ih =>
    have hdisj' : ∀ k ∈ I, ∀ j ∈ I, k ≠ j → Disjoint (D k) (D j) := fun k hk j hj hkj =>
      hdisj k (Finset.mem_insert_of_mem hk) j (Finset.mem_insert_of_mem hj) hkj
    have hno' : ∀ k ∈ I, ∀ j ∈ I, k ≠ j → ∀ a ∈ D k, ∀ b ∈ D j, ¬ G.Adj a b := fun k hk j hj hkj =>
      hno k (Finset.mem_insert_of_mem hk) j (Finset.mem_insert_of_mem hj) hkj
    have hD1 : Disjoint (D i) (I.biUnion D) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun h => hiI (h ▸ hj))
    have hD2 : ∀ a ∈ D i, ∀ b ∈ I.biUnion D, ¬ G.Adj a b := by
      intro a ha b hb
      rw [Finset.mem_biUnion] at hb
      obtain ⟨j, hj, hbj⟩ := hb
      exact hno i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun h => hiI (h ▸ hj)) a ha b hbj
    rw [Finset.biUnion_insert, Finset.sum_insert hiI, Phi_union G x r hD1 hD2, ih hdisj' hno',
      Zx_biUnion G x I D hdisj' hno', Finset.sum_insert hiI, Finset.erase_insert hiI,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := fun h => hiI (h ▸ hj)
    rw [Finset.erase_insert_of_ne hji.symm, Finset.prod_insert (fun h => hiI
      (Finset.mem_of_mem_erase h))]
    ring

theorem Phi_biUnion_nonneg (hx : 0 ≤ x) {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (D : ι → Finset V) (c : ι → ℚ)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (D i) (D j))
    (hno : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, ¬ G.Adj a b)
    (h : ∀ i ∈ I, 0 ≤ Phi G x r (c i) (D i)) :
    0 ≤ Phi G x r (∑ i ∈ I, c i) (I.biUnion D) := by
  rw [Phi_biUnion G x r I D c hdisj hno]
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (h i hi) (Finset.prod_nonneg fun j _ => (Zx_pos G hx _).le)

end Sums

/-! ## Rooted decompositions -/

section Rooted

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `s` is rooted at `v` with branches `C w` (`w ∈ W`): `s − v` is the edge-free disjoint union of
the `C w`, the base `w` lies in `C w`, and inside `C w` the root `v` is adjacent exactly to `w`. -/
structure RootedAt (G : SimpleGraph V) (s : Finset V) (v : V) (W : Finset V) (C : V → Finset V) :
    Prop where
  mem : v ∈ s
  erase_eq : s.erase v = W.biUnion C
  disj : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → Disjoint (C w) (C w')
  noadj : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → ∀ a ∈ C w, ∀ b ∈ C w', ¬ G.Adj a b
  base : ∀ w ∈ W, w ∈ C w
  adj_iff : ∀ w ∈ W, ∀ y ∈ C w, G.Adj v y ↔ y = w

namespace RootedAt

variable {s : Finset V} {v : V} {W : Finset V} {C : V → Finset V}

omit [DecidableRel G.Adj] in
theorem subset (h : RootedAt G s v W C) {w : V} (hw : w ∈ W) : C w ⊆ s.erase v := by
  rw [h.erase_eq]
  exact Finset.subset_biUnion_of_mem C hw

omit [DecidableRel G.Adj] in
theorem notMem_root (h : RootedAt G s v W C) {w : V} (hw : w ∈ W) : v ∉ C w := fun hv =>
  (Finset.mem_erase.mp (h.subset hw hv)).1 rfl

/-- The neighbours of the root are exactly the bases. -/
theorem nbrsIn_eq (h : RootedAt G s v W C) : nbrsIn G s v = W := by
  ext y
  rw [mem_nbrsIn]
  constructor
  · rintro ⟨hys, hvy⟩
    have hy : y ∈ s.erase v := Finset.mem_erase.mpr ⟨(G.ne_of_adj hvy).symm, hys⟩
    rw [h.erase_eq, Finset.mem_biUnion] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    rw [(h.adj_iff w hw y hyw).mp hvy]
    exact hw
  · intro hy
    have h1 := h.subset hy (h.base y hy)
    exact ⟨Finset.mem_of_mem_erase h1, (h.adj_iff y hy y (h.base y hy)).mpr rfl⟩

/-- `s − N[v]` is the union of the branches with their bases removed. -/
theorem outside_eq (h : RootedAt G s v W C) :
    outsideClosedNbhd G s v = W.biUnion fun w => (C w).erase w := by
  ext y
  simp only [outsideClosedNbhd, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨hys, hyv, hvy⟩
    have hy : y ∈ s.erase v := Finset.mem_erase.mpr ⟨hyv, hys⟩
    rw [h.erase_eq, Finset.mem_biUnion] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    exact ⟨w, hw, fun hyw' => hvy ((h.adj_iff w hw y hyw).mpr hyw'), hyw⟩
  · rintro ⟨w, hw, hyw, hy⟩
    have h1 := h.subset hw hy
    exact ⟨Finset.mem_of_mem_erase h1, Finset.ne_of_mem_erase h1,
      fun hvy => hyw ((h.adj_iff w hw y hy).mp hvy)⟩

omit [DecidableRel G.Adj] in
theorem disj' (h : RootedAt G s v W C) :
    ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → Disjoint ((C w).erase w) ((C w').erase w') :=
  fun w hw w' hw' hne => (h.disj w hw w' hw' hne).mono (Finset.erase_subset _ _)
    (Finset.erase_subset _ _)

omit [DecidableRel G.Adj] in
theorem noadj' (h : RootedAt G s v W C) :
    ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → ∀ a ∈ (C w).erase w, ∀ b ∈ (C w').erase w', ¬ G.Adj a b :=
  fun w hw w' hw' hne a ha b hb =>
    h.noadj w hw w' hw' hne a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)

omit [DecidableRel G.Adj] in
theorem card_eq (h : RootedAt G s v W C) : s.card = 1 + ∑ w ∈ W, (C w).card := by
  have h1 := Finset.card_erase_add_one h.mem
  rw [h.erase_eq, Finset.card_biUnion (fun w hw w' hw' hne => h.disj w hw w' hw' hne)] at h1
  omega

variable (x r : ℚ)

/-- `Z(s) = Π Z(C_w) + x Π Z(C_w − w)`. -/
theorem Zx_eq (h : RootedAt G s v W C) :
    Zx G x s = ∏ w ∈ W, Zx G x (C w) + x * ∏ w ∈ W, Zx G x ((C w).erase w) := by
  rw [Zx_erase G x h.mem, h.erase_eq, h.outside_eq, Zx_biUnion G x W C h.disj h.noadj,
    Zx_biUnion G x W _ h.disj' h.noadj']

/-- **The root identity.**  For constants `A w`, `B w`:
`Φ_c(s) = Σ_w Φ_{A w}(C_w) Π_{w' ≠ w} Z(C_{w'}) + x Σ_w Φ_{B w}(C_w − w) Π_{w' ≠ w} Z(C_{w'} − w')
  + (Σ A − r − c) Π Z(C_w) + x (1 − r − r|W| + Σ B − c) Π Z(C_w − w)`. -/
theorem Phi_eq (h : RootedAt G s v W C) (A B : V → ℚ) (c : ℚ) :
    Phi G x r c s =
      (∑ w ∈ W, Phi G x r (A w) (C w) * ∏ w' ∈ W.erase w, Zx G x (C w')) +
      x * (∑ w ∈ W, Phi G x r (B w) ((C w).erase w) *
        ∏ w' ∈ W.erase w, Zx G x ((C w').erase w')) +
      (∑ w ∈ W, A w - r - c) * ∏ w ∈ W, Zx G x (C w) +
      x * (1 - r - r * W.card + ∑ w ∈ W, B w - c) * ∏ w ∈ W, Zx G x ((C w).erase w) := by
  rw [Phi_erase G x r h.mem c, h.nbrsIn_eq, h.erase_eq, h.outside_eq,
    Phi_shift G x r (c + r) (∑ w ∈ W, A w),
    Phi_shift G x r (c + r + r * W.card - 1) (∑ w ∈ W, B w),
    Phi_biUnion G x r W C A h.disj h.noadj, Phi_biUnion G x r W _ B h.disj' h.noadj',
    Zx_biUnion G x W C h.disj h.noadj, Zx_biUnion G x W _ h.disj' h.noadj']
  ring

omit [DecidableRel G.Adj] in
/-- Dropping branches: `s' = v + ⋃_{w ∈ W'} C w` is rooted at `v` with the branches `W' ⊆ W`. -/
theorem restrict (h : RootedAt G s v W C) {W' : Finset V} (hW' : W' ⊆ W) :
    RootedAt G (insert v (W'.biUnion C)) v W' C where
  mem := Finset.mem_insert_self v _
  erase_eq := by
    rw [Finset.erase_insert]
    intro hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    exact h.notMem_root (hW' hw) hvw
  disj := fun w hw w' hw' hne => h.disj w (hW' hw) w' (hW' hw') hne
  noadj := fun w hw w' hw' hne => h.noadj w (hW' hw) w' (hW' hw') hne
  base := fun w hw => h.base w (hW' hw)
  adj_iff := fun w hw => h.adj_iff w (hW' hw)

omit [DecidableRel G.Adj] in
/-- A rooted set whose branches are connected is connected. -/
theorem connectedIn (h : RootedAt G s v W C) (hC : ∀ w ∈ W, ConnectedIn G (C w)) :
    ConnectedIn G s := by
  -- every vertex reaches the root inside `s`
  have key : ∀ y ∈ s, ReachIn G s y v := by
    intro y hy
    by_cases hyv : y = v
    · rw [hyv]
      exact Relation.ReflTransGen.refl
    · have hy' : y ∈ s.erase v := Finset.mem_erase.mpr ⟨hyv, hy⟩
      rw [h.erase_eq, Finset.mem_biUnion] at hy'
      obtain ⟨w, hw, hyw⟩ := hy'
      have hCs : C w ⊆ s := (h.subset hw).trans (Finset.erase_subset v s)
      have h1 : ReachIn G s y w := reachIn_mono hCs (hC w hw y hyw w (h.base w hw))
      have hvw : G.Adj v w := (h.adj_iff w hw w (h.base w hw)).mpr rfl
      exact h1.tail ⟨hCs (h.base w hw), h.mem, hvw.symm⟩
  intro a ha b hb
  exact (key a ha).trans (key b hb).symm

end RootedAt

/-- **Every tree is rooted at each of its vertices** by its branches. -/
theorem rootedAt_of_connectedIn (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s) {v : V}
    (hv : v ∈ s) : RootedAt G s v (nbrsIn G s v) (fun w => compIn G (s.erase v) w) where
  mem := hv
  erase_eq := erase_eq_biUnion hs hv
  disj := fun _ hw _ hw' hne => disjoint_branches hG hw hw' hne
  noadj := fun _ hw _ hw' hne _ ha _ hb => not_adj_branches hG hw hw' hne ha hb
  base := fun _ hw => self_mem_branch hw
  adj_iff := fun _ hw _ hy =>
    ⟨fun hvy => eq_of_mem_branch_of_adj hG (mem_nbrsIn.mp hw).2 hy hvy,
      fun hyw => hyw ▸ (mem_nbrsIn.mp hw).2⟩

/-! ## Graph helpers -/

omit [DecidableEq V] in
theorem nbrsIn_mono {s t : Finset V} (hst : s ⊆ t) (v : V) : nbrsIn G s v ⊆ nbrsIn G t v :=
  fun _ hw => mem_nbrsIn.mpr ⟨hst (mem_nbrsIn.mp hw).1, (mem_nbrsIn.mp hw).2⟩

theorem card_nbrsIn_lt {s : Finset V} {v : V} (hv : v ∈ s) : (nbrsIn G s v).card < s.card :=
  (Finset.card_le_card (nbrsIn_subset_erase G s v)).trans_lt (Finset.card_erase_lt_of_mem hv)

/-- Removing a vertex with at most one neighbour from a connected set keeps it connected. -/
theorem connectedIn_erase_of_card_le_one {s : Finset V} (hs : ConnectedIn G s) {ℓ : V}
    (hℓ : ℓ ∈ s) (hdeg : (nbrsIn G s ℓ).card ≤ 1) : ConnectedIn G (s.erase ℓ) := by
  rcases Nat.lt_or_ge (nbrsIn G s ℓ).card 1 with h0 | h1
  · have hN : nbrsIn G s ℓ = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [erase_eq_biUnion hs hℓ, hN, Finset.biUnion_empty]
    intro a ha
    exact absurd ha (Finset.notMem_empty a)
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (le_antisymm hdeg h1)
    rw [erase_eq_biUnion hs hℓ, ha, Finset.singleton_biUnion]
    exact connectedIn_compIn _ _

omit [DecidableEq V] in
/-- In a connected set with at least two vertices every vertex has a neighbour. -/
theorem nbrsIn_nonempty {s : Finset V} (hs : ConnectedIn G s) (h2 : 2 ≤ s.card) {y : V}
    (hy : y ∈ s) : (nbrsIn G s y).Nonempty := by
  obtain ⟨z, hz, hzy⟩ := Finset.exists_mem_ne (by omega : 1 < s.card) y
  rcases Relation.ReflTransGen.cases_head (hs y hy z hz) with h | ⟨c, hyc, _⟩
  · exact absurd h.symm hzy
  · exact ⟨c, mem_nbrsIn.mpr ⟨hyc.2.1, hyc.2.2⟩⟩

/-- A tree with at least two vertices has a leaf. -/
theorem exists_leaf (hG : G.IsAcyclic) {s : Finset V} (hs : ConnectedIn G s) (h2 : 2 ≤ s.card) :
    ∃ ℓ ∈ s, ∃ a, nbrsIn G s ℓ = {a} := by
  obtain ⟨v, -, ⟨ℓ, hℓ⟩, -⟩ := exists_leafStem hG (fun y hy => nbrsIn_nonempty hs h2 hy)
    (Finset.card_pos.mp (by omega))
  obtain ⟨hℓN, hℓl⟩ := mem_leavesAt.mp hℓ
  exact ⟨ℓ, (mem_nbrsIn.mp hℓN).1, v, hℓl⟩

omit [DecidableRel G.Adj] in
/-- A nonempty set that is not connected splits into a connected component and a nonempty rest,
with no edges between them. -/
theorem exists_split {s : Finset V} (hs : ¬ ConnectedIn G s) :
    ∃ a ∈ s, (s \ compIn G s a).Nonempty ∧
      ∀ p ∈ compIn G s a, ∀ q ∈ s \ compIn G s a, ¬ G.Adj p q := by
  unfold ConnectedIn at hs
  push_neg at hs
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  refine ⟨a, ha, ⟨b, Finset.mem_sdiff.mpr ⟨hb, fun h => hab (mem_compIn.mp h).2⟩⟩, ?_⟩
  intro p hp q hq hpq
  exact (Finset.mem_sdiff.mp hq).2
    (mem_compIn_of_adjIn hp ⟨compIn_subset _ _ hp, (Finset.mem_sdiff.mp hq).1, hpq⟩)

end Rooted

/-! ## The bridge to `FiniteForest` -/

theorem indepCount_univ_eq (F : FiniteForest) [DecidableRel F.graph.Adj] (k : ℕ) :
    indepCount F.graph Finset.univ k = independenceCount F k := by
  rw [indepCount_univ]
  unfold independenceCount
  congr

/-- `μ_F(x) = S(V)/Z(V)` for the whole vertex set of a forest. -/
theorem hardCoreMean_eq_Sx_div_Zx (F : FiniteForest) [DecidableRel F.graph.Adj] (x : ℚ) :
    hardCoreMean F (x : ℝ) =
      ((Sx F.graph x Finset.univ : ℚ) : ℝ) / ((Zx F.graph x Finset.univ : ℚ) : ℝ) := by
  have hcount : ∀ k, (indepCount F.graph Finset.univ k : ℝ) = (independenceCount F k : ℝ) := by
    intro k
    rw [indepCount_univ_eq]
  have hcard : (Finset.univ : Finset (Fin F.n)).card = F.n := by simp
  have hZ : ((Zx F.graph x Finset.univ : ℚ) : ℝ) = partitionFn F x := by
    rw [Zx_eq_sum_count, hcard]
    unfold partitionFn
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [hcount k]
  have hS : ((Sx F.graph x Finset.univ : ℚ) : ℝ) =
      ∑ k ∈ range (F.n + 1), (k : ℝ) * (independenceCount F k : ℝ) * (x : ℝ) ^ k := by
    rw [Sx_eq_sum_count, hcard]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [hcount k]
  rw [hZ, hS]
  rfl

end Erdos993Lean.Analytic.Density
