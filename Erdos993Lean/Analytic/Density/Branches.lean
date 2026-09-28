import Erdos993Lean.Analytic.Density.Record

/-!
# The five branch types and their data

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Source: Soul's
`SOUL/RESULTS/O5.md` §3 "Branches at a root of degree 3 or 4".

A branch is a tree `C` inside the forest with a base vertex `w ∈ C` (the neighbour of the root).
`branchType G C w ∈ {0, …, 4}`: `|C| = 1`; `|C| = 2`; `|C| = 3` with `w` a leaf of `C`; `|C| = 3`
with `w` the centre; `|C| ≥ 4`.  `BranchOK G R C w t` records what the density induction uses about
a branch of type `t`: `Φ_{A t}(C) ≥ 0`, `Φ_{B t}(C − w) ≥ 0` (i.e. `μ(C) − r|C| ≥ A t` and
`μ(C − w) − r(|C| − 1) ≥ B t`) and `lo t · Z(C) ≤ Z(C − w) ≤ hi t · Z(C)`.

* **`branchOK`**: every branch satisfies `BranchOK` for its type, given the induction claims
  (`TreeClaims`) on the trees inside it.  Types 0–3 are paths or the cherry and are exact
  (`Φ = 0`, ratios `Z(P_{j−1})/Z(P_j)` and `(1 + x)²/Z(P_3)`); type 4 uses the claim `g` for `C`
  itself and, for `C − w`, the claim `g` when `w` is a leaf of `C` and `k · s0 ≥ 2 s0 ≥ g` over the
  `k ≥ 2` branches of `C` at `w` otherwise; its ratio lies in `[1/(1 + x), 1]`.
-/

namespace Erdos993Lean.Analytic.Density

open Finset Erdos993Lean.Occupation

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The type of the branch `C` with base `w`. -/
def branchType (C : Finset V) (w : V) : Fin 5 :=
  if C.card ≤ 1 then 0 else if C.card = 2 then 1 else if C.card = 3 then
    (if (nbrsIn G C w).card ≤ 1 then 2 else 3) else 4

variable (G) in
/-- The claims of the density induction for a tree `s`: `μ(s) ≥ r|s| + s0`; `μ(s) ≥ r|s| + g` if
`|s| ≥ 3`; `μ(s) ≥ r|s| + B0` if `s` is not a path. -/
def TreeClaims (R : Record) (s : Finset V) : Prop :=
  0 ≤ Phi G R.x R.r R.s0 s ∧ (3 ≤ s.card → 0 ≤ Phi G R.x R.r R.g s) ∧
    ((∃ v ∈ s, 3 ≤ (nbrsIn G s v).card) → 0 ≤ Phi G R.x R.r R.B0 s)

variable (G) in
/-- The data of a branch `C` with base `w` of type `t`. -/
structure BranchOK (R : Record) (C : Finset V) (w : V) (t : Fin 5) : Prop where
  phiA : 0 ≤ Phi G R.x R.r (R.A t) C
  phiB : 0 ≤ Phi G R.x R.r (R.B t) (C.erase w)
  lo : R.lo t * Zx G R.x C ≤ Zx G R.x (C.erase w)
  hi : Zx G R.x (C.erase w) ≤ R.hi t * Zx G R.x C

/-- At the exact mean `c = μ_n − r n`, the surplus of a path set with `n` vertices vanishes. -/
theorem Phi_path_eq_zero (hG : G.IsAcyclic) {x : ℚ} (hx : 0 ≤ x) (r : ℚ) {s : Finset V}
    (hs : IsPathSet G s) {n : ℕ} (hn : s.card = n) {c : ℚ} (hc : c = sP x n / zP x n - r * n) :
    Phi G x r c s = 0 := by
  rw [IsPathSet.Phi_eq hG x r c hs, hn, hc]
  have := zP_pos hx n
  field_simp
  ring

omit [DecidableEq V] in
theorem isPathSet_empty : IsPathSet G (∅ : Finset V) :=
  ⟨fun a ha => absurd ha (Finset.notMem_empty a), fun v hv => absurd hv (Finset.notMem_empty v)⟩

/-- Types 0–2: a path branch whose base is an end. -/
theorem branchOK_path {R : Record} (hR : R.Valid) (hG : G.IsAcyclic) {C : Finset V} {w : V}
    (hC : IsPathSet G C) (hCw : IsPathSet G (C.erase w)) (hw : w ∈ C) {n : ℕ}
    (hn : C.card = n + 1) (t : Fin 5)
    (hA : R.A t = sP R.x (n + 1) / zP R.x (n + 1) - R.r * ((n + 1 : ℕ) : ℚ))
    (hB : R.B t = sP R.x n / zP R.x n - R.r * n)
    (hlo : R.lo t = zP R.x n / zP R.x (n + 1)) (hhi : R.hi t = zP R.x n / zP R.x (n + 1)) :
    BranchOK G R C w t := by
  have hx := hR.x_pos.le
  have hn' : (C.erase w).card = n := by rw [Finset.card_erase_of_mem hw, hn]; rfl
  have hZ : Zx G R.x C = zP R.x (n + 1) := by rw [(IsPathSet.values hG R.x C hC).1, hn]
  have hZ' : Zx G R.x (C.erase w) = zP R.x n := by
    rw [(IsPathSet.values hG R.x _ hCw).1, hn']
  have hz := zP_pos hx (n + 1)
  have e : zP R.x n / zP R.x (n + 1) * zP R.x (n + 1) = zP R.x n := by field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Phi_path_eq_zero hG hx R.r hC hn hA]
  · rw [Phi_path_eq_zero hG hx R.r hCw hn' hB]
  · rw [hlo, hZ, hZ', e]
  · rw [hhi, hZ, hZ', e]

/-- **Every branch satisfies the data of its type.** -/
theorem branchOK {R : Record} (hR : R.Valid) (hG : G.IsAcyclic) {C : Finset V}
    (hC : ConnectedIn G C) {w : V} (hw : w ∈ C)
    (ih : ∀ D ⊆ C, ConnectedIn G D → D.Nonempty → TreeClaims G R D) :
    BranchOK G R C w (branchType G C w) := by
  have hx := hR.x_pos.le
  have hC1 : 1 ≤ C.card := Finset.card_pos.mpr ⟨w, hw⟩
  unfold branchType
  split_ifs with h1 h2 h3 h4
  · -- type 0: `C = {w}`
    have hc : C.card = 0 + 1 := by omega
    exact branchOK_path hR hG (isPathSet_of_card_le_three hC (by omega))
      (by
        have : C.erase w = ∅ := by
          rw [← Finset.card_eq_zero, Finset.card_erase_of_mem hw]
          omega
        rw [this]
        exact isPathSet_empty)
      hw hc 0 (by simp [Record.A, Record.mu]) (by simp [Record.B, Record.mu])
      (by simp [Record.lo]) (by simp [Record.hi])
  · -- type 1: two vertices
    have hc : C.card = 1 + 1 := by omega
    have hdeg : (nbrsIn G C w).card ≤ 1 := by have := card_nbrsIn_lt (G := G) hw; omega
    exact branchOK_path hR hG (isPathSet_of_card_le_three hC (by omega))
      (isPathSet_of_card_le_three (connectedIn_erase_of_card_le_one hC hw hdeg)
        (by rw [Finset.card_erase_of_mem hw]; omega))
      hw hc 1 (by simp [Record.A, Record.mu]; ring) (by simp [Record.B, Record.mu])
      (by simp [Record.lo]) (by simp [Record.hi])
  · -- type 2: three vertices, the base is an end
    have hc : C.card = 2 + 1 := by omega
    exact branchOK_path hR hG (isPathSet_of_card_le_three hC (by omega))
      (isPathSet_of_card_le_three (connectedIn_erase_of_card_le_one hC hw h4)
        (by rw [Finset.card_erase_of_mem hw]; omega))
      hw hc 2 (by simp [Record.A, Record.mu]; ring) (by simp [Record.B, Record.mu]; ring)
      (by simp [Record.lo]) (by simp [Record.hi])
  · -- type 3: the cherry, the base is the centre
    push_neg at h4
    have hsub : nbrsIn G C w ⊆ C.erase w := nbrsIn_subset_erase G C w
    have hcard : (C.erase w).card = 2 := by rw [Finset.card_erase_of_mem hw]; omega
    have heq : nbrsIn G C w = C.erase w :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact h4)
    obtain ⟨u, y, huy, hUY⟩ := Finset.card_eq_two.mp hcard
    have hu : u ∈ nbrsIn G C w := by rw [heq, hUY]; simp
    have hy : y ∈ nbrsIn G C w := by rw [heq, hUY]; simp
    have hnadj : ¬ G.Adj u y := fun h =>
      not_triangle hG (mem_nbrsIn.mp hu).2 (mem_nbrsIn.mp hy).2 h
    have hdisj : Disjoint ({u} : Finset V) {y} := Finset.disjoint_singleton.mpr huy
    have hno : ∀ a ∈ ({u} : Finset V), ∀ b ∈ ({y} : Finset V), ¬ G.Adj a b := by
      intro a ha b hb
      rw [Finset.mem_singleton] at ha hb
      rw [ha, hb]
      exact hnadj
    have hUY' : C.erase w = {u} ∪ {y} := by rw [hUY]; rfl
    have hZuy : Zx G R.x (C.erase w) = (1 + R.x) ^ 2 := by
      rw [hUY', Zx_union G R.x hdisj hno, Zx_singleton, Zx_singleton]
      ring
    have hSuy : Sx G R.x (C.erase w) = 2 * R.x * (1 + R.x) := by
      rw [hUY', Sx_union G R.x hdisj hno, Zx_singleton, Zx_singleton, Sx_singleton, Sx_singleton]
      ring
    have hC3 : IsPathSet G C := isPathSet_of_card_le_three hC (by omega)
    have hZC : Zx G R.x C = zP R.x 3 := by rw [(IsPathSet.values hG R.x C hC3).1, h3]
    have hz3 := zP_pos hx 3
    have hz1 : zP R.x 1 = 1 + R.x := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Phi_path_eq_zero hG hx R.r hC3 h3 (by simp [Record.A, Record.mu]; ring)]
    · have hB3 : R.B 3 = 2 * (R.x / (1 + R.x)) - 2 * R.r := by
        simp [Record.B, Record.mu, sP, zP]
      have e : Phi G R.x R.r (R.B 3) (C.erase w) = 0 := by
        unfold Phi
        rw [hZuy, hSuy, hcard, hB3]
        have : (0 : ℚ) < 1 + R.x := by linarith
        field_simp
        ring
      rw [e]
    · have : R.lo 3 = zP R.x 1 ^ 2 / zP R.x 3 := by simp [Record.lo]
      rw [this, hZC, hZuy, hz1]
      field_simp
      rfl
    · have : R.hi 3 = zP R.x 1 ^ 2 / zP R.x 3 := by simp [Record.hi]
      rw [this, hZC, hZuy, hz1]
      field_simp
      rfl
  · -- type 4: at least four vertices
    have hC4 : 4 ≤ C.card := by omega
    have hclaims := ih C (Finset.Subset.refl C) hC ⟨w, hw⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : R.A 4 = R.g := by simp [Record.A]
      rw [this]
      exact hclaims.2.1 (by omega)
    · have hB4 : R.B 4 = R.g := by simp [Record.B]
      rw [hB4]
      have hne : (nbrsIn G C w).Nonempty := nbrsIn_nonempty hC (by omega) hw
      rcases Nat.lt_or_ge (nbrsIn G C w).card 2 with hd | hd
      · -- `w` is a leaf of `C`: `C − w` is a tree with at least three vertices
        have hconn := connectedIn_erase_of_card_le_one hC hw (by omega)
        have hcard : 3 ≤ (C.erase w).card := by rw [Finset.card_erase_of_mem hw]; omega
        exact (ih _ (Finset.erase_subset w C) hconn
          (Finset.card_pos.mp (by omega))).2.1 hcard
      · -- at least two branches at `w`, each with boundary `s0`
        have hRA := rootedAt_of_connectedIn hG hC hw
        have hsum := Phi_biUnion_nonneg G R.x R.r hx (nbrsIn G C w)
          (fun u => compIn G (C.erase w) u) (fun _ => R.s0) hRA.disj hRA.noadj
          (fun u hu => (ih _ ((hRA.subset hu).trans (Finset.erase_subset w C))
            (connectedIn_compIn _ _) ⟨u, hRA.base u hu⟩).1)
        rw [← hRA.erase_eq, Finset.sum_const, nsmul_eq_mul] at hsum
        have hg2 : R.g ≤ (nbrsIn G C w).card * R.s0 := by
          have h1 := hR.g_le_h
          have h2 := hR.h_le_two_s0
          have h3 := hR.s0_nonneg
          have h4 : (2 : ℚ) ≤ (nbrsIn G C w).card := by exact_mod_cast hd
          nlinarith
        exact le_trans hsum (Phi_anti G R.x R.r hx hg2 _)
    · have : R.lo 4 = 1 / zP R.x 1 := by simp [Record.lo]
      rw [this]
      have h1 := Zx_le_erase G hx hw
      have hz1 : zP R.x 1 = 1 + R.x := rfl
      rw [hz1, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
      linarith
    · have : R.hi 4 = 1 := by simp [Record.hi]
      rw [this, one_mul]
      exact Zx_mono G hx (Finset.erase_subset w C)

end Erdos993Lean.Analytic.Density
