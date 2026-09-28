import Erdos993Lean.Analytic.Density.Branches

/-!
# The density induction: `μ_F(x) ≥ r n + h` for every forest with `n ≥ 8`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Source: Soul's
`SOUL/RESULTS/O5.md` §2–§3 (adjudicated CORRECT, `LEAN/referee/REVIEW_SOUL_ROUND1.md`, O5(v)).

For a valid record `R` (`Record.Valid`) and a forest `G`, by strong induction on vertex sets
(`treeClaims`): every tree `s` has `μ(s) ≥ r|s| + s0`, `μ(s) ≥ r|s| + g` if `|s| ≥ 3`, and
`μ(s) ≥ r|s| + B0` if `s` is not a path.

* Paths: the exact path bound `Record.Valid.pathBound` (closed form, `Paths.lean`).
* A nonpath tree has a vertex `v` of degree `d ≥ 3`; root it there (`rootedAt_of_connectedIn`).
  - `d ∈ {3, 4}`: the root identity `RootedAt.Phi_eq` with the boundaries of the branch types
    (`branchOK`) leaves `(Σ A − r − B0) Π Z + x (1 − (d + 1) r + Σ B − B0) Π Z' ≥ 0`, the finite
    check (`Record.Valid.check_step`).
  - `d ≥ 5`: remove one branch `C₁` (`RootedAt.Phi_remove`):
    `Φ_c(T) = Z(C₁ − w₁) Φ_c(T') + Φ_0(C₁) Z(R) + x Φ_r(C₁ − w₁) Z(R')
      + (Z(C₁) − Z(C₁ − w₁)) Φ_{c+r}(R)`
    with `T' = T − C₁` (a smaller nonpath tree), `R = T' − v`, `R' = T' − N[v]`; the last term uses
    `(d − 1) s0 ≥ 4 s0 ≥ B0 + r`, the middle ones the gains `A ≥ 0`, `A + x hi (B − r) ≥ 0`.
* Forests (`forest_s0`, `forest_h`): split off a component; `2 s0 ≥ h`, `B0 ≥ h`, and the path
  bound for paths with at least eight vertices.
* **`Record.Valid.hardCoreMean_ge`**: `μ_F(x) ≥ r n + h` for every `FiniteForest` with `n ≥ 8`.
-/

namespace Erdos993Lean.Analytic.Density

open Finset Erdos993Lean.Occupation

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Removing one branch -/

/-- **The branch-removal identity** (O5 §3, root degree `≥ 5`), with `T' = v + ⋃_{w ≠ w₁} C w`,
`R = ⋃_{w ≠ w₁} C w` and `R' = ⋃_{w ≠ w₁} (C w − w)`. -/
theorem RootedAt.Phi_remove {s : Finset V} {v : V} {W : Finset V} {C : V → Finset V}
    (h : RootedAt G s v W C) (x r : ℚ) {w1 : V} (hw1 : w1 ∈ W) (c : ℚ) :
    Phi G x r c s =
      Zx G x ((C w1).erase w1) * Phi G x r c (insert v ((W.erase w1).biUnion C)) +
      Phi G x r 0 (C w1) * Zx G x ((W.erase w1).biUnion C) +
      x * (Phi G x r r ((C w1).erase w1) *
        Zx G x ((W.erase w1).biUnion fun w => (C w).erase w)) +
      (Zx G x (C w1) - Zx G x ((C w1).erase w1)) * Phi G x r (c + r) ((W.erase w1).biUnion C) := by
  have h' := h.restrict (Finset.erase_subset w1 W)
  have hw1' : w1 ∉ W.erase w1 := Finset.notMem_erase w1 W
  have hWins : W = insert w1 (W.erase w1) := (Finset.insert_erase hw1).symm
  have hcard : W.card = (W.erase w1).card + 1 := Finset.card_erase_add_one hw1 |>.symm
  have hU : W.biUnion C = C w1 ∪ (W.erase w1).biUnion C := by
    conv_lhs => rw [hWins]
    rw [Finset.biUnion_insert]
  have hU' : (W.biUnion fun w => (C w).erase w) =
      (C w1).erase w1 ∪ (W.erase w1).biUnion fun w => (C w).erase w := by
    conv_lhs => rw [hWins]
    rw [Finset.biUnion_insert]
  have hd1 : Disjoint (C w1) ((W.erase w1).biUnion C) := by
    rw [Finset.disjoint_biUnion_right]
    intro w hw
    exact h.disj w1 hw1 w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw).symm
  have hn1 : ∀ a ∈ C w1, ∀ b ∈ (W.erase w1).biUnion C, ¬ G.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_biUnion] at hb
    obtain ⟨w, hw, hbw⟩ := hb
    exact h.noadj w1 hw1 w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw).symm a ha b hbw
  have hd2 : Disjoint ((C w1).erase w1) ((W.erase w1).biUnion fun w => (C w).erase w) := by
    rw [Finset.disjoint_biUnion_right]
    intro w hw
    exact h.disj' w1 hw1 w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw).symm
  have hn2 : ∀ a ∈ (C w1).erase w1, ∀ b ∈ (W.erase w1).biUnion (fun w => (C w).erase w),
      ¬ G.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_biUnion] at hb
    obtain ⟨w, hw, hbw⟩ := hb
    exact h.noadj' w1 hw1 w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw).symm a ha b hbw
  have e1 := Phi_erase G x r h.mem c
  rw [h.nbrsIn_eq, h.erase_eq, h.outside_eq, hU, hU'] at e1
  have e2 := Phi_erase G x r h'.mem c
  rw [h'.nbrsIn_eq, h'.erase_eq, h'.outside_eq] at e2
  have u1 := Phi_union G x r hd1 hn1 0 (c + r)
  have u2 := Phi_union G x r hd2 hn2 r (c + r + r * (W.erase w1).card - 1)
  rw [zero_add] at u1
  have ec : r + (c + r + r * ((W.erase w1).card : ℚ) - 1) = c + r + r * (W.card : ℚ) - 1 := by
    rw [hcard]
    push_cast
    ring
  rw [ec] at u2
  rw [e1, u1, u2, e2]
  ring

/-! ## The nonpath step -/

/-- **A nonpath tree has boundary `B0`**, given the claims on the smaller trees. -/
theorem nonpath_step {R : Record} (hR : R.Valid) (hG : G.IsAcyclic) {s : Finset V}
    (hs : ConnectedIn G s) (hnp : ∃ v ∈ s, 3 ≤ (nbrsIn G s v).card)
    (ih : ∀ t ⊂ s, ConnectedIn G t → t.Nonempty → TreeClaims G R t) :
    0 ≤ Phi G R.x R.r R.B0 s := by
  have hx := hR.x_pos.le
  obtain ⟨v, hv, hd⟩ := hnp
  have hRA := rootedAt_of_connectedIn hG hs hv
  set W := nbrsIn G s v with hW
  set C : V → Finset V := fun w => compIn G (s.erase v) w with hC
  have hCsub : ∀ w ∈ W, C w ⊂ s := fun w hw =>
    (hRA.subset hw).trans_ssubset (Finset.erase_ssubset hv)
  have hCconn : ∀ w ∈ W, ConnectedIn G (C w) := fun w _ => connectedIn_compIn _ _
  have hbr : ∀ w ∈ W, BranchOK G R (C w) w (branchType G (C w) w) := fun w hw =>
    branchOK hR hG (hCconn w hw) (hRA.base w hw)
      (fun D hD hDc hDne => ih D (hD.trans_ssubset (hCsub w hw)) hDc hDne)
  have hZpos : ∀ D : Finset V, 0 < Zx G R.x D := fun D => Zx_pos G hx D
  rcases Nat.lt_or_ge W.card 5 with h5 | h5
  · -- root degree 3 or 4: the finite check
    rw [hRA.Phi_eq R.x R.r (fun w => R.A (branchType G (C w) w))
      (fun w => R.B (branchType G (C w) w)) R.B0]
    have t1 : 0 ≤ ∑ w ∈ W, Phi G R.x R.r (R.A (branchType G (C w) w)) (C w) *
        ∏ w' ∈ W.erase w, Zx G R.x (C w') :=
      Finset.sum_nonneg fun w hw =>
        mul_nonneg (hbr w hw).phiA (Finset.prod_nonneg fun _ _ => (hZpos _).le)
    have t2 : 0 ≤ ∑ w ∈ W, Phi G R.x R.r (R.B (branchType G (C w) w)) ((C w).erase w) *
        ∏ w' ∈ W.erase w, Zx G R.x ((C w').erase w') :=
      Finset.sum_nonneg fun w hw =>
        mul_nonneg (hbr w hw).phiB (Finset.prod_nonneg fun _ _ => (hZpos _).le)
    have t3 := hR.check_step (fun w => branchType G (C w) w) (fun w => Zx G R.x (C w))
      (fun w => Zx G R.x ((C w).erase w)) (fun w _ => hZpos _) (fun w hw => (hbr w hw).lo)
      (fun w hw => (hbr w hw).hi) (by omega)
    have t2' := mul_nonneg hx t2
    linarith
  · -- root degree at least 5: remove one branch
    obtain ⟨w1, hw1⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
    have hRA' := hRA.restrict (Finset.erase_subset w1 W)
    set W' := W.erase w1 with hW'
    have hcard : W.card = W'.card + 1 := (Finset.card_erase_add_one hw1).symm
    set T' := insert v (W'.biUnion C) with hT'
    have hT'conn : ConnectedIn G T' :=
      hRA'.connectedIn fun w hw => hCconn w (Finset.mem_of_mem_erase hw)
    have hT'sub : T' ⊂ s := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨w1, (hRA.subset hw1 (hRA.base w1 hw1)) |> Finset.mem_of_mem_erase, ?_⟩
        intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hRA.notMem_root hw1 (h ▸ hRA.base w1 hw1)
        · rw [Finset.mem_biUnion] at h
          obtain ⟨w, hw, hw1w⟩ := h
          exact Finset.disjoint_left.mp (hRA.disj w1 hw1 w (Finset.mem_of_mem_erase hw)
            (Finset.ne_of_mem_erase hw).symm) (hRA.base w1 hw1) hw1w
      · intro y hy
        rcases Finset.mem_insert.mp hy with h | h
        · rw [h]
          exact hv
        · rw [Finset.mem_biUnion] at h
          obtain ⟨w, hw, hyw⟩ := h
          exact Finset.mem_of_mem_erase (hRA.subset (Finset.mem_of_mem_erase hw) hyw)
    have hT'np : ∃ u ∈ T', 3 ≤ (nbrsIn G T' u).card :=
      ⟨v, hRA'.mem, by rw [hRA'.nbrsIn_eq]; omega⟩
    have hPhiT' : 0 ≤ Phi G R.x R.r R.B0 T' :=
      (ih T' hT'sub hT'conn ⟨v, hRA'.mem⟩).2.2 hT'np
    -- the rest `R = T' − v`: boundary `(d − 1) s0 ≥ B0 + r`
    have hrest : 0 ≤ Phi G R.x R.r (R.B0 + R.r) (W'.biUnion C) := by
      have hsum := Phi_biUnion_nonneg G R.x R.r hx W' C (fun _ => R.s0)
        (fun w hw w' hw' hne => hRA.disj w (Finset.mem_of_mem_erase hw) w'
          (Finset.mem_of_mem_erase hw') hne)
        (fun w hw w' hw' hne => hRA.noadj w (Finset.mem_of_mem_erase hw) w'
          (Finset.mem_of_mem_erase hw') hne)
        (fun w hw => (ih _ (hCsub w (Finset.mem_of_mem_erase hw))
          (hCconn w (Finset.mem_of_mem_erase hw))
          ⟨w, hRA.base w (Finset.mem_of_mem_erase hw)⟩).1)
      rw [Finset.sum_const, nsmul_eq_mul] at hsum
      have hle : R.B0 + R.r ≤ W'.card * R.s0 := by
        have h1 := hR.B0_add_r_le
        have h2 := hR.s0_nonneg
        have h3 : (4 : ℚ) ≤ W'.card := by exact_mod_cast (by omega : 4 ≤ W'.card)
        nlinarith
      exact le_trans hsum (Phi_anti G R.x R.r hx hle _)
    -- the removed branch
    obtain ⟨hA, hB, -, hhi⟩ := hbr w1 hw1
    set t := branchType G (C w1) w1 with ht
    obtain ⟨hbig1, hbig2⟩ := hR.big t
    rw [hRA.Phi_remove R.x R.r hw1 R.B0]
    set Z1 := Zx G R.x (C w1) with hZ1
    set Z1' := Zx G R.x ((C w1).erase w1) with hZ1'
    set P := Zx G R.x (W'.biUnion C) with hP
    set P' := Zx G R.x (W'.biUnion fun w => (C w).erase w) with hP'
    have hZ1pos : 0 < Z1 := hZpos _
    have hZ1'pos : 0 < Z1' := hZpos _
    have hPpos : 0 < P := hZpos _
    have hP'pos : 0 < P' := hZpos _
    have hP'le : P' ≤ P := Zx_mono G hx (Finset.biUnion_mono fun w _ => Finset.erase_subset w (C w))
    have hZ1le : Z1' ≤ Z1 := Zx_mono G hx (Finset.erase_subset w1 (C w1))
    have e0 : Phi G R.x R.r 0 (C w1) = Phi G R.x R.r (R.A t) (C w1) + R.A t * Z1 := by
      rw [Phi_shift G R.x R.r 0 (R.A t)]
      ring
    have er : Phi G R.x R.r R.r ((C w1).erase w1) =
        Phi G R.x R.r (R.B t) ((C w1).erase w1) + (R.B t - R.r) * Z1' := by
      rw [Phi_shift G R.x R.r R.r (R.B t)]
    rw [e0, er]
    -- the gains
    have hgain : 0 ≤ R.A t * Z1 * P + R.x * ((R.B t - R.r) * Z1' * P') := by
      rcases le_total 0 (R.B t - R.r) with hBr | hBr
      · have : 0 ≤ R.x * ((R.B t - R.r) * Z1' * P') := by positivity
        have : 0 ≤ R.A t * Z1 * P := by positivity
        linarith
      · have h1 : Z1' * P' ≤ R.hi t * Z1 * P := by
          have := mul_le_mul hhi hP'le hP'pos.le (by
            have := hR.lo_nonneg t
            have := hhi
            nlinarith [hZ1'pos])
          linarith
        have h2 : R.x * (R.B t - R.r) * (R.hi t * Z1 * P) ≤ R.x * (R.B t - R.r) * (Z1' * P') :=
          mul_le_mul_of_nonpos_left h1 (mul_nonpos_of_nonneg_of_nonpos hx hBr)
        have h3 : 0 ≤ Z1 * P * (R.A t + R.x * R.hi t * (R.B t - R.r)) :=
          mul_nonneg (mul_nonneg hZ1pos.le hPpos.le) hbig2
        nlinarith
    have hterm1 : 0 ≤ Z1' * Phi G R.x R.r R.B0 T' := mul_nonneg hZ1'pos.le hPhiT'
    have hterm2 : 0 ≤ Phi G R.x R.r (R.A t) (C w1) * P := mul_nonneg hA hPpos.le
    have hterm3 : 0 ≤ R.x * (Phi G R.x R.r (R.B t) ((C w1).erase w1) * P') :=
      mul_nonneg hx (mul_nonneg hB hP'pos.le)
    have hterm4 : 0 ≤ (Z1 - Z1') * Phi G R.x R.r (R.B0 + R.r) (W'.biUnion C) :=
      mul_nonneg (by linarith) hrest
    nlinarith

/-! ## The claims -/

/-- **The density induction on trees.** -/
theorem treeClaims {R : Record} (hR : R.Valid) (hG : G.IsAcyclic) :
    ∀ s : Finset V, ConnectedIn G s → s.Nonempty → TreeClaims G R s := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs hne
    have hx := hR.x_pos.le
    have hgB : R.g ≤ R.B0 := hR.g_le_h.trans hR.h_le_B0
    have hsB : R.s0 ≤ R.B0 := hR.s0_le_g.trans hgB
    by_cases hnp : ∃ v ∈ s, 3 ≤ (nbrsIn G s v).card
    · have hB0 := nonpath_step hR hG hs hnp ih
      exact ⟨le_trans hB0 (Phi_anti G R.x R.r hx hsB s),
        fun _ => le_trans hB0 (Phi_anti G R.x R.r hx hgB s), fun _ => hB0⟩
    · push_neg at hnp
      have hps : IsPathSet G s := ⟨hs, fun v hv => by have := hnp v hv; omega⟩
      have hj : 1 ≤ s.card := Finset.card_pos.mpr hne
      have hpb := hR.pathBound s.card hj
      have hz := zP_pos hx s.card
      refine ⟨?_, fun h3 => ?_, fun ⟨v, hv, h3⟩ => absurd (hnp v hv) (by omega)⟩
      · rw [IsPathSet.Phi_eq hG R.x R.r _ hps]
        have := hR.s0_le_pathConst s.card
        nlinarith
      · rw [IsPathSet.Phi_eq hG R.x R.r _ hps]
        have := hR.g_le_pathConst h3
        nlinarith

/-- **Every nonempty forest has boundary `s0`.** -/
theorem forest_s0 {R : Record} (hR : R.Valid) (hG : G.IsAcyclic) :
    ∀ s : Finset V, s.Nonempty → 0 ≤ Phi G R.x R.r R.s0 s := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hne
    have hx := hR.x_pos.le
    by_cases hs : ConnectedIn G s
    · exact (treeClaims hR hG s hs hne).1
    · obtain ⟨a, ha, hrest, hno⟩ := exists_split hs
      have hsub : compIn G s a ⊆ s := compIn_subset s a
      have hdisj : Disjoint (compIn G s a) (s \ compIn G s a) := Finset.disjoint_sdiff
      have hsplit : s = compIn G s a ∪ (s \ compIn G s a) :=
        (Finset.union_sdiff_of_subset hsub).symm
      have h1 : 0 ≤ Phi G R.x R.r R.s0 (compIn G s a) :=
        (treeClaims hR hG _ (connectedIn_compIn s a) ⟨a, self_mem_compIn ha⟩).1
      have h2 : 0 ≤ Phi G R.x R.r R.s0 (s \ compIn G s a) :=
        ih _ (Finset.sdiff_ssubset hsub ⟨a, self_mem_compIn ha⟩) hrest
      have h3 : 0 ≤ Phi G R.x R.r (R.s0 + R.s0) s := by
        rw [hsplit, Phi_union G R.x R.r hdisj hno]
        exact add_nonneg (mul_nonneg h1 (Zx_pos G hx _).le) (mul_nonneg (Zx_pos G hx _).le h2)
      exact le_trans h3 (Phi_anti G R.x R.r hx (by linarith [hR.s0_nonneg]) s)

/-- **Every forest with at least eight vertices has boundary `h`.** -/
theorem forest_h {R : Record} (hR : R.Valid) (hG : G.IsAcyclic) (s : Finset V)
    (h8 : 8 ≤ s.card) : 0 ≤ Phi G R.x R.r R.h s := by
  have hx := hR.x_pos.le
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hs : ConnectedIn G s
  · by_cases hnp : ∃ v ∈ s, 3 ≤ (nbrsIn G s v).card
    · exact le_trans ((treeClaims hR hG s hs hne).2.2 hnp)
        (Phi_anti G R.x R.r hx hR.h_le_B0 s)
    · push_neg at hnp
      have hps : IsPathSet G s := ⟨hs, fun v hv => by have := hnp v hv; omega⟩
      have hpb := hR.pathBound s.card (by omega)
      rw [R.pathConst_eq_h h8] at hpb
      rw [IsPathSet.Phi_eq hG R.x R.r _ hps]
      linarith
  · obtain ⟨a, ha, hrest, hno⟩ := exists_split hs
    have hsub : compIn G s a ⊆ s := compIn_subset s a
    have hdisj : Disjoint (compIn G s a) (s \ compIn G s a) := Finset.disjoint_sdiff
    have hsplit : s = compIn G s a ∪ (s \ compIn G s a) :=
      (Finset.union_sdiff_of_subset hsub).symm
    have h1 := forest_s0 hR hG (compIn G s a) ⟨a, self_mem_compIn ha⟩
    have h2 := forest_s0 hR hG (s \ compIn G s a) hrest
    have h3 : 0 ≤ Phi G R.x R.r (R.s0 + R.s0) s := by
      rw [hsplit, Phi_union G R.x R.r hdisj hno]
      exact add_nonneg (mul_nonneg h1 (Zx_pos G hx _).le) (mul_nonneg (Zx_pos G hx _).le h2)
    exact le_trans h3 (Phi_anti G R.x R.r hx (by linarith [hR.h_le_two_s0]) s)

/-- **The certified density record in hard-core form (O5 §2):** for a valid record and every
finite forest with at least eight vertices, `μ_F(x) ≥ r n + h`. -/
theorem Record.Valid.hardCoreMean_ge {R : Record} (hR : R.Valid) (F : FiniteForest)
    (hn : 8 ≤ F.n) : (R.r : ℝ) * F.n + R.h ≤ hardCoreMean F R.x := by
  classical
  have key := forest_h hR F.isForest (Finset.univ : Finset (Fin F.n)) (by simpa using hn)
  have hZ := Zx_pos F.graph hR.x_pos.le (Finset.univ : Finset (Fin F.n))
  rw [hardCoreMean_eq_Sx_div_Zx]
  unfold Phi at key
  rw [Finset.card_univ, Fintype.card_fin] at key
  have hZR : (0 : ℝ) < ((Zx F.graph R.x Finset.univ : ℚ) : ℝ) := by exact_mod_cast hZ
  rw [le_div_iff₀ hZR]
  have h1 : (R.r * F.n + R.h) * Zx F.graph R.x Finset.univ ≤ Sx F.graph R.x Finset.univ := by
    linarith
  exact_mod_cast h1

end Erdos993Lean.Analytic.Density
