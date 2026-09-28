import Mathlib
import Erdos993Lean.Zhang.Rows.Basic

/-!
# Zhang's finite part, row soundness 2: the sparse-complement selection (Lemma 2.5)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemma 2.5: a forest has a maximum independent set `I` whose complement `Y`
spans `e(F[Y]) ≤ E = max(0, δ − 1)` edges (`δ = a − v`), and `e(F[Y]) ≤ v − 1` when `v ≥ 1`.

The paper contracts a maximum matching and swaps terminal-free monochromatic blocks of a
minimizer of `e(F[Y])`.  The Lean proof is a direct induction on vertex sets (`exists_sparse`),
with `δ(s) = 2 α(G[s]) − |s|`:
* an isolated vertex joins `I` (`δ` grows by one, `e` is unchanged);
* at a leaf stem `w` (`Occupation.exists_leafStem`: `k ≥ 1` leaves and at most one other
  neighbour `u`), with `s* = s − w − leaves`: `α(s) = α(s*) + k` (König and `ν(s) = ν(s*) + 1`),
  so `δ(s) = δ(s*) + k − 1`.  For `k = 1`, `w` joins `I` when `u ∉ I*` and the leaf joins it
  otherwise; `e` is unchanged.  For `k ≥ 2` the leaves join `I`, adding at most the edge `wu`,
  which `δ(s) ≥ δ(s*) + 1` pays, except when `δ(s*) = 0`: then `I*` is the colour class of `u`
  (`exists_colorClass`), and nothing is added.

Main results:
* `exists_sparse` (vertex-set form): `∃ I ⊆ s` maximum independent with
  `e(G[s \ I]) ≤ 2 α(G[s]) − |s| − 1`.
* `exists_sparse_maxIndep` (the form used by `RowsSound`): for an acyclic `G` on a finite type,
  `∃ I`, independent, `|I| = G.indepNum`, `e(G[V \ I]) ≤ Cert.E n a` and `≤ Cert.v n a − 1`.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Lemma 2.5: a maximum independent set with a sparse complement -/

/-- **Zhang, Lemma 2.5 (sparse-complement selection), vertex-set form.**  Every vertex set `s`
of an acyclic graph has a maximum independent subset `I` whose complement spans at most
`max(0, δ(s) − 1)` edges, `δ(s) = 2 α(G[s]) − |s|` (natural subtraction).  Proof by induction:
an isolated vertex joins `I` (`δ` grows by one); at a leaf stem `w` with `k` leaves and at most
one other neighbour `u`, `δ(s) = δ(s − w − leaves) + k − 1`, and either `w` joins `I` (when
`k = 1` and `u ∉ I`) or the leaves do (adding at most the edge `wu`); when the residual set has
`δ = 0` its independent set is the colour class of `u`. -/
theorem exists_sparse (hG : G.IsAcyclic) (s : Finset V) :
    ∃ I ⊆ s, IsIndepFinset G I ∧ I.card = alphaIn G s ∧
      eIn G (s \ I) ≤ 2 * alphaIn G s - s.card - 1 := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hiso : ∃ x ∈ s, nbrsIn G s x = ∅
    · obtain ⟨x, hx, hxn⟩ := hiso
      obtain ⟨I, hIs, hI, hIc, he⟩ := ih _ (erase_ssubset hx)
      have hxI : x ∉ I := fun h => (mem_erase.mp (hIs h)).1 rfl
      have key : ∀ y ∈ s, ¬ G.Adj x y := by
        intro y hy hxy
        have hmem : y ∈ nbrsIn G s x := mem_nbrsIn.mpr ⟨hy, hxy⟩
        rw [hxn] at hmem
        exact notMem_empty y hmem
      refine ⟨insert x I, insert_subset hx (hIs.trans (erase_subset x s)), ?_, ?_, ?_⟩
      · intro a ha b hb hab
        rw [mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl hab
        · exact key b (mem_of_mem_erase (hIs hb)) hab
        · exact key a (mem_of_mem_erase (hIs ha)) hab.symm
        · exact hI a ha b hb hab
      · rw [card_insert_of_notMem hxI, hIc, alphaIn_isolated hx hxn]
      · have hsd : s \ insert x I = (s.erase x) \ I := by
          ext y
          simp only [mem_sdiff, mem_insert, mem_erase]
          tauto
        rw [hsd, alphaIn_isolated hx hxn]
        have h1 := card_erase_add_one hx
        have h2 := card_le_two_mul_alphaIn hG (s.erase x)
        omega
    · push_neg at hiso
      rcases s.eq_empty_or_nonempty with rfl | hne
      · refine ⟨∅, empty_subset _, isIndepFinset_empty, by rw [alphaIn_empty, card_empty], ?_⟩
        rw [empty_sdiff, eIn_empty]
        exact Nat.zero_le _
      · obtain ⟨w, hw, ⟨ℓ0, hℓ0⟩, hU⟩ := Occupation.exists_leafStem hG hiso hne
        set Λ := Occupation.leavesAt G s w with hΛdef
        set U := Occupation.stemsAt G s w with hUdef
        set H := Occupation.residualAt G s w with hHdef
        have hsplit : s.erase w = H ∪ Λ := Occupation.erase_eq_residualAt_union G s w
        have hdisj : Disjoint H Λ := Occupation.disjoint_residualAt_leavesAt G s w
        have hcard : s.card = H.card + Λ.card + 1 := by
          rw [← card_erase_add_one hw, hsplit, card_union_of_disjoint hdisj]
        have hmem : ∀ y, y ∈ s ↔ y = w ∨ y ∈ H ∨ y ∈ Λ := by
          intro y
          constructor
          · intro hy
            by_cases hyw : y = w
            · exact Or.inl hyw
            · have : y ∈ s.erase w := mem_erase.mpr ⟨hyw, hy⟩
              rw [hsplit, mem_union] at this
              exact Or.inr this
          · rintro (h | h | h)
            · rw [h]
              exact hw
            · have : y ∈ s.erase w := by
                rw [hsplit]
                exact mem_union_left _ h
              exact mem_of_mem_erase this
            · have : y ∈ s.erase w := by
                rw [hsplit]
                exact mem_union_right _ h
              exact mem_of_mem_erase this
        have hwH : w ∉ H := fun h => by
          have : w ∈ s.erase w := by
            rw [hsplit]
            exact mem_union_left _ h
          exact (mem_erase.mp this).1 rfl
        have hwΛ : w ∉ Λ := fun h => by
          have : w ∈ s.erase w := by
            rw [hsplit]
            exact mem_union_right _ h
          exact (mem_erase.mp this).1 rfl
        have hHs : H ⊆ s := fun y hy => (hmem y).mpr (Or.inr (Or.inl hy))
        have hΛs : Λ ⊆ s := fun y hy => (hmem y).mpr (Or.inr (Or.inr hy))
        have hHss : H ⊂ s := (ssubset_iff_of_subset hHs).mpr ⟨w, hw, hwH⟩
        -- `α(s) = α(H) + |Λ|` (König and `ν(s) = ν(H) + 1`)
        have hα : alphaIn G s = alphaIn G H + Λ.card := by
          have k1 := alphaIn_add_nuIn hG s
          have k2 := alphaIn_add_nuIn hG H
          have k3 := Occupation.nuIn_leafStem (G := G) hℓ0
          rw [← hHdef] at k3
          omega
        have hHα := card_le_two_mul_alphaIn hG H
        -- the neighbours of `w`
        have hUH : U ⊆ H := by
          intro u hu
          obtain ⟨huN, hun⟩ := Occupation.mem_stemsAt.mp hu
          obtain ⟨hus, hwu⟩ := mem_nbrsIn.mp huN
          rcases (hmem u).mp hus with h | h | h
          · rw [h] at hwu
            exact (G.irrefl hwu).elim
          · exact h
          · exact absurd (Occupation.mem_leavesAt.mp h).2 hun
        have hNwH : ∀ y ∈ H, G.Adj w y → y ∈ U := by
          intro y hy hwy
          have hyN : y ∈ nbrsIn G s w := mem_nbrsIn.mpr ⟨hHs hy, hwy⟩
          rw [Occupation.nbrsIn_eq_union G s w, mem_union] at hyN
          rcases hyN with h | h
          · exact absurd h (disjoint_left.mp hdisj hy)
          · exact h
        have hΛN : ∀ ℓ ∈ Λ, ∀ y ∈ s, G.Adj ℓ y → y = w := fun ℓ hℓ y hy hadj =>
          Occupation.eq_of_adj_leaf hℓ hy hadj
        -- the independent set of the residual set
        obtain ⟨I', hI's, hI', hI'c, he', hU'⟩ : ∃ I' ⊆ H, IsIndepFinset G I' ∧
            I'.card = alphaIn G H ∧ eIn G (H \ I') ≤ 2 * alphaIn G H - H.card - 1 ∧
            (2 * alphaIn G H = H.card → U ⊆ I') := by
          by_cases hδ : 2 * alphaIn G H = H.card
          · obtain ⟨x, hx⟩ : ∃ x, U ⊆ {x} := by
              rcases U.eq_empty_or_nonempty with h | ⟨x, hx⟩
              · exact ⟨w, by rw [h]; exact empty_subset _⟩
              · exact ⟨x, fun y hy => mem_singleton.mpr (card_le_one.mp hU y hy x hx)⟩
            obtain ⟨I', hI's, hI', hI'c, hY', hxI'⟩ := exists_colorClass hG H hδ x
            refine ⟨I', hI's, hI', hI'c, by rw [eIn_eq_zero_of_indep hY']; exact Nat.zero_le _,
              fun _ y hy => ?_⟩
            have hyx := mem_singleton.mp (hx hy)
            rw [hyx] at hy ⊢
            exact hxI' (hUH hy)
          · obtain ⟨I', hI's, hI', hI'c, he'⟩ := ih H hHss
            exact ⟨I', hI's, hI', hI'c, he', fun h => absurd h hδ⟩
        have hwI' : w ∉ I' := fun h => hwH (hI's h)
        by_cases hA : Λ.card = 1 ∧ ∃ x ∈ U, x ∉ I'
        · -- `w` joins the independent set
          obtain ⟨hk, x, hxU, hxI'⟩ := hA
          obtain ⟨ℓ, hΛℓ⟩ := card_eq_one.mp hk
          have hℓΛ : ℓ ∈ Λ := by
            rw [hΛℓ]
            exact mem_singleton_self ℓ
          have hUx : U = {x} := eq_singleton_iff_unique_mem.mpr
            ⟨hxU, fun y hy => card_le_one.mp hU y hy x hxU⟩
          refine ⟨insert w I', insert_subset hw (hI's.trans hHs), ?_, ?_, ?_⟩
          · have key : ∀ y ∈ I', ¬ G.Adj w y := by
              intro y hy hwy
              have hyU := hNwH y (hI's hy) hwy
              rw [hUx, mem_singleton] at hyU
              rw [hyU] at hy
              exact hxI' hy
            intro a ha b hb hab
            rw [mem_insert] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · rw [ha, hb] at hab
              exact G.irrefl hab
            · rw [ha] at hab
              exact key b hb hab
            · rw [hb] at hab
              exact key a ha hab.symm
            · exact hI' a ha b hb hab
          · rw [card_insert_of_notMem hwI', hI'c, hα, hk]
          · have hsd : s \ insert w I' = insert ℓ (H \ I') := by
              ext y
              simp only [mem_sdiff, mem_insert]
              constructor
              · rintro ⟨hy, hne⟩
                push_neg at hne
                rcases (hmem y).mp hy with h | h | h
                · exact absurd h hne.1
                · exact Or.inr ⟨h, hne.2⟩
                · rw [hΛℓ, mem_singleton] at h
                  exact Or.inl h
              · rintro (h | ⟨hy, hyI⟩)
                · rw [h]
                  refine ⟨hΛs hℓΛ, ?_⟩
                  push_neg
                  exact ⟨fun h' => hwΛ (h' ▸ hℓΛ), fun h' => disjoint_left.mp hdisj (hI's h') hℓΛ⟩
                · refine ⟨hHs hy, ?_⟩
                  push_neg
                  exact ⟨fun h' => hwH (h' ▸ hy), hyI⟩
            have hℓHI : ℓ ∉ H \ I' := fun h => disjoint_left.mp hdisj (mem_sdiff.mp h).1 hℓΛ
            have hN : nbrsIn G (H \ I') ℓ = ∅ := by
              rw [eq_empty_iff_forall_notMem]
              intro y hy
              obtain ⟨hy1, hadj⟩ := mem_nbrsIn.mp hy
              have hyH := (mem_sdiff.mp hy1).1
              have := hΛN ℓ hℓΛ y (hHs hyH) hadj
              exact hwH (this ▸ hyH)
            rw [hsd, eIn_insert hℓHI, hN, card_empty, add_zero, hα, hcard, hk]
            omega
        · -- the leaves join the independent set
          refine ⟨I' ∪ Λ, union_subset (hI's.trans hHs) hΛs, ?_, ?_, ?_⟩
          · intro a ha b hb hab
            rw [mem_union] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact hI' a ha b hb hab
            · exact Occupation.residualAt_noAdj a (hI's ha) b hb hab
            · exact Occupation.residualAt_noAdj b (hI's hb) a ha hab.symm
            · exact Occupation.leavesAt_edgeless a ha b hb hab
          · rw [card_union_of_disjoint (disjoint_of_subset_left hI's hdisj), hI'c, hα]
          · have hsd : s \ (I' ∪ Λ) = insert w (H \ I') := by
              ext y
              simp only [mem_sdiff, mem_union, mem_insert]
              constructor
              · rintro ⟨hy, hne⟩
                push_neg at hne
                rcases (hmem y).mp hy with h | h | h
                · exact Or.inl h
                · exact Or.inr ⟨h, hne.1⟩
                · exact absurd h hne.2
              · rintro (h | ⟨hy, hyI⟩)
                · rw [h]
                  refine ⟨hw, ?_⟩
                  push_neg
                  exact ⟨hwI', hwΛ⟩
                · refine ⟨hHs hy, ?_⟩
                  push_neg
                  exact ⟨hyI, fun h' => disjoint_left.mp hdisj hy h'⟩
            have hwHI : w ∉ H \ I' := fun h => hwH (mem_sdiff.mp h).1
            have hNsub : nbrsIn G (H \ I') w ⊆ U \ I' := by
              intro y hy
              obtain ⟨hy1, hadj⟩ := mem_nbrsIn.mp hy
              obtain ⟨hyH, hyI⟩ := mem_sdiff.mp hy1
              exact mem_sdiff.mpr ⟨hNwH y hyH hadj, hyI⟩
            have hx1 : (nbrsIn G (H \ I') w).card ≤ 1 :=
              (card_le_card hNsub).trans ((card_le_card sdiff_subset).trans hU)
            have hx0 : U ⊆ I' → (nbrsIn G (H \ I') w).card = 0 := by
              intro hUI
              rw [card_eq_zero, eq_empty_iff_forall_notMem]
              intro y hy
              have := mem_sdiff.mp (hNsub hy)
              exact this.2 (hUI this.1)
            have hk1 : Λ.card = 1 → U ⊆ I' := by
              intro hk y hy
              by_contra hyI
              exact hA ⟨hk, y, hy, hyI⟩
            have hkpos : 1 ≤ Λ.card := card_pos.mpr ⟨ℓ0, hℓ0⟩
            rw [hsd, eIn_insert hwHI, hα, hcard]
            by_cases hδ : 2 * alphaIn G H = H.card
            · have := hx0 (hU' hδ)
              omega
            · by_cases hk : Λ.card = 1
              · have := hx0 (hk1 hk)
                omega
              · omega

end General

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Zhang, Lemma 2.5 (sparse-complement selection).**  A forest has a maximum independent set
`I` whose complement `Y = V \ I` spans at most `E = max(0, δ − 1)` edges (`v = n − a`,
`δ = a − v`), and at most `v − 1` edges. -/
theorem exists_sparse_maxIndep (hG : G.IsAcyclic) :
    ∃ I : Finset V, IsIndepFinset G I ∧ I.card = G.indepNum ∧
      eIn G (univ \ I) ≤ Cert.E (Fintype.card V) G.indepNum ∧
      eIn G (univ \ I) ≤ Cert.v (Fintype.card V) G.indepNum - 1 := by
  obtain ⟨I, -, hI, hIc, he⟩ := exists_sparse hG (univ : Finset V)
  rw [alphaIn_univ] at he hIc
  rw [card_univ] at he
  have hn := SmallAlpha.card_le_two_mul_indepNum hG
  have ha : G.indepNum ≤ Fintype.card V := by
    rw [← hIc]
    exact card_le_univ I
  refine ⟨I, hI, hIc, ?_, ?_⟩
  · unfold Cert.E Cert.δ Cert.v
    omega
  · have h := eIn_le_card_sub_one hG (univ \ I)
    rw [card_univ_sdiff, hIc] at h
    exact h

end Forest

end Rows
end Zhang
end Erdos993Lean
