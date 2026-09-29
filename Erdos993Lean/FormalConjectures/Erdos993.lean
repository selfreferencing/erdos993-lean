import Mathlib
import Erdos993Lean.Analytic.Erdos993

/-!
# The formal-conjectures statement of Erdős Problem 993, proved from `Erdos993Lean.Analytic.erdos993`

## Source of the statement

The definitions `Erdos993.indepSeq` and `Erdos993.UnimodalSeq` and the statement of `Erdos993.erdos_993` below are
copied verbatim, with their doc comments, from

* repository `google-deepmind/formal-conjectures`, pull request #4192 ("feat(Erdos993): state the conjecture and
  prove spider local tie-balance"; open, not merged, as of 2026-09-29), head commit
  `41a7d7493384b447ec707833e1cae7f5956b2bc6`, file `FormalConjectures/ErdosProblems/993.lean`, lines 35–52.

That file is licensed under the Apache License, Version 2.0 (copyright 2026 The Formal Conjectures Authors).

Only two things differ from the source:
* the attribute line `@[category research open, AMS 5]` is omitted, because it needs
  `FormalConjectures.Util.ProblemImports`;
* the proof `sorry` is replaced by a proof.

Neither the statement of `Erdos993.erdos_993` nor the two definitions it uses are changed.

The formal-conjectures package itself cannot be imported here. At that commit it pins `leanprover/lean4:v4.27.0` and
Mathlib `v4.27.0` (`a3a10db0e9`), while this package pins `v4.28.0` for both (Mathlib `8f9d9cff6b`). Between those two
Mathlib versions, the definitions the statement uses (`SimpleGraph.IsTree`, `SimpleGraph.IsAcyclic`,
`SimpleGraph.IsIndepSet`, `Set.Pairwise`, `Nat.card`, `Fintype`) are textually unchanged. The one change is the field
`loopless` of the structure `SimpleGraph`, whose type went from `Irreflexive Adj` to `Std.Irrefl Adj`; both say that
no vertex is adjacent to itself.

## The bridge

`Erdos993Lean.Analytic.erdos993 : Erdos993Statement` quantifies over `FiniteForest`s, which are acyclic simple graphs
on `Fin n`. It counts independent sets with Mathlib's `indepSetFinset` and asserts weak unimodality up to the
independence number. Three mismatches are bridged in `Erdos993Lean.FormalConjecturesBridge`:

1. **Vertex type and graph class.** The formal-conjectures statement is about trees on an arbitrary finite type `V`.
   A tree is acyclic (`SimpleGraph.IsTree.IsAcyclic`), and `V ≃ Fin (Fintype.card V)` transports the graph to
   `Fin n` by `SimpleGraph.comap`, which preserves acyclicity (`SimpleGraph.IsAcyclic.of_comap`). The bridge in fact
   proves the conclusion for every finite forest, not only for trees.
2. **Counting.** `indepSeq G k` is `Nat.card` of a subtype of `Finset V`. `independenceCount` is the cardinality of
   `indepSetFinset k` on `Fin n`. The two agree by the bijection `s ↦ s.map e` (`count_eq`), which preserves
   independence (`isIndepSet_map_iff`).
3. **Unimodality.** `UnimodalSeq` asks for a peak on all of `ℕ`, while `UnimodalUpTo (indepNum)` asks only up to the
   independence number. The counts vanish above the independence number (`count_eq_zero_of_indepNum_lt`, from
   `SimpleGraph.IsIndepSet.card_le_indepNum`), and that closes the gap (`unimodal_of_unimodalUpTo_of_zero`).
-/

namespace Erdos993Lean.FormalConjecturesBridge

open SimpleGraph

/-- A peak up to `N`, followed by zeros above `N`, is a peak on all of `ℕ`. -/
theorem unimodal_of_unimodalUpTo_of_zero {N : ℕ} {a : ℕ → ℕ} (h : UnimodalUpTo N a)
    (hz : ∀ k, N < k → a k = 0) :
    ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i) := by
  obtain ⟨peak, _hpN, hup, hdown⟩ := h
  refine ⟨peak, hup, ?_⟩
  intro i hi
  by_cases hiN : i < N
  · exact hdown i hi hiN
  · rw [hz (i + 1) (by omega)]
    exact Nat.zero_le _

/-- The finite forest on `Fin (Fintype.card V)` obtained from an acyclic graph on a finite type `V`. -/
noncomputable def forestOf {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) : FiniteForest where
  n := Fintype.card V
  graph := G.comap (Fintype.equivFin V).symm.toEmbedding
  isForest := IsAcyclic.of_comap (Fintype.equivFin V).symm.toEmbedding hG

/-- Transporting a finite set along `Fintype.equivFin V` preserves independence. -/
theorem isIndepSet_map_iff {V : Type} [Fintype V] (G : SimpleGraph V) (s : Finset V) :
    (G.comap (Fintype.equivFin V).symm.toEmbedding).IsIndepSet
        (↑(s.map (Fintype.equivFin V).toEmbedding) : Set (Fin (Fintype.card V))) ↔
      G.IsIndepSet (s : Set V) := by
  constructor
  · intro h a ha b hb hab hadj
    have ha' : (Fintype.equivFin V) a ∈ (↑(s.map (Fintype.equivFin V).toEmbedding) : Set _) := by
      simpa using ha
    have hb' : (Fintype.equivFin V) b ∈ (↑(s.map (Fintype.equivFin V).toEmbedding) : Set _) := by
      simpa using hb
    exact h ha' hb' (fun e => hab ((Fintype.equivFin V).injective e)) (by simpa using hadj)
  · intro h a ha b hb hab hadj
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact h ha' hb' (fun e => hab (e ▸ rfl)) (by simpa using hadj)

/-- The two ways of counting `k`-element independent sets agree. -/
theorem count_eq {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) (k : ℕ) :
    Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)} =
      independenceCount (forestOf G hG) k := by
  classical
  unfold independenceCount forestOf
  dsimp only
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine (Fintype.equivFin V).finsetCongr.subtypeEquiv ?_
  intro s
  rw [mem_indepSetFinset_iff, isNIndepSet_iff, Equiv.finsetCongr_apply, Finset.card_map]
  exact and_comm.trans (and_congr_left fun _ => (isIndepSet_map_iff G s).symm)

/-- There are no independent sets larger than the independence number. -/
theorem count_eq_zero_of_indepNum_lt (F : FiniteForest) {k : ℕ} (hk : independenceNumber F < k) :
    independenceCount F k = 0 := by
  classical
  simp only [independenceCount, Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [mem_indepSetFinset_iff, isNIndepSet_iff] at hs
  have hle := hs.1.card_le_indepNum
  simp only [independenceNumber] at hk
  omega

/-- **The bridge.** Every finite forest on any finite type has a unimodal independence sequence in the
formal-conjectures sense, by `Erdos993Lean.Analytic.erdos993`. -/
theorem unimodal_nat_card_of_acyclic {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ m, (∀ i, i < m → Nat.card {s : Finset V // s.card = i ∧ G.IsIndepSet (s : Set V)} ≤
        Nat.card {s : Finset V // s.card = (i + 1) ∧ G.IsIndepSet (s : Set V)}) ∧
      (∀ i, m ≤ i → Nat.card {s : Finset V // s.card = (i + 1) ∧ G.IsIndepSet (s : Set V)} ≤
        Nat.card {s : Finset V // s.card = i ∧ G.IsIndepSet (s : Set V)}) := by
  have hU : independenceSequenceUnimodal (forestOf G hG) := Erdos993Lean.Analytic.erdos993 (forestOf G hG)
  have := unimodal_of_unimodalUpTo_of_zero hU
    (fun k hk => count_eq_zero_of_indepNum_lt (forestOf G hG) hk)
  simpa only [count_eq G hG] using this

end Erdos993Lean.FormalConjecturesBridge

/- ---------------------------------------------------------------------------------------------------------
   Verbatim from google-deepmind/formal-conjectures, PR #4192, commit 41a7d7493384b447ec707833e1cae7f5956b2bc6,
   FormalConjectures/ErdosProblems/993.lean, lines 35–52 (attribute line omitted; `sorry` replaced by a proof).
   --------------------------------------------------------------------------------------------------------- -/

namespace Erdos993

/-- `indepSeq G k` is the number of `k`-element independent sets of `G`, i.e. the `k`-th term
`i_k(G)` of the independence sequence. -/
noncomputable def indepSeq {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)}

/-- A sequence `a : ℕ → ℕ` is *unimodal* if it is nondecreasing up to some index `m` and
nonincreasing thereafter. -/
def UnimodalSeq (a : ℕ → ℕ) : Prop :=
  ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i)

/-- **Erdős Problem 993.** The independence sequence `i_k(T)` of every finite tree `T` is
unimodal. (Conjectured by Alavi, Malde, Schwenk and Erdős [AMSE87]; open.) -/
theorem erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → UnimodalSeq (indepSeq G) := by
  intro V _ G hG
  exact Erdos993Lean.FormalConjecturesBridge.unimodal_nat_card_of_acyclic G hG.IsAcyclic

end Erdos993
