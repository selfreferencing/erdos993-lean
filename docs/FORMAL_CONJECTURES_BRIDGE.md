# Erdős Problem #993: the public formal-conjectures statement, proved from our Lean theorem

Results as of 29 September 2026. The build and the axiom printout were re-run on the committed tree, from
2026-09-29 11:26:45 EDT to 2026-09-29 11:27:51 EDT. The branch `formal-conjectures-bridge` is on the public
repository selfreferencing/erdos993-lean, with the bridge commit `5d68f21` plus the commit adding this document. It
is not merged into `main`, and the tag v1.0-claim is unchanged at `865e814`.

## Result

The Lean statement of Erdős Problem #993 in google-deepmind/formal-conjectures (pull request #4192) was copied verbatim
into our Lean package and proved from our theorem `Erdos993Lean.Analytic.erdos993`. Neither statement was modified.

| | |
|---|---|
| Compiles | **Yes.** `lake build Erdos993LeanFormalConjectures` reports "Build completed successfully (8710 jobs)". No warnings, no `sorry`. |
| Theorem proved | `Erdos993.erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsTree → Erdos993.UnimodalSeq (Erdos993.indepSeq G)` |
| `#print axioms Erdos993.erdos_993` | `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`, the same five as `Erdos993Lean.Analytic.erdos993` |
| Axioms added by the bridge | None. The four bridge lemmas use only `propext`, `Classical.choice` and `Quot.sound`. |
| Changes to the public text | Two: the attribute line is omitted, and `sorry` is replaced by a two-line proof. |
| Changes to our statement | None. |
| Where | Repository erdos993-lean, branch `formal-conjectures-bridge`, commit `5d68f21`, on top of public `main` (`865e814`, tag v1.0-claim). Pushed to the public repository selfreferencing/erdos993-lean (plus the commit adding this document); not merged into `main`; tag v1.0-claim unchanged at `865e814`. |
| Independent review | Four checks passed: verbatim text, elaboration environment, axioms, Mathlib versions. Its four wording fixes are applied. |

## 1. The public statement

**Source.**
- Repository: google-deepmind/formal-conjectures.
- Pull request #4192, by AlperTheKing, titled "feat(Erdos993): state the conjecture and prove spider local tie-balance".
- At 11:26 EDT on 29 September the PR was **open and unmerged**, with head commit
  `41a7d7493384b447ec707833e1cae7f5956b2bc6` (checked with `gh pr view`).
- File `FormalConjectures/ErdosProblems/993.lean`, lines 35–52. The file is not on formal-conjectures `main`.
- Licence: Apache 2.0. Our file says so in its header.

**The PR's lines 35–52, exactly as published:**
```lean
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
@[category research open, AMS 5]
theorem erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → UnimodalSeq (indepSeq G) := by
  sorry
```

**Our copy.** Our file contains the same lines with exactly two changes. The output of `diff` (the PR's lines 35–52 on
the left, our block on the right) is:
```
15d14
< @[category research open, AMS 5]
18c17,20
<   sorry
---
>   intro V _ G hG
>   exact Erdos993Lean.FormalConjecturesBridge.unimodal_nat_card_of_acyclic G hG.IsAcyclic
> 
> end Erdos993
```
- The attribute line needs formal-conjectures' own import, `FormalConjectures.Util.ProblemImports`, which does not
  exist in our package.
- `sorry` is replaced by a two-line proof.
- `end Erdos993` closes the namespace. The PR closes it at its line 977, after its own lemmas on spiders.
- The 16 shared lines are byte-identical: no trailing spaces, tabs or carriage returns.

**Nothing changes how the text elaborates.**
- Lines 1–34 of the PR file are the licence, the import and a docstring. They contain no `open`, `variable`, `set_option`
  or `universe` command, so the statement elaborates in namespace `Erdos993` with nothing opened.
- In our file, the copied block follows the bridge namespace. The only `open` (`open SimpleGraph`) sits inside that
  namespace and is closed before the block. Our package's only global instances are `Decidable` instances on its own
  predicates.
- The reviewer printed `indepSeq`, `UnimodalSeq` and the type of `erdos_993` with `set_option pp.all true`, once under
  `import Mathlib` alone and once under our import. The two outputs are byte-identical: the same instances, coercions
  and universes.

## 2. Compilation and axioms

**Build.** `lake build Erdos993LeanFormalConjectures` reports "Build completed successfully (8710 jobs)".
- The new module compiles in about 35 s. The other 8,709 jobs are the existing proof, already built.
- There are no warnings, and no `sorry`.

**Axiom printout**, verbatim, from `lake env lean Audit/AxiomsFormalConjectures.lean`:
```
Erdos993.erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsTree → Erdos993.UnimodalSeq (Erdos993.indepSeq G)
'Erdos993.erdos_993' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'Erdos993Lean.Analytic.erdos993' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
'Erdos993Lean.FormalConjecturesBridge.unimodal_of_unimodalUpTo_of_zero' depends on axioms: [propext, Quot.sound]
'Erdos993Lean.FormalConjecturesBridge.isIndepSet_map_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos993Lean.FormalConjecturesBridge.count_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos993Lean.FormalConjecturesBridge.count_eq_zero_of_indepNum_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

**Reading it.**
- `Erdos993.erdos_993` depends on the same five axioms as `Erdos993Lean.Analytic.erdos993`, so the bridge adds none.
- The two non-standard axioms, `Lean.ofReduceBool` and `Lean.trustCompiler`, come from `native_decide`. According to the
  header of `Erdos993Lean/Analytic/Erdos993.lean`, the analytic route (forests with at least 61 vertices) evaluates
  271 certificates that way: 30 tail bands, 60 atlas bands, 13 O1 checks and 168 O2 root boxes.
- The finite part (forests with at most 60 vertices, Zhang's 17,100 certificates) is checked by the Lean kernel itself.
- The four bridge lemmas use only the standard axioms.

## 3. The three definitional mismatches, and the exact Lean that bridges each

Our theorem is `Erdos993Lean.Analytic.erdos993 : Erdos993Statement`, with these definitions (from
`Erdos993Lean/Statement.lean`):
```lean
structure FiniteForest where
  n : Nat
  graph : SimpleGraph (Fin n)
  isForest : graph.IsAcyclic

def UnimodalUpTo (N : Nat) (a : Nat → Nat) : Prop :=
  ∃ peak : Nat, peak ≤ N ∧ (∀ k : Nat, k < peak → a k ≤ a (k + 1)) ∧
    (∀ k : Nat, peak ≤ k → k < N → a (k + 1) ≤ a k)

noncomputable def independenceCount (F : FiniteForest) (k : Nat) : Nat := by
  classical
  exact (F.graph.indepSetFinset k).card

noncomputable def independenceNumber (F : FiniteForest) : Nat := F.graph.indepNum

noncomputable def independenceSequenceUnimodal (F : FiniteForest) : Prop :=
  UnimodalUpTo (independenceNumber F) (independenceCount F)

noncomputable def Erdos993Statement : Prop := ∀ forest : FiniteForest, independenceSequenceUnimodal forest
```

### Mismatch 1: vertex type and graph class

- **The difference.** The public statement is about trees on an arbitrary finite type `V`. Ours is about acyclic graphs
  (forests) on `Fin n`.
- **The bridge.**
  - A tree is acyclic: the field `SimpleGraph.IsTree.IsAcyclic`.
  - The equivalence `Fintype.equivFin V : V ≃ Fin (Fintype.card V)` moves the graph to `Fin n` by `comap`, which keeps it
    acyclic (Mathlib's `IsAcyclic.of_comap`).
  - The bridge is therefore proved for every finite forest, not only for trees.
```lean
/-- The finite forest on `Fin (Fintype.card V)` obtained from an acyclic graph on a finite type `V`. -/
noncomputable def forestOf {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) : FiniteForest where
  n := Fintype.card V
  graph := G.comap (Fintype.equivFin V).symm.toEmbedding
  isForest := IsAcyclic.of_comap (Fintype.equivFin V).symm.toEmbedding hG
```

### Mismatch 2: how independent sets are counted

- **The difference.**
  - `indepSeq G k` is `Nat.card` of the subtype of `Finset V` of `k`-element independent sets.
  - `independenceCount` is the cardinality of Mathlib's `indepSetFinset k` on `Fin n`.
- **The bridge.** The map `s ↦ s.map (Fintype.equivFin V)` is a bijection between the two. It keeps both size and
  independence.
```lean
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
```

### Mismatch 3: the range of unimodality

- **The difference.** `UnimodalSeq` asks for a peak on all of `ℕ`. Ours, `UnimodalUpTo (independenceNumber F)`, asks
  only up to the independence number, with the peak at most that number.
- **The bridge.** Above the independence number every count is zero, from Mathlib's `IsIndepSet.card_le_indepNum`, and
  the zeros close the gap.
```lean
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
```

### Assembly, and the proof of the public statement

```lean
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
```
Inside the copied block, `sorry` is replaced by:
```lean
  intro V _ G hG
  exact Erdos993Lean.FormalConjecturesBridge.unimodal_nat_card_of_acyclic G hG.IsAcyclic
```

**No other gaps.**
- Both statements use weak unimodality, with `≤` on both sides of the peak.
- Neither needs a strict peak.
- No special case for small graphs is needed. (`IsTree` implies that `V` is nonempty, and the bridge does not use it.)

## 4. Lean and Mathlib versions

**The two pins.** At that commit, formal-conjectures pins Lean `v4.27.0` and Mathlib `v4.27.0` (`a3a10db0e9`). Our
package pins `v4.28.0` for both (Mathlib `8f9d9cff6b`). Their package cannot be imported as a dependency, which is why
the statement's text is copied. **The theorem proved is that text, elaborated against Mathlib v4.28.0.**

**What changed between the two Mathlib versions.** The definitions the statement uses were diffed in our local Mathlib
clone, which has both tags, and the reviewer extracted the declaration blocks at both tags.
- Unchanged: `IsTree`, `Connected`, `Preconnected`, `Reachable`, `Walk`, the walk functions (`support`, `darts`,
  `edges`, `tail`), `IsTrail`, `IsCircuit`, `IsCycle`, `IsAcyclic`, `Dart`, `Sym2`, `IsIndepSet`, `Set.Pairwise`,
  `Nat.card`, `Finset.card` and `Fintype`.
- **One definitional change: the field `loopless` of the structure `SimpleGraph`.**
  ```lean
  -- Mathlib v4.27.0
  loopless : Irreflexive Adj := by aesop_graph
  -- Mathlib v4.28.0
  loopless : Std.Irrefl Adj := by aesop_graph
  ```
  Both say that no vertex is adjacent to itself. So the graphs on a type, and hence the statement's meaning, are the
  same in the two versions, but the Lean terms are not literally identical.
- **Not checked.**
  - The Lean core itself also moved from v4.27 to v4.28 (`List.Nodup`, `List.tail`, `Std.Irrefl`).
  - Formal-conjectures' own environment also imports its `FormalConjecturesForMathlib` library, whose `SimpleGraph`
    file declares no instances or notations.

## 5. Independent review

A referee agent, separate from the author, checked the claims on its own, with read-only GitHub access.

| Check | Result |
|---|---|
| 1. Verbatim | **PASS.** It fetched the PR file at the head commit from GitHub itself and confirmed the PR is open and unmerged. The PR's lines 35–52 differ from our block only by the two declared changes; the shared lines have equal sha256. |
| 2. Elaboration environment | **PASS.** The `pp.all` printouts under `import Mathlib` alone and under our import are byte-identical. |
| 3. Axioms | **PASS.** It re-ran the audit: the axioms are as printed above, there is no `sorryAx`, and recompiling the bridge file produced no warnings. |
| 4. Mathlib versions | **PASS.** 22 declaration blocks are identical at both tags, except `SimpleGraph.loopless`. |
| 5. Wording of the earlier report | Four fixes, all applied here: the order of the other PRs, "should work" for the n ≥ 21 variant, the push status, and the full list of Mathlib changes. |

## 6. Scope and caveats

- **The statement is not merged.** It lives in an open pull request. If its text changes before a merge, the bridge
  must be re-checked against the merged version. The `diff` takes seconds, and the build about half a minute.
- **Mathlib version.** The statement is elaborated against Mathlib v4.28.0, not formal-conjectures' v4.27.0; see §4.
- **Trust.** It includes `native_decide`, through the certificate evaluations of the analytic route; see §2.
- **The bridge proves more than the statement.** `unimodal_nat_card_of_acyclic` covers every acyclic graph on a finite
  type, that is, every finite forest.
- **Pushed.** The branch `formal-conjectures-bridge` (commit `5d68f21` plus the commit adding this document) is on
  the public repository selfreferencing/erdos993-lean, not merged into `main`; the tag v1.0-claim is unchanged at
  `865e814`.

## 7. Reproduce

```bash
git clone https://github.com/selfreferencing/erdos993-lean.git
cd erdos993-lean
git checkout formal-conjectures-bridge
lake build Erdos993LeanFormalConjectures
lake env lean Audit/AxiomsFormalConjectures.lean
```
The build needs the existing `Erdos993LeanTheorem` build, which is the whole proof; see this branch's README for how
that build is done. From a warm cache it takes about half a minute.

## Appendix A. `Erdos993Lean/FormalConjectures/Erdos993.lean`, complete

sha256 `8a8f5322f2ed7a7526f7df091d8c5f36c0a70d8429558c2ddf5050dc7862ae1d`
```lean
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
```

## Appendix B. `Audit/AxiomsFormalConjectures.lean`

sha256 `ee473e87f36acfbc77f2f1b4812e9a09b28487573e44834f2dc07e208eb567b2`
```lean
import Erdos993Lean.FormalConjectures.Erdos993

/-! Prints the axioms of `Erdos993.erdos_993`, the statement of Erdős Problem #993 in google-deepmind/formal-conjectures
(pull request #4192, copied verbatim), proved from `Erdos993Lean.Analytic.erdos993`, and of the four bridge lemmas.
Run: `lake build Erdos993LeanFormalConjectures`, then `lake env lean Audit/AxiomsFormalConjectures.lean`. -/

#check (Erdos993.erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  G.IsTree → Erdos993.UnimodalSeq (Erdos993.indepSeq G))
#print axioms Erdos993.erdos_993
#print axioms Erdos993Lean.Analytic.erdos993

-- The bridge lemmas on their own (standard axioms only).
#print axioms Erdos993Lean.FormalConjecturesBridge.unimodal_of_unimodalUpTo_of_zero
#print axioms Erdos993Lean.FormalConjecturesBridge.isIndepSet_map_iff
#print axioms Erdos993Lean.FormalConjecturesBridge.count_eq
#print axioms Erdos993Lean.FormalConjecturesBridge.count_eq_zero_of_indepNum_lt
```

## Appendix C. The entry added to `lakefile.toml`

```toml
# Optional: the statement of Erdős Problem 993 in google-deepmind/formal-conjectures (pull request #4192, copied
# verbatim), proved from `Erdos993Lean.Analytic.erdos993`.  `lake build Erdos993LeanFormalConjectures`.
[[lean_lib]]
name = "Erdos993LeanFormalConjectures"
roots = ["Erdos993Lean.FormalConjectures.Erdos993"]
```
