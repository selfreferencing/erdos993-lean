import Mathlib
import Erdos993Lean.Zhang.Rows.Layers

/-!
# Zhang's finite part, row soundness 5: the coverage union bound (Lemma 2.8)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemma 2.8: `Σ_m (a − m) t_{r,m} ≤ C(v−1, r−1) Σ_m (a − m) t_{1,m}`.

* `card_sdiff_avail_le`: `a − m(J) ≤ Σ_{u ∈ J} (a − m({u}))` (the covered part of `I` is a union
  of neighbourhoods).
* `sum_sum_mem_le`: a vertex lies in at most `C(|S| − 1, r − 1)` of a family of `r`-subsets.
* `union_row_holds`: **row family `union(r)`**, for every maximum independent set.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Coverage (Lemma 2.8) -/


omit [Fintype V] in
/-- The covered part of `I` is a union of neighbourhoods: `a − m(J) ≤ Σ_{u ∈ J} (a − m({u}))`. -/
theorem card_sdiff_avail_le (I J : Finset V) :
    (I \ avail G I J).card ≤ ∑ u ∈ J, (I \ avail G I {u}).card := by
  refine le_trans (card_le_card ?_) card_biUnion_le
  intro i hi
  obtain ⟨hiI, hiA⟩ := mem_sdiff.mp hi
  rw [mem_avail] at hiA
  push_neg at hiA
  obtain ⟨y, hy, hyi⟩ := hiA hiI
  rw [mem_biUnion]
  exact ⟨y, hy, mem_sdiff.mpr ⟨hiI, fun h => (mem_avail.mp h).2 y (mem_singleton_self y) hyi⟩⟩

omit [Fintype V] in
theorem card_sdiff_avail (I J : Finset V) :
    ((I \ avail G I J).card : ℚ) = I.card - (avail G I J).card := by
  rw [card_sdiff_of_subset (avail_subset G I J), Nat.cast_sub (card_le_card (avail_subset G I J))]

omit [Fintype V] in
/-- A vertex lies in at most `C(|S| − 1, r − 1)` of a family of `r`-subsets of `S`. -/
theorem sum_sum_mem_le (S : Finset V) (r : ℕ) (𝒥 : Finset (Finset V))
    (h𝒥 : 𝒥 ⊆ S.powersetCard r) (g : V → ℚ) (hg : ∀ u ∈ S, 0 ≤ g u) :
    ∑ J ∈ 𝒥, ∑ u ∈ J, g u ≤ ((S.card - 1).choose (r - 1) : ℚ) * ∑ u ∈ S, g u := by
  have hsub : ∀ J ∈ 𝒥, J ⊆ S := fun J hJ => (mem_powersetCard.mp (h𝒥 hJ)).1
  rw [sum_comm' (t' := S) (s' := fun u => 𝒥.filter (fun J => u ∈ J)) (by
    intro J u
    simp only [mem_filter]
    constructor
    · rintro ⟨hJ, hu⟩
      exact ⟨⟨hJ, hu⟩, hsub J hJ hu⟩
    · rintro ⟨⟨hJ, hu⟩, -⟩
      exact ⟨hJ, hu⟩), mul_sum]
  apply sum_le_sum
  intro u hu
  rw [sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hg u hu)
  have : (𝒥.filter (fun J => u ∈ J)).card ≤ (S.card - 1).choose (r - 1) := by
    have h := card_le_card_of_injOn (fun J => J.erase u)
      (s := 𝒥.filter (fun J => u ∈ J)) (t := (S.erase u).powersetCard (r - 1)) ?_ ?_
    · rwa [card_powersetCard, card_erase_of_mem hu] at h
    · intro J hJ
      obtain ⟨hJ1, huJ⟩ := mem_filter.mp (mem_coe.mp hJ)
      obtain ⟨hJS, hJc⟩ := mem_powersetCard.mp (h𝒥 hJ1)
      rw [mem_coe, mem_powersetCard]
      exact ⟨erase_subset_erase u hJS, by rw [card_erase_of_mem huJ, hJc]⟩
    · intro J hJ J' hJ' heq
      have huJ := (mem_filter.mp (mem_coe.mp hJ)).2
      have huJ' := (mem_filter.mp (mem_coe.mp hJ')).2
      simp only at heq
      rw [← insert_erase huJ, ← insert_erase huJ', heq]
  exact_mod_cast this

/-- **Row family `union(r)`** (Zhang, Lemma 2.8). -/
theorem union_row_holds {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) {r : ℕ}
    (hr : (Cert.Label.union r).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.union r).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv⟩ := hr
  have hY := card_univ_sdiff_eq (G := G) hmax
  have h1 : (1 : ℕ) ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  set B := Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) - 1) ((r : ℤ) - 1) with hBdef
  unfold Cert.Row.Holds
  rw [sum_vars_two hrI h1 (fun m => (G.indepNum : ℚ) - m) (fun m => ((G.indepNum : ℚ) - m) * B)
    _ _ (fun j m => by simp only [Cert.Label.row]; split_ifs <;> ring)]
  simp only [Cert.Label.row]
  rw [sum_tArr_eq hI hmax r (fun m => (G.indepNum : ℚ) - m),
    sum_tArr_eq hI hmax 1 (fun m => ((G.indepNum : ℚ) - m) * B)]
  have hB : B = ((Cert.v (Fintype.card V) G.indepNum - 1).choose (r - 1) : ℚ) :=
    binom_eq (by omega) (by omega)
  -- the one-element layer is the set of singletons
  have hsing : ∑ J ∈ indepSets G (univ \ I) 1, ((G.indepNum : ℚ) - (avail G I J).card) * B =
      B * ∑ u ∈ univ \ I, ((G.indepNum : ℚ) - (avail G I {u}).card) := by
    rw [mul_sum]
    have : indepSets G (univ \ I) 1 = (univ \ I).map ⟨singleton, singleton_injective⟩ := by
      rw [← powersetCard_one]
      unfold indepSets
      rw [filter_true_of_mem]
      intro J hJ
      obtain ⟨u, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hJ).2
      intro x hx y hy hxy
      rw [mem_singleton] at hx hy
      rw [hx, hy] at hxy
      exact G.irrefl hxy
    rw [this, sum_map]
    apply sum_congr rfl
    intro u _
    simp only [Function.Embedding.coeFn_mk]
    ring
  rw [hsing, sub_nonpos]
  -- per `J`: `a − m(J) ≤ Σ_{u ∈ J} (a − m({u}))`
  have hper : ∀ J ∈ indepSets G (univ \ I) r, (G.indepNum : ℚ) - (avail G I J).card ≤
      ∑ u ∈ J, ((G.indepNum : ℚ) - (avail G I {u}).card) := by
    intro J _
    have h := card_sdiff_avail_le (G := G) I J
    have h' : ((I \ avail G I J).card : ℚ) ≤ ∑ u ∈ J, ((I \ avail G I {u}).card : ℚ) := by
      exact_mod_cast h
    rw [card_sdiff_avail] at h'
    rw [← hmax]
    simpa only [card_sdiff_avail] using h'
  calc ∑ J ∈ indepSets G (univ \ I) r, ((G.indepNum : ℚ) - (avail G I J).card)
      ≤ ∑ J ∈ indepSets G (univ \ I) r, ∑ u ∈ J, ((G.indepNum : ℚ) - (avail G I {u}).card) :=
        sum_le_sum hper
    _ ≤ (((univ \ I).card - 1).choose (r - 1) : ℚ) *
          ∑ u ∈ univ \ I, ((G.indepNum : ℚ) - (avail G I {u}).card) := by
        apply sum_sum_mem_le (univ \ I) r _ (filter_subset _ _)
        intro u _
        have := card_le_card (avail_subset G I {u})
        rw [sub_nonneg, ← hmax]
        exact_mod_cast this
    _ = B * ∑ u ∈ univ \ I, ((G.indepNum : ℚ) - (avail G I {u}).card) := by
        rw [hB, hY]

end Forest

end Rows
end Zhang
end Erdos993Lean
