import Mathlib
import Erdos993Lean.Statement
import Erdos993Lean.Ceiling.Statement
import Erdos993Lean.SmallAlpha.BipartiteTail
import Erdos993Lean.Zhang.Konig
import Erdos993Lean.Zhang.Decomposition
import Erdos993Lean.Zhang.CoefficientBounds
import Erdos993Lean.Zhang.Relaxation

/-!
# Zhang's finite part, 5: the forest bridge and the reduction of Theorem 2.1

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Theorem 2.1 (every forest with at most 60 vertices is unimodal) and its
proof (Sections 2.7–2.8).

This file connects the graph side (`Zhang/Decomposition.lean`, `Zhang/CoefficientBounds.lean`)
to the relaxation (`Zhang/Relaxation.lean`) and proves the reduction:

* `tArr G I`: the count array `t_{j,m}` of a graph relative to `I` (all vertices), over `ℚ`.
* `card_indepSetFinset_eq`: **(3)** in the relaxation's variables,
  `c_r = C(a, r) + Σ_{(j,m) ∈ vars} C(m, r − j) t_{j,m}` for a maximum independent `I`.
* `delta_eq`: **(31)**, `c_{k+1} − c_k = delta n a t (k + 1)`.
* `basic_tArr`: the array satisfies the basic constraints (5) (any maximum independent `I`).
* `count_row_holds`, `path_row_holds`: the row families `count` and `path` hold for the array of
  every forest and every maximum independent `I` (from (5) and Lemma 2.2 (6)).
* `unimodal_of_noRecovery`: a sequence with no recovery below `K` and nonincreasing from `K` is
  unimodal (the reduction (34)).
* `RowsSound`: the named hypothesis that every forest with an edge has a maximum independent set
  whose array satisfies **all** row families on their domains (Zhang's Lemmas 2.3–2.10 with the
  choice of Lemma 2.5; `count` and `path` are proved here, the other nine families are not yet
  formalized).
* **`finite60_of_sound : RowsSound → Cert.CertificatesSound → ∀ F, F.n ≤ 60 → unimodal`**: the
  finite theorem reduced to row soundness and the certificate layer's no-recovery claims on
  `P60` (Table 1).  The edgeless forests are handled directly (`(1 + z)^n`), the tail by the
  package's bipartite tail (`SmallAlpha.card_indepSetFinset_succ_le`, = Zhang's Lemma 2.11).

Grade: PROVED IN LEAN (complete proofs, standard axioms only), with `RowsSound` and
`CertificatesSound` as explicit hypotheses of the final theorem.
-/

namespace Erdos993Lean
namespace Zhang

open Finset

section Bridge

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The count array `t_{j,m}` of `G` relative to `I` (the ambient set is all of `V`), over `ℚ`. -/
def tArr (I : Finset V) (j m : ℕ) : ℚ := (tCount G Finset.univ I j m : ℚ)

theorem card_univ_sdiff (I : Finset V) :
    (Finset.univ \ I).card = Fintype.card V - I.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ]

/-- The counts `t_{j,m}` with `m > a − j` vanish, so the layer sums may be cut at `m ≤ a − j`. -/
theorem sum_tCount_trim {I : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum)
    (j : ℕ) :
    ∑ m ∈ range (G.indepNum + 1 - j), tCount G Finset.univ I j m =
      ∑ m ∈ range (I.card + 1), tCount G Finset.univ I j m := by
  apply Finset.sum_subset
  · intro m hm
    rw [mem_range] at hm ⊢
    omega
  · intro m hm hm'
    rw [mem_range] at hm hm'
    apply tCount_eq_zero_of_alphaIn_lt hI (Finset.subset_univ I)
    rw [alphaIn_univ]
    omega

/-- **Zhang (3) in the relaxation's variables**: for a maximum independent set `I`,
`c_r = C(a, r) + Σ_{(j,m) ∈ vars} C(m, r − j) t_{j,m}` (over `ℚ`, paper's binomials). -/
theorem card_indepSetFinset_eq {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (r : ℕ) :
    ((G.indepSetFinset r).card : ℚ) = Cert.binom G.indepNum r +
      ∑ p ∈ Cert.vars (Fintype.card V) G.indepNum,
        Cert.binom p.2 ((r : ℤ) - p.1) * tArr G I p.1 p.2 := by
  have hmax' : I.card = alphaIn G Finset.univ := by rw [alphaIn_univ, hmax]
  have h := indepCount_eq_paper hI (Finset.subset_univ I) hmax' r
  rw [indepCount_univ] at h
  have hv : (Finset.univ \ I).card = Cert.v (Fintype.card V) G.indepNum := by
    rw [card_univ_sdiff, hmax]
    rfl
  rw [h, Cert.sum_vars (Fintype.card V) G.indepNum
    (fun j m => Cert.binom m ((r : ℤ) - j) * tArr G I j m), Cert.binom_natCast, hmax, hv]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hterm : ∀ m : ℕ, ((tCount G Finset.univ I j m : ℕ) : ℚ) *
      (if j ≤ r then ((m.choose (r - j) : ℕ) : ℚ) else 0) =
        Cert.binom m ((r : ℤ) - j) * tArr G I j m := by
    intro m
    rw [Cert.binom_sub_natCast]
    unfold tArr
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  symm
  apply Finset.sum_subset
  · intro m hm
    rw [mem_range] at hm ⊢
    omega
  · intro m hm hm'
    rw [mem_range] at hm hm'
    have h0 : tCount G Finset.univ I j m = 0 := by
      apply tCount_eq_zero_of_alphaIn_lt hI (Finset.subset_univ I)
      rw [← hmax', hmax]
      omega
    simp [tArr, h0]

/-- **Zhang (31)**: `c_{k+1} − c_k = B_{a,0}(k+1) + Σ B_{m,j}(k+1) t_{j,m}`. -/
theorem delta_eq {I : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum) (k : ℕ) :
    ((G.indepSetFinset (k + 1)).card : ℚ) - (G.indepSetFinset k).card =
      Cert.delta (Fintype.card V) G.indepNum (tArr G I) (k + 1) := by
  rw [card_indepSetFinset_eq hI hmax (k + 1), card_indepSetFinset_eq hI hmax k]
  unfold Cert.delta Cert.B
  have e1 : ∀ j : ℕ, ((k + 1 : ℕ) : ℤ) - j - 1 = (k : ℤ) - j := by
    intro j
    push_cast
    ring
  simp only [e1, Nat.cast_zero, sub_zero]
  rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring]
  have hsum : ∑ p ∈ Cert.vars (Fintype.card V) G.indepNum,
      (Cert.binom p.2 (((k + 1 : ℕ) : ℤ) - p.1) - Cert.binom p.2 ((k : ℤ) - p.1)) *
        tArr G I p.1 p.2 =
      ∑ p ∈ Cert.vars (Fintype.card V) G.indepNum,
        Cert.binom p.2 (((k + 1 : ℕ) : ℤ) - p.1) * tArr G I p.1 p.2 -
      ∑ p ∈ Cert.vars (Fintype.card V) G.indepNum,
        Cert.binom p.2 ((k : ℤ) - p.1) * tArr G I p.1 p.2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsum]
  ring

/-- The array of any maximum independent set satisfies the basic constraints (5). -/
theorem basic_tArr {I : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum) :
    Cert.Basic (Fintype.card V) G.indepNum (tArr G I) where
  nonneg := fun _ _ => Nat.cast_nonneg _
  layer_one := by
    unfold Cert.layerSum tArr
    rw [← Nat.cast_sum, sum_tCount_trim hI hmax 1, sum_tCount_one, card_univ_sdiff, hmax]
    rfl
  layer_le := by
    intro j _
    unfold Cert.layerSum tArr Cert.W Cert.v
    rw [← Nat.cast_sum, sum_tCount_trim hI hmax j, Cert.binom_natCast]
    have h := sum_tCount_le_choose (G := G) Finset.univ I j
    rw [card_univ_sdiff, hmax] at h
    rw [hmax]
    exact_mod_cast h

/-- The row family `count(r)` holds (`T_r ≤ C(v, r)`). -/
theorem count_row_holds {I : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum)
    {r : ℕ} (hr : (Cert.Label.count r).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.count r).row (Fintype.card V) G.indepNum).Holds (Fintype.card V) G.indepNum
      (tArr G I) := by
  unfold Cert.Label.InDomain at hr
  unfold Cert.Row.Holds Cert.Label.row
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Cert.sum_vars_layer (Finset.mem_Icc.mpr ⟨by omega, hr.2⟩)
    (fun j m => tArr G I j m)]
  exact (basic_tArr hI hmax).layer_le r (Finset.mem_Icc.mpr hr)

theorem binom_path (n r : ℕ) : Cert.binom ((n : ℤ) - r + 1) r = ((n + 1 - r).choose r : ℚ) := by
  rcases Nat.lt_or_ge (n + 1) r with h | h
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.choose_eq_zero_of_lt (by omega : 0 < r), Nat.cast_zero]
    unfold Cert.binom
    rw [if_neg (by omega)]
  · rw [show (n : ℤ) - r + 1 = ((n + 1 - r : ℕ) : ℤ) by omega, Cert.binom_natCast]

/-- The row family `path(r)` holds for every forest (Lemma 2.2 (6) through (3)). -/
theorem path_row_holds (hG : G.IsAcyclic) {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (r : ℕ) :
    ((Cert.Label.path r).row (Fintype.card V) G.indepNum).Holds (Fintype.card V) G.indepNum
      (tArr G I) := by
  unfold Cert.Row.Holds Cert.Label.row
  simp only [neg_mul, Finset.sum_neg_distrib]
  have h1 := card_indepSetFinset_eq hI hmax r
  have h2 : (((Fintype.card V + 1 - r).choose r : ℕ) : ℚ) ≤ (G.indepSetFinset r).card := by
    exact_mod_cast choose_le_card_indepSetFinset hG r
  rw [binom_path]
  linarith

end Bridge

/-! ### The reduction (34) -/

/-- **The reduction (34).**  If a sequence never recovers below `K` (`c_{k+1} ≤ c_k` implies
`c_{k+2} ≤ c_{k+1}` for `k + 1 < K`) and is nonincreasing from `K` on, it is unimodal. -/
theorem unimodal_of_noRecovery {c : ℕ → ℕ} {K : ℕ}
    (hrec : ∀ k, k + 1 < K → c (k + 1) ≤ c k → c (k + 2) ≤ c (k + 1))
    (htail : ∀ k, K ≤ k → c (k + 1) ≤ c k) : Unimodal c := by
  classical
  have hex : ∃ i, c (i + 1) ≤ c i := ⟨K, htail K le_rfl⟩
  have hmspec : c (Nat.find hex + 1) ≤ c (Nat.find hex) := Nat.find_spec hex
  have hbefore : ∀ i, i < Nat.find hex → c i ≤ c (i + 1) := by
    intro i hi
    have := Nat.find_min hex hi
    omega
  have hafter : ∀ i, Nat.find hex ≤ i → c (i + 1) ≤ c i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact hmspec
    | succ i hmi ih =>
      by_cases hK : K ≤ i + 1
      · exact htail _ hK
      · exact hrec i (by omega) ih
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro i j hij hjm
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (ih (by omega)) (hbefore j (by omega))
  · intro i j hmi hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (hafter j (by omega)) ih

/-! ### Row soundness and the finite theorem -/

/-- **Row soundness** (the named hypothesis; Zhang's Lemmas 2.3–2.10 with the choice of
Lemma 2.5): every forest with an edge has a maximum independent set whose count array satisfies
every row family of Section 2.9 on its domain.  (`count` and `path` hold for every maximum
independent set: `count_row_holds`, `path_row_holds`.) -/
def RowsSound : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsAcyclic → 0 < matchingNumber G →
      ∃ I : Finset V, IsIndepFinset G I ∧ I.card = G.indepNum ∧
        ∀ ρ : Cert.Label, ρ.InDomain (Fintype.card V) G.indepNum →
          (ρ.row (Fintype.card V) G.indepNum).Holds (Fintype.card V) G.indepNum (tArr G I)

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A forest without edges (`ν = 0`) has `c_r = C(n, r)`, a unimodal sequence. -/
theorem unimodal_of_matchingNumber_eq_zero (hG : G.IsAcyclic) (hν : matchingNumber G = 0) :
    Unimodal (fun k => (G.indepSetFinset k).card) := by
  have ha : G.indepNum = Fintype.card V := by
    have := indepNum_add_matchingNumber hG
    omega
  obtain ⟨I, hIn⟩ := G.exists_isNIndepSet_indepNum
  have hIi : IsIndepFinset G I :=
    fun v hv w hw hadj => hIn.isIndepSet hv hw (G.ne_of_adj hadj) hadj
  have hvars : Cert.vars (Fintype.card V) G.indepNum = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Cert.mem_vars, Finset.mem_Icc] at hp
    unfold Cert.v at hp
    omega
  have hc : (fun k => (G.indepSetFinset k).card) = bRow (Fintype.card V) 0 := by
    funext k
    have h := card_indepSetFinset_eq hIi hIn.card_eq k
    rw [hvars, Finset.sum_empty, add_zero, Cert.binom_natCast, ha] at h
    have hb : bRow (Fintype.card V) 0 k = (Fintype.card V).choose k := by
      unfold bRow
      rw [pow_zero, one_mul, Nat.mul_zero, Nat.sub_zero, Polynomial.coeff_one_add_X_pow,
        Nat.cast_id]
    rw [hb]
    exact_mod_cast h
  rw [hc]
  obtain ⟨hbLC, hbPos⟩ := Ceiling.bRow_good (Fintype.card V) 0
  exact unimodal_of_logConcave hbLC hbPos.noInternalZeros hbPos.finitelySupported

/-- **Zhang's Theorem 2.1, reduced** (general finite vertex type): a forest with at most 60
vertices is unimodal, given the certificate layer's no-recovery claims on `P60` and row soundness
for this forest. -/
theorem unimodal_of_sound (hG : G.IsAcyclic) (hn : Fintype.card V ≤ 60)
    (hcert : Cert.CertificatesSound)
    (hrows : 0 < matchingNumber G → ∃ I : Finset V, IsIndepFinset G I ∧ I.card = G.indepNum ∧
      ∀ ρ : Cert.Label, ρ.InDomain (Fintype.card V) G.indepNum →
        (ρ.row (Fintype.card V) G.indepNum).Holds (Fintype.card V) G.indepNum (tArr G I)) :
    Unimodal (fun k => (G.indepSetFinset k).card) := by
  rcases Nat.eq_zero_or_pos (matchingNumber G) with hν | hν
  · exact unimodal_of_matchingNumber_eq_zero hG hν
  obtain ⟨I, hIi, hIc, hrowsI⟩ := hrows hν
  have hfeas : Cert.Feasible (Fintype.card V) G.indepNum (tArr G I) :=
    { toBasic := basic_tArr hIi hIc, rows := hrowsI }
  have hk := indepNum_add_matchingNumber hG
  have hle := matchingNumber_le_indepNum hG
  have h2a := SmallAlpha.card_le_two_mul_indepNum hG
  apply unimodal_of_noRecovery (K := (2 * G.indepNum + 1) / 3)
  · intro k hkK hdown
    have hP : Cert.InP60 (Fintype.card V) G.indepNum (k + 1) := by
      unfold Cert.InP60
      omega
    have h1 := delta_eq hIi hIc k
    have h2 := delta_eq hIi hIc (k + 1)
    have hd1 : Cert.delta (Fintype.card V) G.indepNum (tArr G I) (k + 1) ≤ 0 := by
      rw [← h1]
      have : ((G.indepSetFinset (k + 1)).card : ℚ) ≤ (G.indepSetFinset k).card := by
        exact_mod_cast hdown
      linarith
    have hd2 := hcert _ _ _ hP (tArr G I) hfeas hd1
    rw [← h2] at hd2
    have : ((G.indepSetFinset (k + 1 + 1)).card : ℚ) ≤ (G.indepSetFinset (k + 1)).card := by
      linarith
    exact_mod_cast this
  · intro k hk
    exact SmallAlpha.card_indepSetFinset_succ_le hG (by omega)

end Main

/-- **Zhang's Theorem 2.1 (every forest with at most 60 vertices is unimodal), reduced to its two
inputs**: row soundness (Lemmas 2.3–2.10 with the choice of Lemma 2.5) and the certificate
layer's no-recovery claims on the 17,100 triples of `P60` (Table 1). -/
theorem finite60_of_sound (hrows : RowsSound) (hcert : Cert.CertificatesSound)
    (F : FiniteForest) (hn : F.n ≤ 60) : independenceSequenceUnimodal F := by
  classical
  have h := unimodal_of_sound (G := F.graph) F.isForest (by rw [Fintype.card_fin]; exact hn)
    hcert (fun hν => hrows (Fin F.n) F.graph F.isForest hν)
  unfold independenceSequenceUnimodal
  apply unimodalUpTo_of_unimodal
  convert h using 2

end Zhang
end Erdos993Lean
