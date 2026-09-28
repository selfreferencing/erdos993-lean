import Mathlib
import Erdos993Lean.Zhang.Rows.Layers

/-!
# Zhang's finite part, row soundness 6: the mean bound with the actual edge count (Lemma 2.9)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemma 2.9: `M_r ≥ C_r^0 + β_r e` with `e = e(F[Y]) = C(v, 2) − T_2`.

* `choose_secant`: `C(v−2, r) + (2 − d) C(v−2, r−1) ≤ C(v − d, r)` (the secant through `d = 1, 2`
  of the discretely convex `d ↦ C(v − d, r)`).
* `sum_card_avail_powersetCard`: `Σ_{S ⊆ Y, |S| = r} m(S) = Σ_{i ∈ I} C(v − d_i, r)`.
* `card_avail_add_two_le`: a non-independent `S ⊆ Y` has `m(S) ≤ a − 2` (the endpoints of an
  edge of `F[Y]` have nonempty, disjoint neighbourhoods in `I`: maximality, no triangles).
* `mean_row_holds`: **row family `mean(r)`**, for every maximum independent set; the edge count
  `Σ_i d_i = e(F) − e(F[Y]) ≤ n − 1 − e` uses `eIn_union_indep` and the forest edge bound.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The mean bound (Lemma 2.9) -/

theorem choose_secant_aux (v r : ℕ) (hr : 1 ≤ r) (k : ℕ) :
    ((v - 2).choose r : ℤ) - k * ((v - 2).choose (r - 1) : ℤ) ≤ ((v - 2 - k).choose r : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step : ((v - 2 - k).choose r : ℤ) - ((v - 2).choose (r - 1) : ℤ) ≤
        ((v - 2 - (k + 1)).choose r : ℤ) := by
      rcases Nat.eq_zero_or_pos (v - 2 - k) with h0 | hpos
      · rw [h0, show v - 2 - (k + 1) = 0 by omega, Nat.choose_eq_zero_of_lt (by omega : 0 < r)]
        have : (0 : ℤ) ≤ ((v - 2).choose (r - 1) : ℤ) := Nat.cast_nonneg _
        push_cast
        linarith
      · have hN : v - 2 - (k + 1) + 1 = v - 2 - k := by omega
        have hp := Nat.choose_succ_succ' (v - 2 - (k + 1)) (r - 1)
        rw [hN, show r - 1 + 1 = r by omega] at hp
        have hm : (v - 2 - (k + 1)).choose (r - 1) ≤ (v - 2).choose (r - 1) :=
          Nat.choose_le_choose _ (by omega)
        have hp' : ((v - 2 - k).choose r : ℤ) = ((v - 2 - (k + 1)).choose (r - 1) : ℤ) +
            ((v - 2 - (k + 1)).choose r : ℤ) := by exact_mod_cast hp
        have hm' : ((v - 2 - (k + 1)).choose (r - 1) : ℤ) ≤ ((v - 2).choose (r - 1) : ℤ) := by
          exact_mod_cast hm
        linarith
    push_cast
    linarith

/-- **Secant bound** (Zhang, proof of Lemma 2.9): `d ↦ C(v − d, r)` lies above the line through its
values at `d = 1, 2`: `C(v−2, r) + (2 − d) C(v−2, r−1) ≤ C(v−d, r)`. -/
theorem choose_secant (v r d : ℕ) (hv : 2 ≤ v) (hr : 1 ≤ r) :
    ((v - 2).choose r : ℤ) + (2 - (d : ℤ)) * ((v - 2).choose (r - 1) : ℤ) ≤
      ((v - d).choose r : ℤ) := by
  have hp1 := Nat.choose_succ_succ' (v - 2) (r - 1)
  rw [show v - 2 + 1 = v - 1 by omega, show r - 1 + 1 = r by omega] at hp1
  have hp1' : ((v - 1).choose r : ℤ) = ((v - 2).choose (r - 1) : ℤ) + ((v - 2).choose r : ℤ) := by
    exact_mod_cast hp1
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · have hp0 := Nat.choose_succ_succ' (v - 1) (r - 1)
      rw [show v - 1 + 1 = v by omega, show r - 1 + 1 = r by omega] at hp0
      have hm : (v - 2).choose (r - 1) ≤ (v - 1).choose (r - 1) :=
        Nat.choose_le_choose _ (by omega)
      have hp0' : ((v).choose r : ℤ) = ((v - 1).choose (r - 1) : ℤ) + ((v - 1).choose r : ℤ) := by
        exact_mod_cast hp0
      have hm' : ((v - 2).choose (r - 1) : ℤ) ≤ ((v - 1).choose (r - 1) : ℤ) := by
        exact_mod_cast hm
      simp only [Nat.sub_zero, Nat.cast_zero]
      linarith
    · simp only [Nat.cast_one]
      linarith
  · have h := choose_secant_aux v r hr (d - 2)
    rw [show v - 2 - (d - 2) = v - d by omega] at h
    push_cast [Nat.cast_sub hd] at h
    linarith

omit [Fintype V] [DecidableEq V] in
/-- `Σ_{S ⊆ Y, |S| = r} m(S) = Σ_{i ∈ I} C(|Y| − d_i, r)`, `d_i = |N(i) ∩ Y|` (pairs of an `r`-subset
and an available vertex, counted from the vertex). -/
theorem sum_card_avail_powersetCard (I Y : Finset V) (r : ℕ) :
    ∑ J ∈ Y.powersetCard r, (avail G I J).card =
      ∑ i ∈ I, (Y.card - (nbrsIn G Y i).card).choose r := by
  have h1 : ∀ J ∈ Y.powersetCard r, (avail G I J).card =
      ∑ i ∈ I, if (∀ y ∈ J, ¬ G.Adj y i) then 1 else 0 := by
    intro J _
    rw [avail, card_filter]
  rw [sum_congr rfl h1, sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← card_filter]
  have h2 : (Y.powersetCard r).filter (fun J => ∀ y ∈ J, ¬ G.Adj y i) =
      (Y.filter (fun y => ¬ G.Adj i y)).powersetCard r := by
    ext J
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hJY, hJc⟩, hJ⟩
      exact ⟨fun y hy => mem_filter.mpr ⟨hJY hy, fun h => hJ y hy h.symm⟩, hJc⟩
    · rintro ⟨hJ, hJc⟩
      exact ⟨⟨fun y hy => (mem_filter.mp (hJ hy)).1, hJc⟩,
        fun y hy h => (mem_filter.mp (hJ hy)).2 h.symm⟩
  rw [h2, card_powersetCard]
  congr 1
  have h3 := card_filter_add_card_filter_not (s := Y) (fun y => G.Adj i y)
  have h4 : nbrsIn G Y i = Y.filter (fun y => G.Adj i y) := rfl
  rw [h4]
  exact (Nat.sub_eq_of_eq_add' h3.symm).symm

/-- A non-independent `J ⊆ Y` covers at least two vertices of `I`: it contains an edge `yz`, and
`N_I(y)`, `N_I(z)` are nonempty (maximality of `I`) and disjoint (no triangles). -/
theorem card_avail_add_two_le (hG : G.IsAcyclic) {I J : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (hJ : J ⊆ univ \ I) (hJn : ¬ IsIndepFinset G J) :
    (avail G I J).card + 2 ≤ I.card := by
  have : ∃ y ∈ J, ∃ z ∈ J, G.Adj y z := by
    by_contra hcon
    push_neg at hcon
    exact hJn (fun a ha b hb => hcon a ha b hb)
  obtain ⟨y, hy, z, hz, hyz⟩ := this
  have hyI : y ∉ I := (mem_sdiff.mp (hJ hy)).2
  have hzI : z ∉ I := (mem_sdiff.mp (hJ hz)).2
  obtain ⟨i1, hi1, hyi1⟩ := exists_adj_of_notMem hI hmax hyI
  obtain ⟨i2, hi2, hzi2⟩ := exists_adj_of_notMem hI hmax hzI
  have hne : i1 ≠ i2 := by
    intro h
    rw [← h] at hzi2
    exact not_adj_of_adj_adj hG hyi1.symm hzi2.symm hyz
  have hsub : avail G I J ⊆ (I.erase i1).erase i2 := by
    intro i hi
    obtain ⟨hiI, hiJ⟩ := mem_avail.mp hi
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hiI⟩⟩
    · intro h
      rw [h] at hiJ
      exact hiJ z hz hzi2
    · intro h
      rw [h] at hiJ
      exact hiJ y hy hyi1
  have h1 := card_le_card hsub
  have h2 : 2 ≤ I.card := by
    have := card_le_card (show ({i1, i2} : Finset V) ⊆ I from
      insert_subset hi1 (singleton_subset_iff.mpr hi2))
    rwa [card_pair hne] at this
  rw [card_erase_of_mem (mem_erase.mpr ⟨hne.symm, hi2⟩), card_erase_of_mem hi1] at h1
  omega

/-- **Row family `mean(r)`** (Zhang, Lemma 2.9, with the actual edge count `e = C(v,2) − T_2`). -/
theorem mean_row_holds (hG : G.IsAcyclic) {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) {r : ℕ}
    (hr : (Cert.Label.mean r).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.mean r).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv⟩ := hr
  have hY := card_univ_sdiff_eq (G := G) hmax
  have hn2a := SmallAlpha.card_le_two_mul_indepNum hG
  have han : G.indepNum ≤ Fintype.card V := by
    rw [← hmax]
    exact card_le_univ I
  have hva : Cert.v (Fintype.card V) G.indepNum ≤ G.indepNum := by
    unfold Cert.v
    omega
  have h2 : (2 : ℕ) ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨by norm_num, by omega⟩
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  unfold Cert.Row.Holds
  rw [sum_vars_two hrI h2 (fun m => -(m : ℚ)) (fun _ => Cert.β (Fintype.card V) G.indepNum r)
    _ _ (fun j m => by simp only [Cert.Label.row]; split_ifs <;> ring)]
  simp only [Cert.Label.row]
  rw [← mul_sum, sum_tArr_one hI hmax, sum_tArr_eq hI hmax r (fun m => -(m : ℚ)),
    sum_neg_distrib]
  have hb1 : Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) - 2) ((r : ℤ) - 1) =
      ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 1) : ℚ) :=
    binom_eq (by omega) (by omega)
  have hb2 : Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) - 2) ((r : ℤ) - 2) =
      ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 2) : ℚ) :=
    binom_eq (by omega) (by omega)
  have hb3 : Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) - 2) (r : ℤ) =
      ((Cert.v (Fintype.card V) G.indepNum - 2).choose r : ℚ) := binom_eq (by omega) rfl
  have hb4 : Cert.binom (Cert.v (Fintype.card V) G.indepNum : ℤ) 2 =
      ((Cert.v (Fintype.card V) G.indepNum).choose 2 : ℚ) := binom_eq rfl (by norm_num)
  have hδ : ((Cert.δ (Fintype.card V) G.indepNum : ℕ) : ℚ) =
      2 * (G.indepNum : ℚ) - Fintype.card V := by
    unfold Cert.δ Cert.v
    rw [Nat.cast_sub (by omega), Nat.cast_sub han]
    ring
  simp only [Cert.β, Cert.C0, hb1, hb2, hb3, hb4, hδ]
  -- the combinatorial facts
  have hsplit : ∑ J ∈ (univ \ I).powersetCard r, ((avail G I J).card : ℚ) =
      ∑ J ∈ indepSets G (univ \ I) r, ((avail G I J).card : ℚ) +
      ∑ J ∈ (univ \ I).powersetCard r with ¬ IsIndepFinset G J, ((avail G I J).card : ℚ) := by
    unfold indepSets
    rw [sum_filter_add_sum_filter_not]
  have hall : ∑ J ∈ (univ \ I).powersetCard r, ((avail G I J).card : ℚ) =
      ∑ i ∈ I, ((Cert.v (Fintype.card V) G.indepNum - (nbrsIn G (univ \ I) i).card).choose r
        : ℚ) := by
    rw [← hY]
    exact_mod_cast sum_card_avail_powersetCard (G := G) I (univ \ I) r
  have hsec : ∀ i ∈ I, ((Cert.v (Fintype.card V) G.indepNum - 2).choose r : ℚ) +
      (2 - ((nbrsIn G (univ \ I) i).card : ℚ)) *
        ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 1) : ℚ) ≤
      ((Cert.v (Fintype.card V) G.indepNum - (nbrsIn G (univ \ I) i).card).choose r : ℚ) := by
    intro i _
    exact_mod_cast choose_secant (Cert.v (Fintype.card V) G.indepNum) r _ (by omega) (by omega)
  have hsum_sec : ∑ i ∈ I, (((Cert.v (Fintype.card V) G.indepNum - 2).choose r : ℚ) +
      (2 - ((nbrsIn G (univ \ I) i).card : ℚ)) *
        ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 1) : ℚ)) =
      (I.card : ℚ) * ((Cert.v (Fintype.card V) G.indepNum - 2).choose r : ℚ) +
      (2 * (I.card : ℚ) - ∑ i ∈ I, ((nbrsIn G (univ \ I) i).card : ℚ)) *
        ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 1) : ℚ) := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_mul, sum_sub_distrib, sum_const,
      nsmul_eq_mul]
    ring
  have hA := sum_le_sum hsec
  rw [hsum_sec, ← hall, hsplit] at hA
  have hedges : ∑ i ∈ I, (nbrsIn G (univ \ I) i).card + eIn G (univ \ I) + 1 ≤
      Fintype.card V := by
    have h := eIn_union_indep (G := G) (A := univ \ I) (B := I) sdiff_disjoint hI
    rw [sdiff_union_of_subset (subset_univ I)] at h
    have hVne : Nonempty V := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have : Fintype.card V = 0 := Fintype.card_eq_zero
      unfold Cert.v at hrv
      omega
    have h' := eIn_lt_card hG (univ_nonempty (α := V))
    rw [card_univ] at h'
    omega
  have hedges' : ∑ i ∈ I, ((nbrsIn G (univ \ I) i).card : ℚ) + (eIn G (univ \ I) : ℚ) + 1 ≤
      (Fintype.card V : ℚ) := by exact_mod_cast hedges
  have hNI : ∑ J ∈ (univ \ I).powersetCard r with ¬ IsIndepFinset G J,
      ((avail G I J).card : ℚ) ≤
      ((G.indepNum : ℚ) - 2) *
        (((univ \ I).powersetCard r).filter (fun J => ¬ IsIndepFinset G J)).card := by
    rw [← nsmul_eq_mul', ← sum_const]
    apply sum_le_sum
    intro J hJ
    obtain ⟨hJp, hJn⟩ := mem_filter.mp hJ
    have := card_avail_add_two_le hG hI hmax (mem_powersetCard.mp hJp).1 hJn
    rw [hmax] at this
    have : ((avail G I J).card : ℚ) + 2 ≤ G.indepNum := by exact_mod_cast this
    linarith
  have hNc := card_nonindep_le (G := G) (univ \ I) r
  rw [hY] at hNc
  have hNc' : ((((univ \ I).powersetCard r).filter (fun J => ¬ IsIndepFinset G J)).card : ℚ) ≤
      (eIn G (univ \ I) : ℚ) * ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 2) : ℚ) := by
    exact_mod_cast hNc
  have hT2 := indepCount_two_add_eIn (G := G) (univ \ I)
  rw [hY] at hT2
  have hT2' : (indepCount G (univ \ I) 2 : ℚ) =
      ((Cert.v (Fintype.card V) G.indepNum).choose 2 : ℚ) - (eIn G (univ \ I) : ℚ) := by
    have : (indepCount G (univ \ I) 2 : ℚ) + (eIn G (univ \ I) : ℚ) =
        ((Cert.v (Fintype.card V) G.indepNum).choose 2 : ℚ) := by exact_mod_cast hT2
    linarith
  rw [hT2']
  have ha2 : (2 : ℚ) ≤ G.indepNum := by exact_mod_cast (show 2 ≤ G.indepNum by omega)
  have hC1 : (0 : ℚ) ≤ ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 1) : ℚ) :=
    Nat.cast_nonneg _
  have hP1 := mul_le_mul_of_nonneg_left hNc' (sub_nonneg.mpr ha2)
  have hP2 := mul_nonneg (sub_nonneg.mpr hedges') hC1
  rw [hmax] at hA
  nlinarith

end Forest

end Rows
end Zhang
end Erdos993Lean
