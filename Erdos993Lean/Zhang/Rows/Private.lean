import Mathlib
import Erdos993Lean.Zhang.Rows.Layers

/-!
# Zhang's finite part, row soundness 7: private neighbours (Lemma 2.3)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemma 2.3 and (10), (13).  For an independent `J ⊆ Y` with `|J| = r`,
`m = m(J)`, `d = a − m`, and `u ∈ J`, the private neighbours `priv G I J u` of `u` are the
vertices of `I` available for `J − u` but not for `J`; `p_u` is their number.

* `card_avail_erase`: `m(J − u) = m + p_u`; `disjoint_priv`, `sum_card_priv_le`: `Σ_u p_u ≤ d`.
* `card_sdiff_avail_le_sum_priv`: `Σ_u p_u ≥ d − r + 1` (in the forest on `J ∪ N_I(J)` the
  `Σ_{i ∈ N_I(J)} |N_J(i)|` edges number at most `r + d − 1`, while a covered vertex has one
  neighbour in `J` when it is private and at least two otherwise).
* `sum_card_avail_erase_ge`, `sum_card_avail_erase_le`, `card_avail_erase_add_le` (`p_u ≤ L`).
* `priv_row_holds`: **row family `private(r, h)`**, for every maximum independent set.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Private neighbours (Lemma 2.3) -/

omit [Fintype V] [DecidableEq V] in
theorem avail_anti {I J J' : Finset V} (h : J ⊆ J') : avail G I J' ⊆ avail G I J := by
  intro i hi
  rw [mem_avail] at hi ⊢
  exact ⟨hi.1, fun y hy => hi.2 y (h hy)⟩

variable (G) in
/-- The private neighbours of `u` in `I` relative to `J`: available for `J − u`, not for `J`. -/
def priv (I J : Finset V) (u : V) : Finset V := avail G I (J.erase u) \ avail G I J

omit [Fintype V] in
/-- `m(J − u) = m(J) + p_u`. -/
theorem card_avail_erase (I J : Finset V) (u : V) :
    (avail G I (J.erase u)).card = (avail G I J).card + (priv G I J u).card := by
  unfold priv
  rw [← card_union_of_disjoint disjoint_sdiff,
    union_sdiff_of_subset (avail_anti (erase_subset u J))]

omit [Fintype V] in
theorem disjoint_priv {I J : Finset V} {u u' : V} (hne : u ≠ u') :
    Disjoint (priv G I J u) (priv G I J u') := by
  rw [disjoint_left]
  intro i hi hi'
  unfold priv at hi hi'
  obtain ⟨hi1, hi2⟩ := mem_sdiff.mp hi
  obtain ⟨hi1', -⟩ := mem_sdiff.mp hi'
  rw [mem_avail] at hi1 hi1' hi2
  push_neg at hi2
  obtain ⟨y, hy, hyi⟩ := hi2 hi1.1
  have h1 : y = u := by
    by_contra h
    exact hi1.2 y (mem_erase.mpr ⟨h, hy⟩) hyi
  have h2 : y = u' := by
    by_contra h
    exact hi1'.2 y (mem_erase.mpr ⟨h, hy⟩) hyi
  exact hne (h1.symm.trans h2)

omit [Fintype V] in
theorem sum_card_priv (I J : Finset V) :
    ∑ u ∈ J, (priv G I J u).card = (J.biUnion (priv G I J)).card := by
  rw [card_biUnion]
  intro u _ u' _ hne
  exact disjoint_priv hne

omit [Fintype V] in
/-- Private neighbours are distinct covered vertices: `Σ_u p_u ≤ d = |I| − m(J)`. -/
theorem sum_card_priv_le (I J : Finset V) :
    ∑ u ∈ J, (priv G I J u).card ≤ (I \ avail G I J).card := by
  rw [sum_card_priv]
  apply card_le_card
  intro i hi
  obtain ⟨u, _, hiu⟩ := mem_biUnion.mp hi
  unfold priv at hiu
  obtain ⟨hi1, hi2⟩ := mem_sdiff.mp hiu
  exact mem_sdiff.mpr ⟨(mem_avail.mp hi1).1, hi2⟩

omit [Fintype V] in
/-- **Zhang (13), the release lower bound** `Σ_u p_u ≥ d − r + 1`: in the forest on `J ∪ N_I(J)`
(`d = |N_I(J)|`), the edges number `Σ_{i ∈ N_I(J)} |N_J(i)| ≤ r + d − 1`, while each covered vertex
has one neighbour in `J` if it is private and at least two otherwise. -/
theorem card_sdiff_avail_le_sum_priv (hG : G.IsAcyclic) {I J : Finset V}
    (hI : IsIndepFinset G I) (hJI : Disjoint J I) (hJi : IsIndepFinset G J)
    (hJne : J.Nonempty) :
    (I \ avail G I J).card + 1 ≤ ∑ u ∈ J, (priv G I J u).card + J.card := by
  set D := I \ avail G I J with hD
  set I1 := D.filter (fun i => (nbrsIn G J i).card = 1) with hI1
  have hDpos : ∀ i ∈ D, 1 ≤ (nbrsIn G J i).card := by
    intro i hi
    obtain ⟨hiI, hiA⟩ := mem_sdiff.mp hi
    rw [mem_avail] at hiA
    push_neg at hiA
    obtain ⟨y, hy, hyi⟩ := hiA hiI
    exact card_pos.mpr ⟨y, mem_nbrsIn.mpr ⟨hy, hyi.symm⟩⟩
  have hDI : D ⊆ I := sdiff_subset
  have hJD : Disjoint J D := disjoint_of_subset_right hDI hJI
  have hsum_le : ∑ i ∈ D, (nbrsIn G J i).card + 1 ≤ J.card + D.card := by
    have h1 := eIn_union_indep (G := G) hJD (isIndepFinset_mono hI hDI)
    rw [eIn_eq_zero_of_indep hJi, zero_add] at h1
    have h2 := eIn_lt_card hG (hJne.mono subset_union_left : (J ∪ D).Nonempty)
    rw [card_union_of_disjoint hJD] at h2
    omega
  have hsum_ge : 2 * D.card ≤ ∑ i ∈ D, (nbrsIn G J i).card + I1.card := by
    have h2D : 2 * D.card = ∑ _i ∈ D, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    rw [h2D, hI1, card_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    have := hDpos i hi
    split_ifs with h <;> omega
  have hsub : I1 ⊆ J.biUnion (priv G I J) := by
    intro i hi
    obtain ⟨hiD, hi1⟩ := mem_filter.mp hi
    obtain ⟨u, hu⟩ := card_eq_one.mp hi1
    have huN : u ∈ nbrsIn G J i := by
      rw [hu]
      exact mem_singleton_self u
    obtain ⟨huJ, hiu⟩ := mem_nbrsIn.mp huN
    rw [mem_biUnion]
    refine ⟨u, huJ, ?_⟩
    unfold priv
    refine mem_sdiff.mpr ⟨mem_avail.mpr ⟨(mem_sdiff.mp hiD).1, ?_⟩, (mem_sdiff.mp hiD).2⟩
    intro y hy hyi
    have : y ∈ nbrsIn G J i := mem_nbrsIn.mpr ⟨mem_of_mem_erase hy, hyi.symm⟩
    rw [hu, mem_singleton] at this
    exact (mem_erase.mp hy).1 this
  have h3 := card_le_card hsub
  rw [← sum_card_priv] at h3
  omega

theorem disjoint_of_subset_sdiff {I J : Finset V} (hJ : J ⊆ univ \ I) : Disjoint J I := by
  rw [disjoint_left]
  intro y hy hyI
  exact (mem_sdiff.mp (hJ hy)).2 hyI

/-- `Σ_{u ∈ J} m(J − u) ≥ r m + (a − m) − r + 1` (Zhang (10), (13)). -/
theorem sum_card_avail_erase_ge (hG : G.IsAcyclic) {I J : Finset V} (hI : IsIndepFinset G I)
    (hJ : J ⊆ univ \ I) (hJi : IsIndepFinset G J) (hJne : J.Nonempty) :
    J.card * (avail G I J).card + (I.card - (avail G I J).card) + 1 ≤
      ∑ u ∈ J, (avail G I (J.erase u)).card + J.card := by
  have h1 := card_sdiff_avail_le_sum_priv hG hI (disjoint_of_subset_sdiff hJ) hJi hJne
  rw [card_sdiff_of_subset (avail_subset G I J)] at h1
  have h2 : ∑ u ∈ J, (avail G I (J.erase u)).card =
      J.card * (avail G I J).card + ∑ u ∈ J, (priv G I J u).card := by
    rw [sum_congr rfl (fun u _ => card_avail_erase I J u), sum_add_distrib, sum_const,
      smul_eq_mul]
  omega

omit [Fintype V] in
/-- `Σ_{u ∈ J} m(J − u) ≤ r m + (a − m)`. -/
theorem sum_card_avail_erase_le (I J : Finset V) :
    ∑ u ∈ J, (avail G I (J.erase u)).card ≤
      J.card * (avail G I J).card + (I.card - (avail G I J).card) := by
  have h1 := sum_card_priv_le (G := G) I J
  rw [card_sdiff_of_subset (avail_subset G I J)] at h1
  rw [sum_congr rfl (fun u _ => card_avail_erase I J u), sum_add_distrib, sum_const, smul_eq_mul]
  omega

/-- `m(J − u) + (r − 1) ≤ a`, i.e. `p_u ≤ L`. -/
theorem card_avail_erase_add_le {I J : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (hJ : J ⊆ univ \ I) (hJi : IsIndepFinset G J) {u : V}
    (hu : u ∈ J) : (avail G I (J.erase u)).card + (J.card - 1) ≤ I.card := by
  have h := card_add_card_avail_le hI hmax ((erase_subset u J).trans hJ)
    (isIndepFinset_mono hJi (erase_subset u J))
  rw [card_erase_of_mem hu] at h
  omega

theorem pos_nonneg (x : ℤ) : 0 ≤ Cert.pos x := by
  unfold Cert.pos
  exact_mod_cast le_max_right x 0

/-- Per independent `J` (Lemma 2.3): `((r−1)m + a − r + 1 − rh)_+ ≤ Σ_{u ∈ J} (m(J − u) − h)_+`. -/
theorem priv_aux (hG : G.IsAcyclic) {I J : Finset V} (hI : IsIndepFinset G I)
    (hJ : J ⊆ univ \ I) (hJi : IsIndepFinset G J) (hJne : J.Nonempty) (h : ℕ) :
    Cert.pos (((J.card : ℤ) - 1) * (avail G I J).card + I.card - J.card + 1 - J.card * h) ≤
      ∑ u ∈ J, Cert.pos (((avail G I (J.erase u)).card : ℤ) - h) := by
  have hL := sum_card_avail_erase_ge hG hI hJ hJi hJne
  have hm : (avail G I J).card ≤ I.card := card_le_card (avail_subset G I J)
  have hL' : ((J.card * (avail G I J).card + (I.card - (avail G I J).card) + 1 : ℕ) : ℤ) ≤
      ((∑ u ∈ J, (avail G I (J.erase u)).card + J.card : ℕ) : ℤ) := Nat.cast_le.mpr hL
  push_cast [Nat.cast_sub hm] at hL'
  have key : max (((J.card : ℤ) - 1) * (avail G I J).card + I.card - J.card + 1 - J.card * h) 0 ≤
      ∑ u ∈ J, max (((avail G I (J.erase u)).card : ℤ) - h) 0 := by
    apply max_le
    · calc ((J.card : ℤ) - 1) * (avail G I J).card + I.card - J.card + 1 - J.card * h
          ≤ ∑ u ∈ J, (((avail G I (J.erase u)).card : ℤ) - h) := by
            rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
            linarith
        _ ≤ _ := sum_le_sum (fun u _ => le_max_left _ _)
    · exact sum_nonneg (fun u _ => le_max_right _ _)
  unfold Cert.pos
  push_cast
  exact_mod_cast key

/-- **Row family `private(r, h)`** (Zhang, Lemma 2.3). -/
theorem priv_row_holds (hG : G.IsAcyclic) {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) {r h : ℕ}
    (hr : (Cert.Label.priv r h).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.priv r h).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv, -⟩ := hr
  have hY := card_univ_sdiff_eq (G := G) hmax
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  have hr1I : r - 1 ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨by omega, by omega⟩
  unfold Cert.Row.Holds
  rw [sum_vars_two hrI hr1I
    (fun m => Cert.pos (((r : ℤ) - 1) * m + G.indepNum - r + 1 - r * h))
    (fun m => ((Cert.v (Fintype.card V) G.indepNum : ℚ) - r + 1) * Cert.pos ((m : ℤ) - h))
    ((Cert.Label.priv r h).row (Fintype.card V) G.indepNum).coef (tArr G I) (fun j m => rfl)]
  simp only [Cert.Label.row]
  rw [sum_tArr_eq hI hmax r (fun m => Cert.pos (((r : ℤ) - 1) * m + G.indepNum - r + 1 - r * h)),
    sum_tArr_eq hI hmax (r - 1)
      (fun m => ((Cert.v (Fintype.card V) G.indepNum : ℚ) - r + 1) * Cert.pos ((m : ℤ) - h)),
    ← mul_sum, sub_nonpos]
  have hper : ∀ J ∈ indepSets G (univ \ I) r,
      Cert.pos (((r : ℤ) - 1) * (avail G I J).card + G.indepNum - r + 1 - r * h) ≤
        ∑ u ∈ J, Cert.pos (((avail G I (J.erase u)).card : ℤ) - h) := by
    intro J hJ
    obtain ⟨hJY, hJc, hJi⟩ := mem_indepSets.mp hJ
    have hJne : J.Nonempty := by
      rw [← card_pos, hJc]
      omega
    have := priv_aux hG hI hJY hJi hJne h
    rw [hJc, hmax] at this
    exact this
  have hdc := sum_sum_erase_le (G := G) (univ \ I) (r - 1)
    (fun K => Cert.pos (((avail G I K).card : ℤ) - h)) (fun K _ => pos_nonneg _)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r), hY] at hdc
  calc ∑ J ∈ indepSets G (univ \ I) r,
        Cert.pos (((r : ℤ) - 1) * (avail G I J).card + G.indepNum - r + 1 - r * h)
      ≤ ∑ J ∈ indepSets G (univ \ I) r,
          ∑ u ∈ J, Cert.pos (((avail G I (J.erase u)).card : ℤ) - h) := sum_le_sum hper
    _ ≤ _ := hdc
    _ = _ := by
        rw [Nat.cast_sub (by omega : 1 ≤ r)]
        push_cast
        ring

end Forest

end Rows
end Zhang
end Erdos993Lean
