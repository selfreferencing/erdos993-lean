import Mathlib
import Erdos993Lean.Zhang.Rows.Layers

/-!
# Zhang's finite part, row soundness 9: matching-based extensions (Lemma 2.4)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemma 2.4: `(r + 1) H_{r+1,l} ≤ (v − r − max(0, l − δ)) H_{r,l}`,
`H_{r,l} = Σ_m C(m, l) t_{r,m}`, `H_{0,l} = C(a, l)`.

* `card_le_card_nbrsY`: for `L ⊆ I`, `|N_Y(L)| ≥ |L| − δ` (the paper uses a maximum matching; here:
  on `H = V − L − N_Y(L)`, `α(H) ≤ a − |L|` and `|H| ≤ 2 α(H)`).
* `sum_choose_avail`: `H_{r,l} = Σ_{L ⊆ I, |L| = l} i_r(Y − N(L))`.
* `hall_row_holds`: **row family `hall(r, l)`**, for every maximum independent set (the down-up
  inequality `(r + 1) i_{r+1} ≤ (|Y_L| − r) i_r` for each `L`).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Matching-based extensions (Lemma 2.4) -/

/-- **Deficiency bound** (Zhang, proof of Lemma 2.4): for `L ⊆ I`, `|L| + n ≤ |N_Y(L)| + 2a`,
i.e. `|N_Y(L)| ≥ |L| − δ`.  Proof without matchings: on `H = V − L − N_Y(L)`, every independent
set joins `L` independently, so `α(H) ≤ a − |L|`, while `|H| ≤ 2 α(H)`. -/
theorem card_le_card_nbrsY (hG : G.IsAcyclic) {I L : Finset V} (hI : IsIndepFinset G I)
    (hL : L ⊆ I) :
    L.card + Fintype.card V ≤
      ((univ \ I).filter (fun y => ¬ ∀ i ∈ L, ¬ G.Adj y i)).card + 2 * G.indepNum := by
  set NY := (univ \ I).filter (fun y => ¬ ∀ i ∈ L, ¬ G.Adj y i) with hNY
  set H := univ \ (L ∪ NY) with hH
  obtain ⟨T, hTH, hTi, hTc⟩ := exists_alphaIn G H
  have hdisjLN : Disjoint L NY := by
    rw [disjoint_left]
    intro x hxL hxN
    exact (mem_sdiff.mp (mem_filter.mp hxN).1).2 (hL hxL)
  have hTL : Disjoint T L := by
    rw [disjoint_left]
    intro x hxT hxL
    exact (mem_sdiff.mp (hTH hxT)).2 (mem_union_left _ hxL)
  have cross : ∀ x ∈ T, ∀ y ∈ L, ¬ G.Adj x y := by
    intro x hx y hy hxy
    by_cases hxI : x ∈ I
    · exact hI x hxI y (hL hy) hxy
    · have hxN : x ∈ NY :=
        mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ x, hxI⟩, fun h => h y hy hxy⟩
      exact (mem_sdiff.mp (hTH hx)).2 (mem_union_right _ hxN)
  have hind : IsIndepFinset G (T ∪ L) := by
    intro x hx y hy hxy
    rw [mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hTi x hx y hy hxy
    · exact cross x hx y hy hxy
    · exact cross y hy x hx hxy.symm
    · exact hI x (hL hx) y (hL hy) hxy
  have h1 := le_alphaIn (subset_univ (T ∪ L)) hind
  rw [alphaIn_univ, card_union_of_disjoint hTL, hTc] at h1
  have h2 := card_le_two_mul_alphaIn hG H
  have h3 : H.card + (L ∪ NY).card = Fintype.card V := by
    rw [hH, card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_univ (L ∪ NY)
    omega
  rw [card_union_of_disjoint hdisjLN] at h3
  omega

/-- `H_{r,l} = Σ_J C(m(J), l) = Σ_{L ⊆ I, |L| = l} i_r(Y − N(L))` (pairs of an independent `r`-set
and an `l`-set of its available vertices, counted from the `l`-set). -/
theorem sum_choose_avail (I Y : Finset V) (r l : ℕ) :
    ∑ J ∈ indepSets G Y r, (avail G I J).card.choose l =
      ∑ L ∈ I.powersetCard l, indepCount G (Y.filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) r := by
  have h1 : ∀ J ∈ indepSets G Y r, (avail G I J).card.choose l =
      ∑ L ∈ I.powersetCard l, if L ⊆ avail G I J then 1 else 0 := by
    intro J _
    rw [← card_powersetCard, ← card_filter]
    congr 1
    ext L
    simp only [mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨hL, hLc⟩
      exact ⟨⟨hL.trans (avail_subset G I J), hLc⟩, hL⟩
    · rintro ⟨⟨_, hLc⟩, hL⟩
      exact ⟨hL, hLc⟩
  rw [sum_congr rfl h1, sum_comm]
  apply sum_congr rfl
  intro L hL
  rw [← card_filter, indepCount_eq_card_indepSets]
  congr 1
  ext J
  simp only [mem_filter, mem_indepSets]
  constructor
  · rintro ⟨⟨hJY, hJc, hJi⟩, hLJ⟩
    exact ⟨fun y hy => mem_filter.mpr ⟨hJY hy, fun i hi hyi =>
      (mem_avail.mp (hLJ hi)).2 y hy hyi⟩, hJc, hJi⟩
  · rintro ⟨hJ, hJc, hJi⟩
    exact ⟨⟨fun y hy => (mem_filter.mp (hJ hy)).1, hJc, hJi⟩, fun i hi =>
      mem_avail.mpr ⟨(mem_powersetCard.mp hL).1 hi, fun y hy hyi =>
        (mem_filter.mp (hJ hy)).2 i hi hyi⟩⟩

/-- **Row family `hall(r, l)`** (Zhang, Lemma 2.4). -/
theorem hall_row_holds (hG : G.IsAcyclic) {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) {r l : ℕ}
    (hr : (Cert.Label.hall r l).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.hall r l).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨-, hrv, -, hl0⟩ := hr
  have hrv' : r < Cert.v (Fintype.card V) G.indepNum := lt_of_lt_of_le hrv (min_le_left _ _)
  have hY := card_univ_sdiff_eq (G := G) hmax
  have hn2a := SmallAlpha.card_le_two_mul_indepNum hG
  have han : G.indepNum ≤ Fintype.card V := by
    rw [← hmax]
    exact card_le_univ I
  -- the inequality for each `l`-subset `L` of `I`
  have hperL : ∀ L ∈ I.powersetCard l,
      ((r : ℚ) + 1) *
          (indepCount G ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) (r + 1) : ℚ) ≤
        (Cert.hallC (Fintype.card V) G.indepNum r l : ℚ) *
          (indepCount G ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) r : ℚ) := by
    intro L hL
    obtain ⟨hLI, hLc⟩ := mem_powersetCard.mp hL
    have h1 := succ_mul_indepCount_le (G := G)
      ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) r
    have h2 := card_le_card_nbrsY hG hI hLI
    have h3 := card_filter_add_card_filter_not (s := univ \ I) (fun y => ∀ i ∈ L, ¬ G.Adj y i)
    rw [hY] at h3
    have hkey : ((((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)).card : ℤ) - r) ≤
        Cert.hallC (Fintype.card V) G.indepNum r l := by
      have hm : max 0 ((l : ℤ) - (Cert.δ (Fintype.card V) G.indepNum : ℤ)) ≤
          (((univ \ I).filter (fun y => ¬ ∀ i ∈ L, ¬ G.Adj y i)).card : ℤ) := by
        apply max_le (Nat.cast_nonneg _)
        unfold Cert.δ Cert.v
        omega
      unfold Cert.hallC
      omega
    have hkey' : ((((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)).card : ℚ) - r) ≤
        (Cert.hallC (Fintype.card V) G.indepNum r l : ℚ) := by exact_mod_cast hkey
    have hnn : (0 : ℚ) ≤
        (indepCount G ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) r : ℚ) :=
      Nat.cast_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_right hkey' hnn)
  have hsumL := sum_le_sum hperL
  rw [← mul_sum, ← mul_sum] at hsumL
  unfold Cert.Row.Holds
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- `r = 0`: `H_{1,l} ≤ c C(a, l)`
    subst hr0
    have h1I : (1 : ℕ) ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
      mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hcoef : ∀ p ∈ Cert.vars (Fintype.card V) G.indepNum,
        ((Cert.Label.hall 0 l).row (Fintype.card V) G.indepNum).coef p.1 p.2 * tArr G I p.1 p.2 =
          (if p.1 = 1 then Cert.binom p.2 l else 0) * tArr G I p.1 p.2 := by
      intro p hp
      have hp1 := (mem_Icc.mp (Cert.mem_vars.mp hp).1).1
      simp only [Cert.Label.row]
      split_ifs <;> first | omega | (push_cast; ring)
    rw [sum_congr rfl hcoef, sum_vars_ite h1I (fun m => Cert.binom m l) (tArr G I),
      sum_tArr_eq hI hmax 1 (fun m => Cert.binom m l)]
    simp only [Cert.Label.row, if_pos, Cert.binom_natCast]
    have e1 : ∑ J ∈ indepSets G (univ \ I) 1, ((avail G I J).card.choose l : ℚ) =
        ∑ L ∈ I.powersetCard l,
          (indepCount G ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) (0 + 1) : ℚ) := by
      exact_mod_cast sum_choose_avail (G := G) I (univ \ I) 1 l
    have e2 : ∑ L ∈ I.powersetCard l,
        (indepCount G ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) 0 : ℚ) =
          (G.indepNum.choose l : ℚ) := by
      simp only [indepCount_zero, Nat.cast_one, sum_const, card_powersetCard, hmax,
        nsmul_eq_mul, mul_one]
    rw [e1]
    rw [e2] at hsumL
    push_cast at hsumL
    linarith
  · -- `r ≥ 1`: `(r + 1) H_{r+1,l} ≤ c H_{r,l}`
    have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
      mem_Icc.mpr ⟨hrpos, hrv'.le⟩
    have hr1I : r + 1 ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
      mem_Icc.mpr ⟨by omega, by omega⟩
    rw [sum_vars_two hr1I hrI (fun m => ((r : ℚ) + 1) * Cert.binom m l)
      (fun m => (Cert.hallC (Fintype.card V) G.indepNum r l : ℚ) * Cert.binom m l)
      ((Cert.Label.hall r l).row (Fintype.card V) G.indepNum).coef (tArr G I)
      (fun j m => by simp only [Cert.Label.row]; split_ifs <;> ring)]
    rw [sum_tArr_eq hI hmax (r + 1) (fun m => ((r : ℚ) + 1) * Cert.binom m l),
      sum_tArr_eq hI hmax r
        (fun m => (Cert.hallC (Fintype.card V) G.indepNum r l : ℚ) * Cert.binom m l)]
    simp only [Cert.Label.row, if_neg (show r ≠ 0 by omega), Cert.binom_natCast]
    rw [← mul_sum, ← mul_sum]
    have e1 : ∑ J ∈ indepSets G (univ \ I) (r + 1), ((avail G I J).card.choose l : ℚ) =
        ∑ L ∈ I.powersetCard l,
          (indepCount G ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) (r + 1) : ℚ) := by
      exact_mod_cast sum_choose_avail (G := G) I (univ \ I) (r + 1) l
    have e2 : ∑ J ∈ indepSets G (univ \ I) r, ((avail G I J).card.choose l : ℚ) =
        ∑ L ∈ I.powersetCard l,
          (indepCount G ((univ \ I).filter (fun y => ∀ i ∈ L, ¬ G.Adj y i)) r : ℚ) := by
      exact_mod_cast sum_choose_avail (G := G) I (univ \ I) r l
    rw [e1, e2]
    linarith

end Forest

end Rows
end Zhang
end Erdos993Lean
