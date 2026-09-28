import Mathlib
import Erdos993Lean.Zhang.Rows.Layers

/-!
# Zhang's finite part, row soundness 4: edge-count bounds (Lemma 2.10)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemma 2.10 and (26)–(29), applied to `F[Y]` with `e = C(v, 2) − T_2`.

* `edgeLower_row_holds`: **row family `edge_lower(r)`** (28), from the union bound (24), for every
  maximum independent set.
* `indepCount_le_star`: **the star upper bound** (25), `i_r ≤ C(v − 1, r) + C(v − e − 1, r − 1)`
  for a nonempty vertex set of an acyclic graph with `v` vertices and `e` edges (induction: no
  edges; an isolated vertex; a leaf `ℓ` with `i_r(s) = i_r(s − ℓ) + i_{r−1}(s − ℓ − w)`).
* `chord_bound`: for `g` with `g 0 = 0` and nonincreasing increments, `e g(D) ≤ D g(e)` (`e ≤ D`).
* `edgeUpper_row_holds`: **row family `edge_upper(r)`** (29), for a maximum independent set with
  `e(F[Y]) ≤ E` (Lemma 2.5), via `g_r(e) = C(v−1, r−1) − C(v−e−1, r−1)` and `e ≤ D_0`.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Row family `edge_lower(r)`** (Zhang (28)). -/
theorem edgeLower_row_holds {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) {r : ℕ}
    (hr : (Cert.Label.edgeLower r).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.edgeLower r).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv⟩ := hr
  have hY := card_univ_sdiff_eq (G := G) hmax
  have h2 : (2 : ℕ) ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨by norm_num, by omega⟩
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  unfold Cert.Row.Holds
  rw [sum_vars_two h2 hrI
    (fun _ => Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) - 2) ((r : ℤ) - 2))
    (fun _ => 1) _ _ (fun j m => by simp only [Cert.Label.row]; split_ifs <;> ring)]
  simp only [Cert.Label.row, one_mul]
  have hb1 : Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) - 2) ((r : ℤ) - 2) =
      ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 2) : ℚ) := binom_eq (by omega) (by omega)
  have hb2 : Cert.binom (Cert.v (Fintype.card V) G.indepNum : ℤ) 2 =
      ((Cert.v (Fintype.card V) G.indepNum).choose 2 : ℚ) := binom_eq rfl (by norm_num)
  have hb3 : Cert.binom (Cert.v (Fintype.card V) G.indepNum : ℤ) (r : ℤ) =
      ((Cert.v (Fintype.card V) G.indepNum).choose r : ℚ) := Cert.binom_natCast _ _
  rw [← mul_sum, sum_tArr_one hI hmax, sum_tArr_one hI hmax, hb1, hb2, hb3]
  have e1 := indepCount_two_add_eIn (G := G) (univ \ I)
  have e2 := choose_le_indepCount_add (G := G) (univ \ I) r
  rw [hY] at e1 e2
  have e1' : ((indepCount G (univ \ I) 2 : ℕ) : ℚ) + (eIn G (univ \ I) : ℚ) =
      ((Cert.v (Fintype.card V) G.indepNum).choose 2 : ℚ) := by exact_mod_cast e1
  have e2' : (((Cert.v (Fintype.card V) G.indepNum).choose r : ℕ) : ℚ) ≤
      (indepCount G (univ \ I) r : ℚ) + (eIn G (univ \ I) : ℚ) *
        ((Cert.v (Fintype.card V) G.indepNum - 2).choose (r - 2) : ℚ) := by exact_mod_cast e2
  nlinarith

/-! ### Edge-count bounds (Lemma 2.10) -/

omit [Fintype V] [DecidableEq V] in
theorem indepCount_eq_choose_of_indep {s : Finset V} (hs : IsIndepFinset G s) (r : ℕ) :
    indepCount G s r = s.card.choose r := by
  rw [indepCount_eq_card_filter, filter_true_of_mem, card_powersetCard]
  intro t ht
  exact isIndepFinset_mono hs (mem_powersetCard.mp ht).1

omit [Fintype V] in
theorem indep_of_eIn_eq_zero {s : Finset V} (h : eIn G s = 0) : IsIndepFinset G s := by
  intro a ha b hb hab
  have hmem : ({a, b} : Finset V) ∈ edgesIn G s := by
    rw [mem_edgesIn]
    refine ⟨insert_subset ha (singleton_subset_iff.mpr hb), card_pair (G.ne_of_adj hab), ?_⟩
    intro hind
    exact hind a (mem_insert_self _ _) b (mem_insert_of_mem (mem_singleton_self _)) hab
  unfold eIn at h
  rw [card_eq_zero] at h
  rw [h] at hmem
  exact notMem_empty _ hmem

omit [Fintype V] in
/-- **Zhang, Lemma 2.10 (25), the star upper bound**: a nonempty vertex set `s` of an acyclic
graph with `e` edges has `i_r ≤ C(|s| − 1, r) + C(|s| − e − 1, r − 1)` for `r ≥ 1` (the
coefficients of `(1 + z)^{v−1} + z (1 + z)^{v−e−1}`).  Induction: no edges; an isolated vertex;
a leaf `ℓ` with neighbour `w` (`i_r(s) = i_r(s − ℓ) + i_{r−1}(s − ℓ − w)`). -/
theorem indepCount_le_star (hG : G.IsAcyclic) {s : Finset V} (hs : s.Nonempty) {r : ℕ}
    (hr : 1 ≤ r) :
    indepCount G s r ≤ (s.card - 1).choose r + (s.card - eIn G s - 1).choose (r - 1) := by
  induction s using Finset.strongInduction generalizing r with
  | H s ih =>
    have hs1 : 1 ≤ s.card := card_pos.mpr hs
    have hev := eIn_lt_card hG hs
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · have : r = 1 := by omega
      subst this
      rw [indepCount_one, Nat.choose_one_right, Nat.sub_self, Nat.choose_zero_right]
      omega
    rcases Nat.eq_zero_or_pos (eIn G s) with he0 | hepos
    · rw [indepCount_eq_choose_of_indep (indep_of_eIn_eq_zero he0), he0, Nat.sub_zero]
      have hp := Nat.choose_succ_succ' (s.card - 1) (r - 1)
      rw [show s.card - 1 + 1 = s.card by omega, show r - 1 + 1 = r by omega] at hp
      omega
    by_cases hiso : ∃ x ∈ s, nbrsIn G s x = ∅
    · obtain ⟨x, hx, hxn⟩ := hiso
      have hsx : s.filter (fun w => w ≠ x) = s.erase x := filter_ne' s x
      have hrec := indepCount_succ_erase (G := G) hx (r - 1)
      rw [outsideClosedNbhd_of_isolated hxn, hsx, show r - 1 + 1 = r by omega] at hrec
      have hee : eIn G (s.erase x) = eIn G s := by
        have := eIn_erase (G := G) hx
        rw [hxn, card_empty, add_zero] at this
        exact this.symm
      have hc := card_erase_add_one hx
      have hne : (s.erase x).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        rw [h, eIn_empty] at hee
        omega
      have ih1 := ih _ (erase_ssubset hx) hne (r := r) (by omega)
      have ih2 := ih _ (erase_ssubset hx) hne (r := r - 1) (by omega)
      rw [hee] at ih1 ih2
      have hev' := eIn_lt_card hG hne
      rw [hee] at hev'
      have p1 := Nat.choose_succ_succ' (s.card - 2) (r - 1)
      rw [show s.card - 2 + 1 = s.card - 1 by omega, show r - 1 + 1 = r by omega] at p1
      have p2 := Nat.choose_succ_succ' (s.card - eIn G s - 2) (r - 2)
      rw [show s.card - eIn G s - 2 + 1 = s.card - eIn G s - 1 by omega,
        show r - 2 + 1 = r - 1 by omega] at p2
      rw [show (s.erase x).card - 1 = s.card - 2 by omega,
        show (s.erase x).card - eIn G s - 1 = s.card - eIn G s - 2 by omega,
        show r - 1 - 1 = r - 2 by omega] at ih2
      rw [show (s.erase x).card - 1 = s.card - 2 by omega,
        show (s.erase x).card - eIn G s - 1 = s.card - eIn G s - 2 by omega] at ih1
      omega
    · push_neg at hiso
      obtain ⟨w, hw, ⟨ℓ, hℓ⟩, -⟩ := Occupation.exists_leafStem hG hiso hs
      obtain ⟨hℓN, hℓn⟩ := Occupation.mem_leavesAt.mp hℓ
      have hℓs : ℓ ∈ s := (mem_nbrsIn.mp hℓN).1
      have hwℓ : w ≠ ℓ := G.ne_of_adj (mem_nbrsIn.mp hℓN).2
      have hwE : w ∈ s.erase ℓ := mem_erase.mpr ⟨hwℓ, hw⟩
      have hrec := indepCount_succ_erase (G := G) hℓs (r - 1)
      rw [outsideClosedNbhd_of_pendant hℓn, show r - 1 + 1 = r by omega] at hrec
      have he1 : eIn G s = eIn G (s.erase ℓ) + 1 := by
        rw [eIn_erase hℓs, hℓn, card_singleton]
      have hc1 := card_erase_add_one hℓs
      have hc2 := card_erase_add_one hwE
      have hne1 : (s.erase ℓ).Nonempty := ⟨w, hwE⟩
      have ih1 := ih _ (erase_ssubset hℓs) hne1 (r := r) (by omega)
      rw [show (s.erase ℓ).card - 1 = s.card - 2 by omega,
        show (s.erase ℓ).card - eIn G (s.erase ℓ) - 1 = s.card - eIn G s - 1 by omega] at ih1
      have p1 := Nat.choose_succ_succ' (s.card - 2) (r - 1)
      rw [show s.card - 2 + 1 = s.card - 1 by omega, show r - 1 + 1 = r by omega] at p1
      have h2 : indepCount G ((s.erase ℓ).erase w) (r - 1) ≤ (s.card - 2).choose (r - 1) := by
        rcases ((s.erase ℓ).erase w).eq_empty_or_nonempty with he | hne2
        · rw [he, indepCount_eq_zero_of_card_lt G ∅ (by rw [card_empty]; omega)]
          exact Nat.zero_le _
        · have ih2 := ih _ ((erase_subset w _).trans_ssubset (erase_ssubset hℓs)) hne2
            (r := r - 1) (by omega)
          have ht1 := card_pos.mpr hne2
          have p2 := Nat.choose_succ_succ' (s.card - 3) (r - 2)
          rw [show s.card - 3 + 1 = s.card - 2 by omega, show r - 2 + 1 = r - 1 by omega] at p2
          have hm : (((s.erase ℓ).erase w).card - eIn G ((s.erase ℓ).erase w) - 1).choose
              (r - 1 - 1) ≤ (s.card - 3).choose (r - 2) := by
            rw [show r - 1 - 1 = r - 2 by omega]
            exact Nat.choose_le_choose _ (by omega)
          rw [show ((s.erase ℓ).erase w).card - 1 = s.card - 3 by omega] at ih2
          omega
      omega

/-- Increments bounded below by the last one sum to at least `e` times it. -/
theorem mul_incr_le (g : ℕ → ℤ) (hg0 : g 0 = 0) (D : ℕ)
    (hinc : ∀ k, k ≤ D → g (D + 1) - g D ≤ g (k + 1) - g k) :
    ∀ e ≤ D, (e : ℤ) * (g (D + 1) - g D) ≤ g e := by
  intro e he
  induction e with
  | zero => simp [hg0]
  | succ e ih =>
    have h1 := ih (by omega)
    have h2 := hinc e (by omega)
    push_cast
    linarith

/-- **Chord bound**: for `g` with `g 0 = 0` and nonincreasing increments on `[0, D]`,
`e g(D) ≤ D g(e)` for `e ≤ D`. -/
theorem chord_bound (g : ℕ → ℤ) (hg0 : g 0 = 0) :
    ∀ D : ℕ, (∀ j k, j ≤ k → k < D → g (k + 1) - g k ≤ g (j + 1) - g j) →
      ∀ e ≤ D, (e : ℤ) * g D ≤ D * g e := by
  intro D
  induction D with
  | zero =>
    intro _ e he
    have : e = 0 := by omega
    subst this
    simp
  | succ D ih =>
    intro hinc e he
    rcases Nat.lt_or_ge e (D + 1) with h | h
    · have h1 := ih (fun j k hjk hk => hinc j k hjk (by omega)) e (by omega)
      have h2 := mul_incr_le g hg0 D (fun k hk => hinc k D hk (by omega)) e (by omega)
      push_cast
      linarith
    · have : e = D + 1 := by omega
      subst this
      exact le_refl _

/-- **Row family `edge_upper(r)`** (Zhang (29)): the chord below `g_r(e) = C(v−1, r−1) −
C(v−e−1, r−1)` on `[0, D_0]`, for the `I` of Lemma 2.5 (`e ≤ E`). -/
theorem edgeUpper_row_holds (hG : G.IsAcyclic) {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (he : eIn G (univ \ I) ≤ Cert.E (Fintype.card V) G.indepNum)
    {r : ℕ} (hr : (Cert.Label.edgeUpper r).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.edgeUpper r).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv, hD⟩ := hr
  have hY := card_univ_sdiff_eq (G := G) hmax
  have h2 : (2 : ℕ) ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨by norm_num, by omega⟩
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  have hD0v : Cert.D0 (Fintype.card V) G.indepNum ≤ Cert.v (Fintype.card V) G.indepNum - 1 :=
    min_le_right _ _
  have hD0E : Cert.D0 (Fintype.card V) G.indepNum = min (Cert.E (Fintype.card V) G.indepNum)
      (Cert.v (Fintype.card V) G.indepNum - 1) := rfl
  have hYne : (univ \ I).Nonempty := by
    rw [← card_pos, hY]
    omega
  have hev := eIn_lt_card hG hYne
  rw [hY] at hev
  have heD : eIn G (univ \ I) ≤ Cert.D0 (Fintype.card V) G.indepNum := by
    rw [hD0E]
    exact le_min he (by omega)
  unfold Cert.Row.Holds
  rw [sum_vars_two hrI h2 (fun _ => (Cert.D0 (Fintype.card V) G.indepNum : ℚ))
    (fun _ => Cert.Gr (Fintype.card V) G.indepNum r)
    ((Cert.Label.edgeUpper r).row (Fintype.card V) G.indepNum).coef (tArr G I) (fun j m => rfl)]
  simp only [Cert.Label.row]
  rw [← mul_sum, ← mul_sum, sum_tArr_one hI hmax, sum_tArr_one hI hmax]
  have hb2 : Cert.binom (Cert.v (Fintype.card V) G.indepNum : ℤ) 2 =
      ((Cert.v (Fintype.card V) G.indepNum).choose 2 : ℚ) := binom_eq rfl (by norm_num)
  have hbr : Cert.binom (Cert.v (Fintype.card V) G.indepNum : ℤ) (r : ℤ) =
      ((Cert.v (Fintype.card V) G.indepNum).choose r : ℚ) := Cert.binom_natCast _ _
  have hg1 : Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) - 1) ((r : ℤ) - 1) =
      ((Cert.v (Fintype.card V) G.indepNum - 1).choose (r - 1) : ℚ) :=
    binom_eq (by omega) (by omega)
  have hg2 : Cert.binom ((Cert.v (Fintype.card V) G.indepNum : ℤ) -
      (Cert.D0 (Fintype.card V) G.indepNum : ℤ) - 1) ((r : ℤ) - 1) =
      ((Cert.v (Fintype.card V) G.indepNum - Cert.D0 (Fintype.card V) G.indepNum - 1).choose
        (r - 1) : ℚ) := binom_eq (by omega) (by omega)
  simp only [Cert.Gr, hb2, hbr, hg1, hg2]
  -- the concave function `g(k) = C(v−1, r−1) − C(v−1−k, r−1)`
  set v := Cert.v (Fintype.card V) G.indepNum with hvdef
  set D := Cert.D0 (Fintype.card V) G.indepNum with hDdef
  set e := eIn G (univ \ I) with hedef
  set g : ℕ → ℤ := fun k => ((v - 1).choose (r - 1) : ℤ) - ((v - 1 - k).choose (r - 1) : ℤ)
    with hgdef
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hinc : ∀ j k, j ≤ k → k < D → g (k + 1) - g k ≤ g (j + 1) - g j := by
    intro j k hjk hk
    have pk := Nat.choose_succ_succ' (v - 1 - (k + 1)) (r - 2)
    rw [show v - 1 - (k + 1) + 1 = v - 1 - k by omega, show r - 2 + 1 = r - 1 by omega] at pk
    have pj := Nat.choose_succ_succ' (v - 1 - (j + 1)) (r - 2)
    rw [show v - 1 - (j + 1) + 1 = v - 1 - j by omega, show r - 2 + 1 = r - 1 by omega] at pj
    have hm : (v - 1 - (k + 1)).choose (r - 2) ≤ (v - 1 - (j + 1)).choose (r - 2) :=
      Nat.choose_le_choose _ (by omega)
    have pk' : ((v - 1 - k).choose (r - 1) : ℤ) = ((v - 1 - (k + 1)).choose (r - 2) : ℤ) +
        ((v - 1 - (k + 1)).choose (r - 1) : ℤ) := by exact_mod_cast pk
    have pj' : ((v - 1 - j).choose (r - 1) : ℤ) = ((v - 1 - (j + 1)).choose (r - 2) : ℤ) +
        ((v - 1 - (j + 1)).choose (r - 1) : ℤ) := by exact_mod_cast pj
    have hm' : ((v - 1 - (k + 1)).choose (r - 2) : ℤ) ≤ ((v - 1 - (j + 1)).choose (r - 2) : ℤ) := by
      exact_mod_cast hm
    simp only [hgdef]
    linarith
  have hchord := chord_bound g hg0 D hinc e heD
  simp only [hgdef] at hchord
  -- the star bound and Pascal
  have hstar := indepCount_le_star hG hYne (r := r) (by omega)
  rw [hY] at hstar
  have hp := Nat.choose_succ_succ' (v - 1) (r - 1)
  rw [show v - 1 + 1 = v by omega, show r - 1 + 1 = r by omega] at hp
  have hT2 := indepCount_two_add_eIn (G := G) (univ \ I)
  rw [hY] at hT2
  have hstar' : (indepCount G (univ \ I) r : ℚ) ≤ ((v - 1).choose r : ℚ) +
      ((v - e - 1).choose (r - 1) : ℚ) := by exact_mod_cast hstar
  have hp' : (v.choose r : ℚ) = ((v - 1).choose (r - 1) : ℚ) + ((v - 1).choose r : ℚ) := by
    exact_mod_cast hp
  have hT2' : (indepCount G (univ \ I) 2 : ℚ) + (e : ℚ) = (v.choose 2 : ℚ) := by
    exact_mod_cast hT2
  have hchord' : (e : ℚ) * (((v - 1).choose (r - 1) : ℚ) - ((v - 1 - D).choose (r - 1) : ℚ)) ≤
      (D : ℚ) * (((v - 1).choose (r - 1) : ℚ) - ((v - 1 - e).choose (r - 1) : ℚ)) := by
    exact_mod_cast hchord
  rw [show v - 1 - e = v - e - 1 by omega, show v - 1 - D = v - D - 1 by omega] at hchord'
  have hD0 : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hmono := mul_le_mul_of_nonneg_left
    (show ((v - 1).choose (r - 1) : ℚ) - ((v - e - 1).choose (r - 1) : ℚ) ≤
      (v.choose r : ℚ) - indepCount G (univ \ I) r by linarith) hD0
  nlinarith

end Forest

end Rows
end Zhang
end Erdos993Lean
