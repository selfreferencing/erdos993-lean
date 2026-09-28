import Mathlib
import Erdos993Lean.Zhang.Rows.Private

/-!
# Zhang's finite part, row soundness 8: deletion thresholds (Lemmas 2.6 and 2.7)

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemmas 2.6, 2.7 and (14)–(20).

* `tail_aux`: `b_{r,h}(m) ≤ #{u ∈ J : m(J − u) ≥ h}`; `tail_row_holds`: **row family
  `tail(r, h)`**, for every maximum independent set.
* `sum_max_le_U`: the maximization behind `U_{r,h}` (`m ≤ y_u ≤ m + L`, `Σ y_u ≤ r m + qL + ρ`);
  `U_eq`: `U_{r,h}(m)` as an integer expression; `release_aux`:
  `Σ_{u ∈ J} (m(J − u) − h)_+ ≤ U_{r,h}(m)`; `tailUpper_aux`: `#{u : m(J − u) ≥ h} ≤ V_{r,h}(m)`.
* `sExt_le_extIn`: `s_r ≤ ext(K)` for every independent `(r−1)`-subset `K` of `Y`, when
  `e(F[Y]) ≤ E` (Lemma 2.5).
* `releaseUpper_row_holds`, `tailUpper_row_holds`: **row families `release_upper(r, h)` and
  `tail_upper(r, h)`**, for a maximum independent set with `e(F[Y]) ≤ E`.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Deletion thresholds (Lemmas 2.6 and 2.7) -/

/-- Per independent `J` (Lemma 2.6): `b_{r,h}(m) ≤ #{u ∈ J : m(J − u) ≥ h}`. -/
theorem tail_aux (hG : G.IsAcyclic) {I J : Finset V} (hI : IsIndepFinset G I)
    (hJ : J ⊆ univ \ I) (hJi : IsIndepFinset G J) (hJne : J.Nonempty) (h : ℕ) :
    Cert.bStep I.card J.card h (avail G I J).card ≤
      ((J.filter (fun u => h ≤ (avail G I (J.erase u)).card)).card : ℚ) := by
  unfold Cert.bStep
  split_ifs with h1 h2
  · rw [filter_true_of_mem (fun u _ => le_trans h1 (card_le_card (avail_anti (erase_subset u J))))]
  · have hne : (J.filter (fun u => h ≤ (avail G I (J.erase u)).card)).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hne
      have hsum : ∑ u ∈ J, (avail G I (J.erase u)).card ≤ J.card * (h - 1) := by
        calc ∑ u ∈ J, (avail G I (J.erase u)).card ≤ ∑ _u ∈ J, (h - 1) :=
              sum_le_sum (fun u hu => by have := hne hu; omega)
          _ = J.card * (h - 1) := by rw [sum_const, smul_eq_mul]
      have hL := sum_card_avail_erase_ge hG hI hJ hJi hJne
      have hm : (avail G I J).card ≤ I.card := card_le_card (avail_subset G I J)
      have hJ1 : 1 ≤ J.card := card_pos.mpr hJne
      have hL' : ((J.card * (avail G I J).card + (I.card - (avail G I J).card) + 1 : ℕ) : ℤ) ≤
          ((∑ u ∈ J, (avail G I (J.erase u)).card + J.card : ℕ) : ℤ) := Nat.cast_le.mpr hL
      push_cast [Nat.cast_sub hm] at hL'
      have hsum' : ((∑ u ∈ J, (avail G I (J.erase u)).card : ℕ) : ℤ) ≤
          ((J.card * (h - 1) : ℕ) : ℤ) := Nat.cast_le.mpr hsum
      push_cast [Nat.cast_sub (show 1 ≤ h by omega)] at hsum'
      have h2' : ((J.card * h : ℕ) : ℤ) ≤ ((I.card + (J.card - 1) * (avail G I J).card : ℕ) : ℤ) :=
        Nat.cast_le.mpr h2
      push_cast [Nat.cast_sub hJ1] at h2'
      nlinarith
    have := card_pos.mpr hne
    exact_mod_cast this
  · exact Nat.cast_nonneg _

/-- Per independent `J` (Lemma 2.7, indicator form): `#{u ∈ J : m(J − u) ≥ h} ≤ V_{r,h}(m)`. -/
theorem tailUpper_aux {I J : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum)
    (hJ : J ⊆ univ \ I) (hJi : IsIndepFinset G J) (h : ℕ) :
    ((J.filter (fun u => h ≤ (avail G I (J.erase u)).card)).card : ℚ) ≤
      Cert.Vt I.card J.card h (avail G I J).card := by
  have hrm : J.card + (avail G I J).card ≤ I.card := card_add_card_avail_le hI hmax hJ hJi
  have hcardle : (J.filter (fun u => h ≤ (avail G I (J.erase u)).card)).card ≤ J.card :=
    card_filter_le _ _
  unfold Cert.Vt
  simp only []
  split_ifs with h1 h2
  · exact_mod_cast hcardle
  · have hmul : (J.filter (fun u => h ≤ (avail G I (J.erase u)).card)).card *
        (h - (avail G I J).card) ≤ I.card - (avail G I J).card := by
      calc (J.filter (fun u => h ≤ (avail G I (J.erase u)).card)).card *
            (h - (avail G I J).card)
          = ∑ _u ∈ J.filter (fun u => h ≤ (avail G I (J.erase u)).card),
              (h - (avail G I J).card) := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ u ∈ J.filter (fun u => h ≤ (avail G I (J.erase u)).card), (priv G I J u).card := by
            apply sum_le_sum
            intro u hu
            have := (mem_filter.mp hu).2
            rw [card_avail_erase] at this
            omega
        _ ≤ ∑ u ∈ J, (priv G I J u).card := sum_le_sum_of_subset (filter_subset _ _)
        _ ≤ (I \ avail G I J).card := sum_card_priv_le I J
        _ = I.card - (avail G I J).card := card_sdiff_of_subset (avail_subset G I J)
    have hdiv : (J.filter (fun u => h ≤ (avail G I (J.erase u)).card)).card ≤
        (I.card - (avail G I J).card) / (h - (avail G I J).card) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr hmul
    exact_mod_cast le_min hcardle hdiv
  · have hempty : J.filter (fun u => h ≤ (avail G I (J.erase u)).card) = ∅ := by
      rw [filter_eq_empty_iff]
      intro u hu hle
      have := card_avail_erase_add_le hI hmax hJ hJi hu
      omega
    rw [hempty, card_empty, Nat.cast_zero]

/-- **The maximization behind `U_{r,h}`** (Zhang, proof of Lemma 2.7): if `m ≤ y_u ≤ m + L` and
`Σ y_u ≤ r m + d` with `d = qL + ρ`, `q ≥ 0`, then
`Σ (y_u − h)_+ ≤ q (m + L − h)_+ + [q < r] ((m + ρ − h)_+ + (r − q − 1)(m − h)_+)`. -/
theorem sum_max_le_U {ι : Type*} (J : Finset ι) (y : ι → ℤ) (m h L d q ρ : ℤ) (r : ℕ)
    (hJ : J.card = r) (hy0 : ∀ u ∈ J, m ≤ y u) (hyL : ∀ u ∈ J, y u ≤ m + L)
    (hsum : ∑ u ∈ J, y u ≤ r * m + d) (hd : d = q * L + ρ) (hq : 0 ≤ q) :
    ∑ u ∈ J, max (y u - h) 0 ≤
      q * max (m + L - h) 0 +
        (if q < r then max (m + ρ - h) 0 + (r - q - 1) * max (m - h) 0 else 0) := by
  classical
  set A := J.filter (fun u => 0 < y u - h) with hA
  have hsplit : ∑ u ∈ J, max (y u - h) 0 = ∑ u ∈ A, (y u - h) := by
    rw [hA, sum_filter]
    apply sum_congr rfl
    intro u _
    split_ifs with hu
    · exact max_eq_left hu.le
    · push_neg at hu
      exact max_eq_right hu
  rw [hsplit]
  have hk : (A.card : ℤ) ≤ r := by
    rw [← hJ]
    exact_mod_cast card_le_card (filter_subset _ _)
  by_cases hkq : (A.card : ℤ) ≤ q
  · have h1 : ∑ u ∈ A, (y u - h) ≤ ∑ _u ∈ A, max (m + L - h) 0 := by
      apply sum_le_sum
      intro u hu
      have := hyL u (mem_filter.mp hu).1
      exact le_trans (by linarith) (le_max_left _ _)
    rw [sum_const, nsmul_eq_mul] at h1
    have h2 : (A.card : ℤ) * max (m + L - h) 0 ≤ q * max (m + L - h) 0 :=
      mul_le_mul_of_nonneg_right hkq (le_max_right _ _)
    have h3 : 0 ≤ (if q < r then max (m + ρ - h) 0 + (r - q - 1) * max (m - h) 0 else 0) := by
      split_ifs with hqr'
      · have e1 : (0 : ℤ) ≤ r - q - 1 := by omega
        have e2 := le_max_right (m + ρ - h) 0
        have e3 := mul_nonneg e1 (le_max_right (m - h) 0)
        linarith
      · exact le_refl 0
    linarith
  · push_neg at hkq
    have hqr' : q < r := lt_of_lt_of_le hkq hk
    rw [if_pos hqr']
    have h1 : ∑ u ∈ A, (y u - m) ≤ d := by
      have e1 : ∑ u ∈ A, (y u - m) ≤ ∑ u ∈ J, (y u - m) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun u hu _ => by have := hy0 u hu; linarith)
      have e2 : ∑ u ∈ J, (y u - m) = ∑ u ∈ J, y u - r * m := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hJ]
      linarith
    have h2 : ∑ u ∈ A, (y u - h) = ∑ u ∈ A, (y u - m) + A.card * (m - h) := by
      rw [show (fun u => y u - h) = fun u => (y u - m) + (m - h) by funext u; ring,
        sum_add_distrib, sum_const, nsmul_eq_mul]
    have e0 : (0 : ℤ) ≤ (A.card : ℤ) - q - 1 := by omega
    have h3 : ((A.card : ℤ) - q - 1) * (m - h) ≤ ((A.card : ℤ) - q - 1) * max (m - h) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) e0
    have h4 : ((A.card : ℤ) - q - 1) * max (m - h) 0 ≤ ((r : ℤ) - q - 1) * max (m - h) 0 :=
      mul_le_mul_of_nonneg_right (by linarith) (le_max_right _ _)
    have h5 : q * (m + L - h) ≤ q * max (m + L - h) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hq
    have h6 : m + ρ - h ≤ max (m + ρ - h) 0 := le_max_left _ _
    rw [h2]
    nlinarith

theorem U_eq (a r h m : ℕ) :
    Cert.U a r h m =
      (((((a - m) / (a - m + 1 - r) : ℕ) : ℤ) *
          max ((m : ℤ) + ((a - m + 1 - r : ℕ) : ℤ) - h) 0 +
        (if (((a - m) / (a - m + 1 - r) : ℕ) : ℤ) < r then
          max ((m : ℤ) + (((a - m) % (a - m + 1 - r) : ℕ) : ℤ) - h) 0 +
            ((r : ℤ) - (((a - m) / (a - m + 1 - r) : ℕ) : ℤ) - 1) * max ((m : ℤ) - h) 0
        else 0) : ℤ) : ℚ) := by
  unfold Cert.U Cert.pos
  simp only [Nat.cast_lt]
  generalize (a - m) / (a - m + 1 - r) = q
  generalize (a - m) % (a - m + 1 - r) = ρ
  generalize a - m + 1 - r = L
  split_ifs with hq
  · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  · push_cast
    ring

/-- Per independent `J` (Lemma 2.7, release form): `Σ_{u ∈ J} (m(J − u) − h)_+ ≤ U_{r,h}(m)`. -/
theorem release_aux {I J : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum)
    (hJ : J ⊆ univ \ I) (hJi : IsIndepFinset G J) (hJne : J.Nonempty) (h : ℕ) :
    ∑ u ∈ J, Cert.pos (((avail G I (J.erase u)).card : ℤ) - h) ≤
      Cert.U I.card J.card h (avail G I J).card := by
  have hrm := card_add_card_avail_le hI hmax hJ hJi
  have hr1 : 1 ≤ J.card := card_pos.mpr hJne
  have hdm := Nat.div_add_mod (I.card - (avail G I J).card)
    (I.card - (avail G I J).card + 1 - J.card)
  have key := sum_max_le_U J (fun u => ((avail G I (J.erase u)).card : ℤ))
    ((avail G I J).card : ℤ) h
    ((I.card - (avail G I J).card + 1 - J.card : ℕ) : ℤ)
    ((I.card - (avail G I J).card : ℕ) : ℤ)
    (((I.card - (avail G I J).card) / (I.card - (avail G I J).card + 1 - J.card) : ℕ) : ℤ)
    (((I.card - (avail G I J).card) % (I.card - (avail G I J).card + 1 - J.card) : ℕ) : ℤ)
    J.card rfl
    (fun u _ => by
      show ((avail G I J).card : ℤ) ≤ ((avail G I (J.erase u)).card : ℤ)
      exact_mod_cast card_le_card (avail_anti (erase_subset u J)))
    (fun u hu => by
      have := card_avail_erase_add_le hI hmax hJ hJi hu
      simp only []
      omega)
    (by
      have := sum_card_avail_erase_le (G := G) I J
      simp only []
      exact_mod_cast this)
    (by
      have e : (((I.card - (avail G I J).card + 1 - J.card) *
          ((I.card - (avail G I J).card) / (I.card - (avail G I J).card + 1 - J.card)) +
          (I.card - (avail G I J).card) % (I.card - (avail G I J).card + 1 - J.card) : ℕ) : ℤ) =
          ((I.card - (avail G I J).card : ℕ) : ℤ) := by exact_mod_cast hdm
      push_cast at e ⊢
      linarith)
    (by positivity)
  simp only [] at key
  rw [U_eq]
  unfold Cert.pos
  rw [← Int.cast_sum]
  exact_mod_cast key

/-- `s_r` is at most the number of extensions of any independent `(r−1)`-subset of `Y` (Zhang (16);
uses `e(F[Y]) ≤ E`). -/
theorem sExt_le_extIn {I K : Finset V} (hmax : I.card = G.indepNum)
    (he : eIn G (univ \ I) ≤ Cert.E (Fintype.card V) G.indepNum) {r : ℕ} (hr : 1 ≤ r)
    (hK : K ∈ indepSets G (univ \ I) (r - 1)) :
    Cert.sExt (Fintype.card V) G.indepNum r ≤ ((extIn G (univ \ I) K).card : ℚ) := by
  obtain ⟨hKY, hKc, hKi⟩ := mem_indepSets.mp hK
  have h1 := card_sdiff_le_extIn_add_eIn (G := G) hKY hKi
  rw [card_sdiff_of_subset hKY, card_univ_sdiff_eq hmax, hKc] at h1
  unfold Cert.sExt Cert.pos
  have key : max ((Cert.v (Fintype.card V) G.indepNum : ℤ) - r + 1 -
      Cert.E (Fintype.card V) G.indepNum) 0 ≤ ((extIn G (univ \ I) K).card : ℤ) := by
    apply max_le
    · omega
    · exact Nat.cast_nonneg _
  exact_mod_cast key

theorem sExt_nonneg (n a r : ℕ) : 0 ≤ Cert.sExt n a r := pos_nonneg _

/-- **Row family `tail(r, h)`** (Zhang, Lemma 2.6). -/
theorem tail_row_holds (hG : G.IsAcyclic) {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) {r h : ℕ}
    (hr : (Cert.Label.tail r h).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.tail r h).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv, -⟩ := hr
  have hY := card_univ_sdiff_eq (G := G) hmax
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  have hr1I : r - 1 ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨by omega, by omega⟩
  unfold Cert.Row.Holds
  rw [sum_vars_two hrI hr1I (fun m => Cert.bStep G.indepNum r h m)
    (fun m => if h ≤ m then (Cert.v (Fintype.card V) G.indepNum : ℚ) - r + 1 else 0)
    ((Cert.Label.tail r h).row (Fintype.card V) G.indepNum).coef (tArr G I)
    (fun j m => by simp only [Cert.Label.row, ite_and])]
  rw [sum_tArr_eq hI hmax r (fun m => Cert.bStep G.indepNum r h m),
    sum_tArr_eq hI hmax (r - 1)
      (fun m => if h ≤ m then (Cert.v (Fintype.card V) G.indepNum : ℚ) - r + 1 else 0)]
  simp only [Cert.Label.row, sub_nonpos]
  have hper : ∀ J ∈ indepSets G (univ \ I) r, Cert.bStep G.indepNum r h (avail G I J).card ≤
      ∑ u ∈ J, (if h ≤ (avail G I (J.erase u)).card then (1 : ℚ) else 0) := by
    intro J hJ
    obtain ⟨hJY, hJc, hJi⟩ := mem_indepSets.mp hJ
    have hJne : J.Nonempty := by
      rw [← card_pos, hJc]
      omega
    have := tail_aux hG hI hJY hJi hJne h
    rw [hJc, hmax] at this
    rw [sum_boole]
    exact this
  have hdc := sum_sum_erase_le (G := G) (univ \ I) (r - 1)
    (fun K => if h ≤ (avail G I K).card then (1 : ℚ) else 0)
    (fun K _ => by dsimp only; split_ifs <;> norm_num)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r), hY] at hdc
  calc ∑ J ∈ indepSets G (univ \ I) r, Cert.bStep G.indepNum r h (avail G I J).card
      ≤ ∑ J ∈ indepSets G (univ \ I) r,
          ∑ u ∈ J, (if h ≤ (avail G I (J.erase u)).card then (1 : ℚ) else 0) := sum_le_sum hper
    _ ≤ _ := hdc
    _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro K _
        split_ifs
        · rw [Nat.cast_sub (by omega : 1 ≤ r)]
          push_cast
          ring
        · ring

/-- **Row family `tail_upper(r, h)`** (Zhang, Lemma 2.7 (20)), for the `I` of Lemma 2.5. -/
theorem tailUpper_row_holds {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (he : eIn G (univ \ I) ≤ Cert.E (Fintype.card V) G.indepNum)
    {r h : ℕ} (hr : (Cert.Label.tailUpper r h).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.tailUpper r h).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv, -⟩ := hr
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  have hr1I : r - 1 ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨by omega, by omega⟩
  unfold Cert.Row.Holds
  rw [sum_vars_two hr1I hrI (fun m => if h ≤ m then Cert.sExt (Fintype.card V) G.indepNum r else 0)
    (fun m => Cert.Vt G.indepNum r h m)
    ((Cert.Label.tailUpper r h).row (Fintype.card V) G.indepNum).coef (tArr G I)
    (fun j m => by simp only [Cert.Label.row, ite_and])]
  rw [sum_tArr_eq hI hmax (r - 1)
      (fun m => if h ≤ m then Cert.sExt (Fintype.card V) G.indepNum r else 0),
    sum_tArr_eq hI hmax r (fun m => Cert.Vt G.indepNum r h m)]
  simp only [Cert.Label.row, sub_nonpos]
  have hdc := le_sum_sum_erase (G := G) (univ \ I) (r - 1)
    (fun K => if h ≤ (avail G I K).card then (1 : ℚ) else 0)
    (Cert.sExt (Fintype.card V) G.indepNum r) (fun K _ => by dsimp only; split_ifs <;> norm_num)
    (fun K hK => sExt_le_extIn hmax he (by omega) hK)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hdc
  have hper : ∀ J ∈ indepSets G (univ \ I) r,
      ∑ u ∈ J, (if h ≤ (avail G I (J.erase u)).card then (1 : ℚ) else 0) ≤
        Cert.Vt G.indepNum r h (avail G I J).card := by
    intro J hJ
    obtain ⟨hJY, hJc, hJi⟩ := mem_indepSets.mp hJ
    have := tailUpper_aux hI hmax hJY hJi h
    rw [hJc, hmax] at this
    rw [sum_boole]
    exact this
  calc ∑ K ∈ indepSets G (univ \ I) (r - 1),
        (if h ≤ (avail G I K).card then Cert.sExt (Fintype.card V) G.indepNum r else 0)
      = Cert.sExt (Fintype.card V) G.indepNum r * ∑ K ∈ indepSets G (univ \ I) (r - 1),
          (if h ≤ (avail G I K).card then (1 : ℚ) else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro K _
        split_ifs <;> ring
    _ ≤ _ := hdc
    _ ≤ _ := sum_le_sum hper

/-- **Row family `release_upper(r, h)`** (Zhang, Lemma 2.7 (19)), for the `I` of Lemma 2.5. -/
theorem releaseUpper_row_holds {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (he : eIn G (univ \ I) ≤ Cert.E (Fintype.card V) G.indepNum)
    {r h : ℕ} (hr : (Cert.Label.releaseUpper r h).InDomain (Fintype.card V) G.indepNum) :
    ((Cert.Label.releaseUpper r h).row (Fintype.card V) G.indepNum).Holds (Fintype.card V)
      G.indepNum (tArr G I) := by
  obtain ⟨hr2, hrv, -⟩ := hr
  have hrI : r ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) := mem_Icc.mpr ⟨by omega, hrv⟩
  have hr1I : r - 1 ∈ Icc 1 (Cert.v (Fintype.card V) G.indepNum) :=
    mem_Icc.mpr ⟨by omega, by omega⟩
  unfold Cert.Row.Holds
  rw [sum_vars_two hr1I hrI
    (fun m => Cert.sExt (Fintype.card V) G.indepNum r * Cert.pos ((m : ℤ) - h))
    (fun m => Cert.U G.indepNum r h m)
    ((Cert.Label.releaseUpper r h).row (Fintype.card V) G.indepNum).coef (tArr G I)
    (fun j m => rfl)]
  rw [sum_tArr_eq hI hmax (r - 1)
      (fun m => Cert.sExt (Fintype.card V) G.indepNum r * Cert.pos ((m : ℤ) - h)),
    sum_tArr_eq hI hmax r (fun m => Cert.U G.indepNum r h m)]
  simp only [Cert.Label.row, sub_nonpos]
  have hdc := le_sum_sum_erase (G := G) (univ \ I) (r - 1)
    (fun K => Cert.pos (((avail G I K).card : ℤ) - h))
    (Cert.sExt (Fintype.card V) G.indepNum r) (fun K _ => pos_nonneg _)
    (fun K hK => sExt_le_extIn hmax he (by omega) hK)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hdc
  have hper : ∀ J ∈ indepSets G (univ \ I) r,
      ∑ u ∈ J, Cert.pos (((avail G I (J.erase u)).card : ℤ) - h) ≤
        Cert.U G.indepNum r h (avail G I J).card := by
    intro J hJ
    obtain ⟨hJY, hJc, hJi⟩ := mem_indepSets.mp hJ
    have hJne : J.Nonempty := by
      rw [← card_pos, hJc]
      omega
    have := release_aux hI hmax hJY hJi hJne h
    rw [hJc, hmax] at this
    exact this
  calc ∑ K ∈ indepSets G (univ \ I) (r - 1),
        Cert.sExt (Fintype.card V) G.indepNum r * Cert.pos (((avail G I K).card : ℤ) - h)
      = Cert.sExt (Fintype.card V) G.indepNum r * ∑ K ∈ indepSets G (univ \ I) (r - 1),
          Cert.pos (((avail G I K).card : ℤ) - h) := by rw [mul_sum]
    _ ≤ _ := hdc
    _ ≤ _ := sum_le_sum hper

end Forest

end Rows
end Zhang
end Erdos993Lean
