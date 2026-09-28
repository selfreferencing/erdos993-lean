import Mathlib
import Erdos993Lean.Zhang.Rows.Basic

/-!
# Zhang's finite part, row soundness 3: from the array `t_{j,m}` to independent sets

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Sections 2.1 and 2.9.  Throughout, `I` is a maximum independent set of the
graph (`I.card = G.indepNum`), `Y = V \ I`, and `t_{j,m} = tArr G I j m`.

* `exists_adj_of_notMem`: every vertex outside `I` has a neighbour in `I`;
  `card_add_card_avail_le`: `j + m(J) ≤ a` for an independent `J ⊆ Y`.
* `sum_tArr_eq` (**the bridge**): `Σ_{m ≤ a − j} f(m) t_{j,m} = Σ_J f(m(J))` over the independent
  `j`-subsets `J` of `Y`; `sum_tArr_one`: `Σ_m t_{j,m} = T_j = i_j(F[Y])`.
* `sum_vars_ite`, `sum_vars_two`: a row supported on one or two layers is a layer sum.
* `binom_eq`: the paper's binomial at integer arguments equal to natural numbers.
* `choose_le_indepCount_add`: `C(v, r) ≤ i_r + e C(v − 2, r − 2)` (Zhang (24)).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Maximality of `I` -/

/-- Every vertex outside a maximum independent set has a neighbour in it. -/
theorem exists_adj_of_notMem {I : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) {y : V} (hy : y ∉ I) : ∃ i ∈ I, G.Adj y i := by
  by_contra hcon
  push_neg at hcon
  have hind := isIndepFinset_insert hI hcon
  have := le_alphaIn (subset_univ (insert y I)) hind
  rw [alphaIn_univ, card_insert_of_notMem hy, hmax] at this
  omega

/-- `j + m(J) ≤ a` for an independent `J ⊆ Y`. -/
theorem card_add_card_avail_le {I J : Finset V} (hI : IsIndepFinset G I)
    (hmax : I.card = G.indepNum) (hJ : J ⊆ univ \ I) (hJi : IsIndepFinset G J) :
    J.card + (avail G I J).card ≤ I.card := by
  have h := card_avail_add_card_le hI (subset_univ I) hJ hJi
  rwa [alphaIn_univ, ← hmax] at h

/-! ### From the array `t_{j,m}` to sums over independent sets -/

/-- **The bridge**: `Σ_m f(m) t_{j,m} = Σ_{J} f(m(J))`, over the independent `j`-subsets `J` of
`Y = V \ I`. -/
theorem sum_tArr_eq {I : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum)
    (j : ℕ) (f : ℕ → ℚ) :
    ∑ m ∈ range (G.indepNum + 1 - j), f m * tArr G I j m =
      ∑ J ∈ indepSets G (univ \ I) j, f (avail G I J).card := by
  have hmaps : ∀ J ∈ indepSets G (univ \ I) j,
      (fun J => (avail G I J).card) J ∈ range (G.indepNum + 1 - j) := by
    intro J hJ
    obtain ⟨hJY, hJc, hJi⟩ := mem_indepSets.mp hJ
    have h := card_add_card_avail_le hI hmax hJY hJi
    rw [mem_range]
    dsimp only
    omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro m _
  rw [sum_congr rfl (g := fun _ => f m) (fun J hJ => by rw [(mem_filter.mp hJ).2]),
    sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  unfold tArr tCount
  congr 1
  congr 1
  ext J
  simp only [mem_filter, mem_powerset, indepSets, mem_powersetCard]
  tauto

/-- The layer sums: `Σ_m t_{j,m} = T_j`, the number of independent `j`-subsets of `Y`. -/
theorem sum_tArr_one {I : Finset V} (hI : IsIndepFinset G I) (hmax : I.card = G.indepNum)
    (j : ℕ) :
    ∑ m ∈ range (G.indepNum + 1 - j), tArr G I j m = indepCount G (univ \ I) j := by
  have h := sum_tArr_eq hI hmax j (fun _ => 1)
  simp only [one_mul, sum_const, nsmul_eq_mul, mul_one] at h
  rw [h, indepCount_eq_card_indepSets]

/-! ### Rows as sums over layers -/

theorem sum_vars_ite {n a r : ℕ} (hr : r ∈ Icc 1 (Cert.v n a)) (F : ℕ → ℚ)
    (t : ℕ → ℕ → ℚ) :
    ∑ p ∈ Cert.vars n a, (if p.1 = r then F p.2 else 0) * t p.1 p.2 =
      ∑ m ∈ range (a + 1 - r), F m * t r m := by
  simp only [ite_mul, zero_mul]
  rw [← sum_filter]
  exact Cert.sum_vars_layer hr (fun j m => F m * t j m)

theorem sum_vars_ite_zero {n a r : ℕ} (hr : r ∉ Icc 1 (Cert.v n a)) (F : ℕ → ℚ)
    (t : ℕ → ℕ → ℚ) :
    ∑ p ∈ Cert.vars n a, (if p.1 = r then F p.2 else 0) * t p.1 p.2 = 0 := by
  apply sum_eq_zero
  intro p hp
  have := (Cert.mem_vars.mp hp).1
  rw [if_neg (show p.1 ≠ r from fun h => hr (h ▸ this)), zero_mul]

/-- A row with coefficients on two layers `r` and `r'`. -/
theorem sum_vars_two {n a r r' : ℕ} (hr : r ∈ Icc 1 (Cert.v n a))
    (hr' : r' ∈ Icc 1 (Cert.v n a)) (F F' : ℕ → ℚ) (coef : ℕ → ℕ → ℚ) (t : ℕ → ℕ → ℚ)
    (hcoef : ∀ j m, coef j m = (if j = r then F m else 0) - (if j = r' then F' m else 0)) :
    ∑ p ∈ Cert.vars n a, coef p.1 p.2 * t p.1 p.2 =
      ∑ m ∈ range (a + 1 - r), F m * t r m - ∑ m ∈ range (a + 1 - r'), F' m * t r' m := by
  simp only [hcoef, sub_mul, sum_sub_distrib]
  rw [sum_vars_ite hr, sum_vars_ite hr']

theorem binom_eq {b k : ℤ} {b' k' : ℕ} (hb : b = b') (hk : k = k') :
    Cert.binom b k = (b'.choose k' : ℚ) := by
  subst hb
  subst hk
  exact Cert.binom_natCast b' k'

/-! ### Counting lemmas for the rows -/

omit [Fintype V] [DecidableEq V] in
theorem indepCount_add_card_nonindep (S : Finset V) (r : ℕ) :
    indepCount G S r + ((S.powersetCard r).filter (fun J => ¬ IsIndepFinset G J)).card =
      S.card.choose r := by
  rw [indepCount_eq_card_filter, card_filter_add_card_filter_not, card_powersetCard]

omit [Fintype V] in
/-- The edge-count lower bound (Zhang (24)): `i_r ≥ C(v, r) − e C(v − 2, r − 2)`. -/
theorem choose_le_indepCount_add (S : Finset V) (r : ℕ) :
    S.card.choose r ≤ indepCount G S r + eIn G S * (S.card - 2).choose (r - 2) := by
  have h1 := indepCount_add_card_nonindep (G := G) S r
  have h2 := card_nonindep_le (G := G) S r
  omega

omit [DecidableRel G.Adj] in
theorem card_univ_sdiff_eq {I : Finset V} (hmax : I.card = G.indepNum) :
    (univ \ I).card = Cert.v (Fintype.card V) G.indepNum := by
  rw [card_univ_sdiff, hmax]
  rfl

end Forest

end Rows
end Zhang
end Erdos993Lean
