import Erdos993Lean.Analytic.O2.Ledger
import Erdos993Lean.Analytic.Reserve.Assembly
import Erdos993Lean.Analytic.Tail.Fallback
import Erdos993Lean.Analytic.Atlas.Profile

/-!
# O2 for every forest and for the certified profile

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A16).  Source: `PRO_R2_PROOF.md` Theorem 4
(`Var K ≤ c ∑ π g ≤ c J' ≤ c W` for every finite forest and every maximizing `B`), eq. (2) (the
competitor), and `LEAN_O2_IMPLEMENTATION_MAP.md` §2, obligation 6 (the wrapper; the empty forest and
all tied maximizers are covered by the same argument), §5 (the left-edge convention of `bandOf`).

* **`hardCoreVar_le_of_band`**: for every O2 band `b` with `b.OK` (sign guards, certified local
  payment, leaf endpoint, small messages), every finite forest `F`, every activity `λ ∈ [lo, hi]`
  and every maximum-weight independent set `B`: `Var K ≤ γ/(1 + λ) · W`.  No restriction on order,
  degree, height or connectedness.
* `guards_bands`: the sign guards of the 14 rows (kernel-checked on the rational tables).
* **`varianceRatioBound_profile30_of_ok`**: `VarianceRatioBound Profile30.P` from the three band
  propositions of the 14 O2 rows (`LocalPaymentOK`, `LeafOK`, `SmallMessageOK`); the price of the
  row containing `λ` is exactly `1 + θ(λ)` of `Profile30` (`γ = 2, 17/10, 8/5, 17/10, 2` on
  `[1/3, 3/5]`, `(3/5, 4/5]`, `(4/5, 13/10]`, `(13/10, 8/5]`, `(8/5, 7/3]`).

Scalarity check.  `θ(λ) = γ − 1` is the output (the bound on the second moment of `δ` through
`V ≤ (1 + θ)(1 − q) W`), produced by the actual payment ledger and consumed by `VarianceRatioBound`
(the no-valley lemma through `Profile30.P`); `W` is the weight of the given maximizer `B`.
-/

namespace Erdos993Lean.Analytic.O2

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve

/-! ### The forest theorem -/

section Forest

variable (F : FiniteForest)

theorem gMarg_eq_marginal [DecidableRel F.graph.Adj] (t : ℝ) (v : Fin F.n) :
    gMarg F.graph t v = marginal F t v := by
  rw [marginal_eq_marg F t v, marg_of_mem (Finset.mem_univ v)]
  rfl

/-- `Var K` of the whole forest is the total-count variance `varB univ univ`. -/
theorem hardCoreVar_eq_varB [DecidableRel F.graph.Adj] {t : ℝ} (ht : 0 ≤ t) :
    hardCoreVar F t = varB F.graph univ t univ := by
  rw [varB_univ_eq_varKB F univ ht, HardCore.varKB, HardCore.hardCoreVar_eq_sum]
  have hW : weightW F t univ = hardCoreMean F t := HardCore.sum_univ_marginal F t
  rw [hW]
  simp only [Finset.inter_univ]

/-- **O2 on one band, for every finite forest**: `Var K ≤ γ/(1 + λ) · W` for every activity of the
band and every maximum-weight independent set `B`. -/
theorem hardCoreVar_le_of_band {b : BandData} (hok : b.OK) (F : FiniteForest) {t : ℝ}
    (ht : b.InBand t) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ b.price t * weightW F t B := by
  classical
  have hl := ht.pos hok.guards
  have hc := b.price_nonneg hok.guards ht
  have hV := BandData.varB_le_closed hok ht F.isForest univ (fun _ _ w _ => Finset.mem_univ w)
  obtain ⟨I, -, hIi, hI⟩ := dp_closed (gMarg F.graph t) (sRef F.graph t) F.isForest
    (sRef_nonneg hl) (sRef_le_one hl) (fun u v huv => sRef_edge huv) univ
    (fun _ _ w _ => Finset.mem_univ w)
  have hIW : ∑ v ∈ I, gMarg F.graph t v ≤ weightW F t B := by
    rw [Finset.sum_congr rfl (fun v _ => gMarg_eq_marginal F t v)]
    exact hB.2 I ((HardCore.isIndepSet_coe_iff F).mpr hIi)
  rw [hardCoreVar_eq_varB F hl.le]
  calc varB F.graph univ t univ ≤ b.price t * ∑ v, gMarg F.graph t v * sRef F.graph t v := hV
    _ ≤ b.price t * weightW F t B := mul_le_mul_of_nonneg_left (hI.trans hIW) hc

end Forest

/-! ### The 14 rows -/

theorem guards_low : low.Guards := by decide +kernel
theorem guards_L1 : L1.Guards := by decide +kernel
theorem guards_L23 : L23.Guards := by decide +kernel
theorem guards_L4e : L4e.Guards := by decide +kernel
theorem guards_central0 : central0.Guards := by decide +kernel
theorem guards_central1 : central1.Guards := by decide +kernel
theorem guards_central2 : central2.Guards := by decide +kernel
theorem guards_central3 : central3.Guards := by decide +kernel
theorem guards_upperShoulder : upperShoulder.Guards := by decide +kernel
theorem guards_H1 : H1.Guards := by decide +kernel
theorem guards_H2b : H2b.Guards := by decide +kernel
theorem guards_H3b : H3b.Guards := by decide +kernel
theorem guards_H4b : H4b.Guards := by decide +kernel
theorem guards_H8 : H8.Guards := by decide +kernel

/-- The sign guards of the 14 rows. -/
theorem guards_bands : ∀ b ∈ bands, b.Guards := by
  intro b hb
  simp only [bands, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact guards_low
  · exact guards_L1
  · exact guards_L23
  · exact guards_L4e
  · exact guards_central0
  · exact guards_central1
  · exact guards_central2
  · exact guards_central3
  · exact guards_upperShoulder
  · exact guards_H1
  · exact guards_H2b
  · exact guards_H3b
  · exact guards_H4b
  · exact guards_H8

/-! ### The band table of `Profile30` -/

open Profile30 in
/-- Lean bands 0–5 lie in `[1/3, 3/5]` and have `θ = 1`. -/
theorem o2_bands0 : ∀ i < 30, i ≤ 5 →
    1 / 3 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 3 / 5 ∧ θt.getD i 1 = 1 := by
  decide +kernel

open Profile30 in
/-- Lean bands 6–9 lie in `[3/5, 4/5]` and have `θ = 7/10`. -/
theorem o2_bands1 : ∀ i < 30, 6 ≤ i → i ≤ 9 →
    3 / 5 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 4 / 5 ∧ θt.getD i 1 = 7 / 10 := by
  decide +kernel

open Profile30 in
/-- Lean bands 10–21 lie in `[4/5, 13/10]` and have `θ = 3/5`. -/
theorem o2_bands2 : ∀ i < 30, 10 ≤ i → i ≤ 21 →
    4 / 5 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 13 / 10 ∧ θt.getD i 1 = 3 / 5 := by
  decide +kernel

open Profile30 in
/-- Lean bands 22–24 lie in `[13/10, 8/5]` and have `θ = 7/10`. -/
theorem o2_bands3 : ∀ i < 30, 22 ≤ i → i ≤ 24 →
    13 / 10 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 8 / 5 ∧ θt.getD i 1 = 7 / 10 := by
  decide +kernel

open Profile30 in
/-- Lean bands 25–29 lie in `[8/5, 7/3]` and have `θ = 1`. -/
theorem o2_bands4 : ∀ i < 30, 25 ≤ i →
    8 / 5 ≤ edges.getD i 0 ∧ edges.getD (i + 1) 0 ≤ 7 / 3 ∧ θt.getD i 1 = 1 := by
  decide +kernel

/-- The price in the form of `VarianceRatioBound`: `γ/(1 + λ) = γ (1 − q)`. -/
theorem price_eq (b : BandData) {t : ℝ} (ht : 0 < t) : b.price t = (b.gamma : ℝ) * (1 - actQ t) := by
  unfold BandData.price actQ
  rw [one_sub_div (by linarith : (1 : ℝ) + t ≠ 0)]
  ring

/-- From a band containing `t` whose price is `1 + θ`: the O2 bound at `t`. -/
theorem vrb_of_band {b : BandData} (hok : b.OK) {F : FiniteForest} {t θ : ℝ} (ht : b.InBand t)
    (hθ : (b.gamma : ℝ) = 1 + θ) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (1 + θ) * (1 - actQ t) * weightW F t B := by
  have h := hardCoreVar_le_of_band hok F ht hB
  rw [price_eq b (ht.pos hok.guards), hθ] at h
  exact h

/-- **O2 for the certified profile** (`VarianceRatioBound Profile30.P`) from the three band
propositions of the 14 O2 rows.  The hypotheses `61 ≤ F.n` and `AtInteriorRank` are not used:
the bound holds for every forest, every activity in `[1/3, 7/3]` and every maximum-weight `B`. -/
theorem varianceRatioBound_profile30_of_ok (hpay : ∀ b ∈ bands, b.LocalPaymentOK)
    (hleaf : ∀ b ∈ bands, b.LeafOK) (hsmall : ∀ b ∈ bands, b.SmallMessageOK) :
    VarianceRatioBound Profile30.P := by
  have hok : ∀ b ∈ bands, b.OK := fun b hb =>
    ⟨guards_bands b hb, hpay b hb, hleaf b hb, hsmall b hb⟩
  have mem : ∀ b, b ∈ [low, L1, L23, L4e, central0, central1, central2, central3, upperShoulder,
      H1, H2b, H3b, H4b, H8] → b ∈ bands := fun b hb => hb
  intro F _ t ht _ B hB
  obtain ⟨hi, hlo, hhi⟩ := Atlas.bandOf_spec ht
  have hlo' : ((Profile30.edges.getD (Profile30.bandOf t) 0 : ℚ) : ℝ) ≤ t := hlo
  have hhi' : t ≤ ((Profile30.edges.getD (Profile30.bandOf t + 1) 0 : ℚ) : ℝ) := hhi
  have hθb : Profile30.P.θb t = ((Profile30.θt.getD (Profile30.bandOf t) 1 : ℚ) : ℝ) := rfl
  rw [hθb]
  rcases (show Profile30.bandOf t ≤ 5 ∨ (6 ≤ Profile30.bandOf t ∧ Profile30.bandOf t ≤ 9) ∨
      (10 ≤ Profile30.bandOf t ∧ Profile30.bandOf t ≤ 21) ∨
      (22 ≤ Profile30.bandOf t ∧ Profile30.bandOf t ≤ 24) ∨ 25 ≤ Profile30.bandOf t by omega)
    with h | h | h | h | h
  · obtain ⟨e1, e2, e3⟩ := o2_bands0 _ hi h
    rw [e3]
    have h1 : ((1 / 3 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((3 / 5 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    exact vrb_of_band (hok low (mem _ (by simp))) ⟨h1, h2⟩ (by norm_num [low]) hB
  · obtain ⟨e1, e2, e3⟩ := o2_bands1 _ hi h.1 h.2
    rw [e3]
    have h1 : ((3 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((4 / 5 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    by_cases c1 : t ≤ ((13 / 20 : ℚ) : ℝ)
    · exact vrb_of_band (hok L1 (mem _ (by simp))) ⟨h1, c1⟩ (by norm_num [L1]) hB
    by_cases c2 : t ≤ ((3 / 4 : ℚ) : ℝ)
    · exact vrb_of_band (hok L23 (mem _ (by simp))) ⟨(not_le.mp c1).le, c2⟩ (by norm_num [L23]) hB
    · exact vrb_of_band (hok L4e (mem _ (by simp))) ⟨(not_le.mp c2).le, h2⟩ (by norm_num [L4e]) hB
  · obtain ⟨e1, e2, e3⟩ := o2_bands2 _ hi h.1 h.2
    rw [e3]
    have h1 : ((4 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((13 / 10 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    by_cases c1 : t ≤ ((9 / 10 : ℚ) : ℝ)
    · exact vrb_of_band (hok central0 (mem _ (by simp))) ⟨h1, c1⟩ (by norm_num [central0]) hB
    by_cases c2 : t ≤ ((1 : ℚ) : ℝ)
    · exact vrb_of_band (hok central1 (mem _ (by simp))) ⟨(not_le.mp c1).le, c2⟩
        (by norm_num [central1]) hB
    by_cases c3 : t ≤ ((23 / 20 : ℚ) : ℝ)
    · exact vrb_of_band (hok central2 (mem _ (by simp))) ⟨(not_le.mp c2).le, c3⟩
        (by norm_num [central2]) hB
    · exact vrb_of_band (hok central3 (mem _ (by simp))) ⟨(not_le.mp c3).le, h2⟩
        (by norm_num [central3]) hB
  · obtain ⟨e1, e2, e3⟩ := o2_bands3 _ hi h.1 h.2
    rw [e3]
    have h1 : ((13 / 10 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((8 / 5 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    exact vrb_of_band (hok upperShoulder (mem _ (by simp))) ⟨h1, h2⟩
      (by norm_num [upperShoulder]) hB
  · obtain ⟨e1, e2, e3⟩ := o2_bands4 _ hi h
    rw [e3]
    have h1 : ((8 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((7 / 3 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    by_cases c1 : t ≤ ((17 / 10 : ℚ) : ℝ)
    · exact vrb_of_band (hok H1 (mem _ (by simp))) ⟨h1, c1⟩ (by norm_num [H1]) hB
    by_cases c2 : t ≤ ((19 / 10 : ℚ) : ℝ)
    · exact vrb_of_band (hok H2b (mem _ (by simp))) ⟨(not_le.mp c1).le, c2⟩ (by norm_num [H2b]) hB
    by_cases c3 : t ≤ ((21 / 10 : ℚ) : ℝ)
    · exact vrb_of_band (hok H3b (mem _ (by simp))) ⟨(not_le.mp c2).le, c3⟩ (by norm_num [H3b]) hB
    by_cases c4 : t ≤ ((9 / 4 : ℚ) : ℝ)
    · exact vrb_of_band (hok H4b (mem _ (by simp))) ⟨(not_le.mp c3).le, c4⟩ (by norm_num [H4b]) hB
    · exact vrb_of_band (hok H8 (mem _ (by simp))) ⟨(not_le.mp c4).le, h2⟩ (by norm_num [H8]) hB

end Erdos993Lean.Analytic.O2
