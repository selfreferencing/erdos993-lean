import Erdos993Lean.Analytic.O2.Knots
import Erdos993Lean.Analytic.O2.Basic

/-!
# O2: the small-message boundary (§7)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A16).  Source: `PRO_R2_PROOF.md` §7 ("Uniform
analytic small-`p` boundary"): with `ε = 2⁻¹⁶`, the rational guards
`u, v, s ≥ 0; sup u, v ≤ 1; sup s ≤ 4; |τ| ≤ 4; 0 ≤ w ≤ 2; ℓ ≥ 1/1000; u, v ≥ 1/100 on x ∈ [0, 1/8]`
give, for `0 < p ≤ ε` and every real response,
`Φ ≥ (A_* − 12)η² − 6|η| − 16 + 9/(1000 ε) > 0`, `η = z − 1`, `A_* = (1/100)/(pT)`.

* `BandData.SmallGuards`: the guards above plus `1/3 ≤ lo`, `hi ≤ 7/3`, `xmin ≤ 2⁻¹⁶` (decidable);
* the field bounds on the band: `lerp_bounds`, `pwLin_bounds`, `pwLin_first_ge`;
* the analytic bounds for `0 < p < 2⁻¹⁶`: `pT ≤ 1/1300` (`p log(4/p) ≤ ε(18 log 2 + 1)`),
  `G ≤ −9` (`e⁹ ≤ 8104`), `h ≤ 1`, `φ ≥ 0`, `H ≥ 0`;
* **`BandData.smallMessageOK_of_guards`**: `Guards` and `SmallGuards` give `SmallMessageOK`;
* the §7 guards of the 14 rows, kernel-checked (`smallGuards_low` …).
-/

namespace Erdos993Lean.Analytic.O2

/-! ### Bounds on the interpolated fields -/

theorem lerp_bounds {lo hi a b : ℚ} {m M lam : ℝ} (hlo : (lo : ℝ) ≤ lam) (hhi : lam ≤ hi)
    (ha1 : m ≤ (a : ℝ)) (ha2 : (a : ℝ) ≤ M) (hb1 : m ≤ (b : ℝ)) (hb2 : (b : ℝ) ≤ M) :
    m ≤ lerp lo hi a b lam ∧ lerp lo hi a b lam ≤ M := by
  unfold lerp
  rcases eq_or_lt_of_le (hlo.trans hhi) with heq | hlt
  · rw [← heq, sub_self, div_zero, zero_mul, add_zero]
    exact ⟨ha1, ha2⟩
  · have hθ0 : 0 ≤ (lam - lo) / ((hi : ℝ) - lo) := div_nonneg (by linarith) (by linarith)
    have hθ1 : (lam - lo) / ((hi : ℝ) - lo) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hb1 hθ0, mul_le_mul_of_nonneg_left ha1 (sub_nonneg.2 hθ1)]
    · nlinarith [mul_le_mul_of_nonneg_left hb2 hθ0, mul_le_mul_of_nonneg_left ha2 (sub_nonneg.2 hθ1)]

theorem exists_cell {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ k : ℕ, k < 8 ∧ (k : ℝ) / 8 ≤ x ∧ x ≤ ((k : ℝ) + 1) / 8 := by
  have h8 : 0 ≤ 8 * x := by linarith
  rcases le_or_gt ⌊8 * x⌋₊ 7 with h | h
  · refine ⟨⌊8 * x⌋₊, by omega, ?_, ?_⟩
    · have := Nat.floor_le h8
      linarith
    · have := Nat.lt_floor_add_one (8 * x)
      linarith
  · refine ⟨7, by norm_num, ?_, ?_⟩
    · have h7 : ((7 : ℕ) : ℝ) < (⌊8 * x⌋₊ : ℝ) := by exact_mod_cast h
      have := Nat.floor_le h8
      push_cast at h7 ⊢
      linarith
    · push_cast
      linarith

theorem pwLin_bounds {f : Fin 9 → ℝ} {m M x : ℝ} (hf1 : ∀ j, m ≤ f j) (hf2 : ∀ j, f j ≤ M)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : m ≤ pwLin f x ∧ pwLin f x ≤ M := by
  obtain ⟨k, hk, hk1, hk2⟩ := exists_cell hx0 hx1
  rw [pwLin_eq_cell f k hk hk1 hk2]
  have hθ0 : 0 ≤ 8 * x - k := by linarith
  have hθ1 : 8 * x - k ≤ 1 := by linarith
  have a1 := hf1 ⟨k, by omega⟩
  have a2 := hf2 ⟨k, by omega⟩
  have b1 := hf1 ⟨k + 1, by omega⟩
  have b2 := hf2 ⟨k + 1, by omega⟩
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left b1 hθ0, mul_le_mul_of_nonneg_left a1 (sub_nonneg.2 hθ1)]
  · nlinarith [mul_le_mul_of_nonneg_left b2 hθ0, mul_le_mul_of_nonneg_left a2 (sub_nonneg.2 hθ1)]

theorem pwLin_first_ge {f : Fin 9 → ℝ} {m x : ℝ} (h0 : m ≤ f 0) (h1 : m ≤ f 1) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 8) : m ≤ pwLin f x := by
  have := pwLin_eq_cell f 0 (by norm_num) (by simpa using hx0) (by simpa using hx1)
  rw [this]
  have hθ0 : 0 ≤ 8 * x - ((0 : ℕ) : ℝ) := by push_cast; linarith
  have hθ1 : 8 * x - ((0 : ℕ) : ℝ) ≤ 1 := by push_cast; linarith
  have e0 : f ⟨0, by omega⟩ = f 0 := rfl
  have e1 : f ⟨0 + 1, by omega⟩ = f 1 := rfl
  rw [e0, e1]
  nlinarith [mul_le_mul_of_nonneg_left h1 hθ0, mul_le_mul_of_nonneg_left h0 (sub_nonneg.2 hθ1)]

/-! ### The small-message guards -/

namespace BandData

variable (b : BandData)

/-- **The §7 guards** on the rational tables (decidable). -/
def SmallGuards : Prop :=
  1 / 3 ≤ b.lo ∧ b.hi ≤ 7 / 3 ∧ b.xmin ≤ 1 / 65536 ∧
    (∀ j, b.left.u j ≤ 1) ∧ (∀ j, b.right.u j ≤ 1) ∧ (∀ j, b.left.v j ≤ 1) ∧
    (∀ j, b.right.v j ≤ 1) ∧ (∀ j, b.left.s j ≤ 4) ∧ (∀ j, b.right.s j ≤ 4) ∧
    (∀ j, -4 ≤ b.left.tau j) ∧ (∀ j, b.left.tau j ≤ 4) ∧
    (∀ j, -4 ≤ b.right.tau j) ∧ (∀ j, b.right.tau j ≤ 4) ∧
    b.left.w ≤ 2 ∧ b.right.w ≤ 2 ∧ 1 / 1000 ≤ b.left.ell ∧ 1 / 1000 ≤ b.right.ell ∧
    1 / 100 ≤ b.left.u 0 ∧ 1 / 100 ≤ b.left.u 1 ∧ 1 / 100 ≤ b.right.u 0 ∧ 1 / 100 ≤ b.right.u 1 ∧
    1 / 100 ≤ b.left.v 0 ∧ 1 / 100 ≤ b.left.v 1 ∧ 1 / 100 ≤ b.right.v 0 ∧ 1 / 100 ≤ b.right.v 1

instance : Decidable b.SmallGuards := by unfold SmallGuards; infer_instance

end BandData

/-! ### Analytic bounds for small messages -/

section Analytic

theorem log_four_div_eps : Real.log (4 / (1 / 65536)) ≤ 25 / 2 := by
  have h : (4 : ℝ) / (1 / 65536) = 2 ^ 18 := by norm_num
  rw [h, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  linarith

/-- `p T ≤ 1/1300` for `0 < p < 2⁻¹⁶`, `λ ≤ 4`. -/
theorem p_mul_logMass_le {lam p : ℝ} (hl : 0 < lam) (hl4 : lam ≤ 4) (hp0 : 0 < p)
    (hpe : p < 1 / 65536) : p * logMass lam p ≤ 1 / 1300 := by
  have hp1 : p < 1 := by linarith
  -- T ≤ log(4/p)
  have hT : logMass lam p ≤ Real.log (4 / p) := by
    unfold logMass
    apply Real.log_le_log (by apply div_pos (mul_pos hl (by linarith)) hp0)
    apply div_le_div_of_nonneg_right _ hp0.le
    nlinarith
  -- log(4/p) = log(4/ε) + log(ε/p), and p log(ε/p) ≤ ε − p
  have hsplit : Real.log (4 / p) = Real.log (4 / (1 / 65536)) + Real.log ((1 / 65536) / p) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hq : Real.log ((1 / 65536) / p) ≤ (1 / 65536) / p - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hL0 : 0 ≤ Real.log (4 / (1 / 65536)) := Real.log_nonneg (by norm_num)
  have hLe := log_four_div_eps
  have h1 : p * Real.log (4 / p) ≤ (1 / 65536) * (25 / 2) + (1 / 65536) := by
    rw [hsplit, mul_add]
    have e : p * ((1 / 65536) / p - 1) = 1 / 65536 - p := by
      rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hp0.ne', mul_one]
    have h2 : p * Real.log ((1 / 65536) / p) ≤ 1 / 65536 - p := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hq hp0.le
    have h3 : p * Real.log (4 / (1 / 65536)) ≤ (1 / 65536) * (25 / 2) := by
      calc p * Real.log (4 / (1 / 65536)) ≤ (1 / 65536) * Real.log (4 / (1 / 65536)) :=
            mul_le_mul_of_nonneg_right hpe.le hL0
        _ ≤ (1 / 65536) * (25 / 2) := by linarith
    linarith
  calc p * logMass lam p ≤ p * Real.log (4 / p) := mul_le_mul_of_nonneg_left hT hp0.le
    _ ≤ (1 / 65536) * (25 / 2) + (1 / 65536) := h1
    _ ≤ 1 / 1300 := by norm_num

/-- `G ≤ −9` for `0 < p < 2⁻¹⁶`, `λ ≥ 1/3`. -/
theorem logG_le {lam p : ℝ} (hl : 1 / 3 ≤ lam) (hp0 : 0 < p) (hpe : p < 1 / 65536) :
    logG lam p ≤ -9 := by
  have hp1 : 0 < 1 - p := by linarith
  have hlam : 0 < lam := by linarith
  have hx : 0 < p / (lam * (1 - p) ^ 2) := by positivity
  unfold logG
  rw [Real.log_le_iff_le_exp hx]
  have he9 : Real.exp 9 ≤ 8104 := by
    have h1 : Real.exp 9 = Real.exp 1 ^ 9 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have h2 := Real.exp_one_lt_d9
    have h3 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 9 ≤ (2.7182818286 : ℝ) ^ 9 := pow_le_pow_left₀ h3 h2.le 9
      _ ≤ 8104 := by norm_num
  have hneg : Real.exp (-9) = 1 / Real.exp 9 := by rw [Real.exp_neg, one_div]
  rw [hneg, le_div_iff₀ (Real.exp_pos 9)]
  have hd : 0 < lam * (1 - p) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_one hd]
  have hsq : (1 - 1 / 65536 : ℝ) ^ 2 ≤ (1 - p) ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left he9 hp0.le, mul_le_mul hl hsq (by norm_num) hlam.le]

theorem hFun_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : hFun p ≤ 1 := by
  unfold hFun
  have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - p)
  rw [div_le_one (by linarith)]
  linarith

theorem logMass_nonneg {lam p : ℝ} (hl : 0 < lam) (hp0 : 0 < p) (hpq : p ≤ actQ lam) :
    0 ≤ logMass lam p := by
  unfold logMass
  apply Real.log_nonneg
  unfold actQ at hpq
  rw [le_div_iff₀ (by linarith)] at hpq
  rw [le_div_iff₀ hp0]
  nlinarith

theorem packRes_nonneg {lam p : ℝ} (hl : 0 < lam) (hp0 : 0 < p) (hpq : p ≤ actQ lam) :
    0 ≤ packRes lam p := by
  have hL : 0 < Real.log (1 + lam) := Real.log_pos (by linarith)
  have hT := logMass_nonneg hl hp0 hpq
  unfold packRes packJ
  have := Nat.floor_le (div_nonneg hT hL.le)
  rw [le_div_iff₀ hL] at this
  linarith

theorem packPhi_nonneg {lam p : ℝ} (hl : 0 < lam) (hp0 : 0 < p) (hpq : p ≤ actQ lam) :
    0 ≤ packPhi lam p := by
  have hres := packRes_nonneg hl hp0 hpq
  have hq : 0 ≤ actQ lam := by unfold actQ; positivity
  unfold packPhi
  have h1 : Real.exp (-packRes lam p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 0 ≤ (packJ lam p : ℝ) * actQ lam := mul_nonneg (Nat.cast_nonneg _) hq
  linarith

theorem packH_nonneg {lam p : ℝ} (hl : 0 < lam) (hp0 : 0 < p) (hpq : p ≤ actQ lam) :
    0 ≤ packH lam p := by
  have hres := packRes_nonneg hl hp0 hpq
  unfold packH
  have h1 : 1 ≤ Real.exp (packRes lam p) := Real.one_le_exp hres
  have h2 : 0 ≤ (packJ lam p : ℝ) * lam := mul_nonneg (Nat.cast_nonneg _) hl.le
  linarith

theorem src_nonneg {lam p r : ℝ} (hl : 0 < lam) (hp0 : 0 ≤ p) (hr0 : 0 ≤ r) : 0 ≤ src lam p r := by
  have hq : 0 < actQ lam := by unfold actQ; positivity
  unfold src
  exact le_trans (le_trans (div_nonneg (mul_nonneg (by linarith) (mul_nonneg hp0 hr0))
    (by linarith)) (le_max_left _ _)) (le_max_left _ _)

end Analytic

/-! ### The small-message theorem -/

theorem sq_max_add_sq_max (z : ℝ) : (max (z - 1) 0) ^ 2 + (max (1 - z) 0) ^ 2 = (z - 1) ^ 2 := by
  rcases le_total z 1 with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

theorem sq_max_add_sq_max' (z : ℝ) : (max (-z) 0) ^ 2 + (max z 0) ^ 2 = z ^ 2 := by
  rcases le_total z 0 with h | h
  · rw [max_eq_left (by linarith), max_eq_right h]; ring
  · rw [max_eq_right (by linarith), max_eq_left h]; ring

/-- The response quadratic of (15): `13 η² − 6 z² − 6|η| + 576 ≥ 0`, `η = z − 1`. -/
theorem quad_small (z : ℝ) : 0 ≤ 13 * (z - 1) ^ 2 - 6 * z ^ 2 - 6 * |z - 1| + 576 := by
  nlinarith [sq_abs (z - 1), neg_abs_le (z - 1), sq_nonneg (|z - 1| - 9 / 7)]

/-- Transport of a rational inequality to the reals, with the two sides identified. -/
theorem q2r_le {a b : ℚ} {x y : ℝ} (hx : (a : ℝ) = x) (hy : (b : ℝ) = y) (h : a ≤ b) : x ≤ y := by
  rw [← hx, ← hy]
  exact Rat.cast_le.mpr h

namespace BandData

variable {b : BandData}

set_option maxHeartbeats 1000000 in
/-- **The small-message boundary (§7)**: the sign guards and the §7 guards give `SmallMessageOK`. -/
theorem smallMessageOK_of_guards (hg : b.Guards) (hs : b.SmallGuards) : b.SmallMessageOK := by
  intro lam hlam p r t z hrec hp
  have hxpos : (0 : ℝ) < b.xmin := by exact_mod_cast hg.xmin_pos
  have hc : 0 ≤ b.price lam := b.price_nonneg hg hlam
  obtain ⟨hlo, hhi, hxm, hu1l, hu1r, hv1l, hv1r, hs4l, hs4r, hτ1l, hτ2l, hτ1r, hτ2r, hwl, hwr,
    hℓl, hℓr, hu0l, hu1l', hu0r, hu1r', hv0l, hv1l', hv0r, hv1r'⟩ := hs
  obtain ⟨-, -, -, -, -, hu0L, hu0R, hv0L, hv0R, hs0L, hs0R, hw0L, hw0R, hℓ0L, hℓ0R⟩ := hg
  have hl3 : 1 / 3 ≤ lam := le_trans (q2r_le (by norm_num) rfl hlo) hlam.1
  have hl7 : lam ≤ 7 / 3 := le_trans hlam.2 (q2r_le rfl (by norm_num) hhi)
  have hl : 0 < lam := by linarith
  have hq : 0 < actQ lam := by unfold actQ; positivity
  have hq1 : actQ lam < 1 := by unfold actQ; rw [div_lt_one (by linarith)]; linarith
  obtain ⟨hp0, hpq, hr1, hrt, htp, htr⟩ := id hrec
  have hxm' : (b.xmin : ℝ) ≤ 1 / 65536 := q2r_le rfl (by norm_num) hxm
  have hxq : (b.xmin : ℝ) * actQ lam ≤ 1 / 65536 := by
    have := mul_le_mul_of_nonneg_left hq1.le hxpos.le
    linarith
  have hpe : p < 1 / 65536 := by linarith
  have hp1 : p < 1 := by linarith
  have hden : 0 < 1 + lam * (1 - p) := by
    have := mul_pos hl (by linarith : (0 : ℝ) < 1 - p)
    linarith
  have htp' := htp
  rw [le_div_iff₀ hden] at htp'
  have hr0 : 0 < r := by
    by_contra h
    push_neg at h
    have h1 := mul_nonpos_of_nonpos_of_nonneg h hden.le
    have h2 := mul_le_mul_of_nonneg_right hrt hden.le
    linarith
  have ht0 : 0 ≤ t := by linarith
  have htq : t ≤ actQ lam := by
    refine htp.trans ?_
    unfold actQ
    rw [div_le_div_iff₀ hden (by linarith)]
    have := mul_pos hl hp0
    have := mul_pos (mul_pos hl hl) hp0
    linarith
  have hxp : p / actQ lam ≤ 1 / 8 := by
    rw [div_le_iff₀ hq]
    have : (b.xmin : ℝ) * actQ lam ≤ 1 / 65536 * actQ lam :=
      mul_le_mul_of_nonneg_right hxm' hq.le
    linarith
  have hy0 : 0 ≤ p / actQ lam := div_nonneg hp0.le hq.le
  have hy1 : p / actQ lam ≤ 1 := by linarith
  have ht0' : 0 ≤ t / actQ lam := div_nonneg ht0 hq.le
  have ht1' : t / actQ lam ≤ 1 := by rw [div_le_one hq]; exact htq
  -- field bounds
  have fb : ∀ (sel : CoeffTable → Fin 9 → ℚ) (m M : ℝ),
      (∀ j, m ≤ ((sel b.left j : ℚ) : ℝ)) → (∀ j, ((sel b.left j : ℚ) : ℝ) ≤ M) →
      (∀ j, m ≤ ((sel b.right j : ℚ) : ℝ)) → (∀ j, ((sel b.right j : ℚ) : ℝ) ≤ M) →
      ∀ y, 0 ≤ y / actQ lam → y / actQ lam ≤ 1 →
        m ≤ b.field sel lam y ∧ b.field sel lam y ≤ M := by
    intro sel m M h1 h2 h3 h4 y hy0 hy1
    exact pwLin_bounds (fun j => (lerp_bounds hlam.1 hlam.2 (h1 j) (h2 j) (h3 j) (h4 j)).1)
      (fun j => (lerp_bounds hlam.1 hlam.2 (h1 j) (h2 j) (h3 j) (h4 j)).2) hy0 hy1
  have hu_t := fb CoeffTable.u 0 1 (fun j => q2r_le (by norm_num) rfl (hu0L j))
    (fun j => q2r_le rfl (by norm_num) (hu1l j)) (fun j => q2r_le (by norm_num) rfl (hu0R j))
    (fun j => q2r_le rfl (by norm_num) (hu1r j)) t ht0' ht1'
  have hv_t := fb CoeffTable.v 0 1 (fun j => q2r_le (by norm_num) rfl (hv0L j))
    (fun j => q2r_le rfl (by norm_num) (hv1l j)) (fun j => q2r_le (by norm_num) rfl (hv0R j))
    (fun j => q2r_le rfl (by norm_num) (hv1r j)) t ht0' ht1'
  have hs_t := fb CoeffTable.s 0 4 (fun j => q2r_le (by norm_num) rfl (hs0L j))
    (fun j => q2r_le rfl (by norm_num) (hs4l j)) (fun j => q2r_le (by norm_num) rfl (hs0R j))
    (fun j => q2r_le rfl (by norm_num) (hs4r j)) t ht0' ht1'
  have hs_p := fb CoeffTable.s 0 4 (fun j => q2r_le (by norm_num) rfl (hs0L j))
    (fun j => q2r_le rfl (by norm_num) (hs4l j)) (fun j => q2r_le (by norm_num) rfl (hs0R j))
    (fun j => q2r_le rfl (by norm_num) (hs4r j)) p hy0 hy1
  have hτ_t := fb CoeffTable.tau (-4) 4 (fun j => q2r_le (by norm_num) rfl (hτ1l j))
    (fun j => q2r_le rfl (by norm_num) (hτ2l j)) (fun j => q2r_le (by norm_num) rfl (hτ1r j))
    (fun j => q2r_le rfl (by norm_num) (hτ2r j)) t ht0' ht1'
  have hτ_p := fb CoeffTable.tau (-4) 4 (fun j => q2r_le (by norm_num) rfl (hτ1l j))
    (fun j => q2r_le rfl (by norm_num) (hτ2l j)) (fun j => q2r_le (by norm_num) rfl (hτ1r j))
    (fun j => q2r_le rfl (by norm_num) (hτ2r j)) p hy0 hy1
  -- the first segment: u(p), v(p) ≥ 1/100
  have hu_first : 1 / 100 ≤ b.uF lam p := by
    refine pwLin_first_ge ?_ ?_ hy0 hxp
    · exact (lerp_bounds (M := 1) hlam.1 hlam.2 (q2r_le (by norm_num) rfl hu0l)
        (q2r_le rfl (by norm_num) (hu1l 0)) (q2r_le (by norm_num) rfl hu0r)
        (q2r_le rfl (by norm_num) (hu1r 0))).1
    · exact (lerp_bounds (M := 1) hlam.1 hlam.2 (q2r_le (by norm_num) rfl hu1l')
        (q2r_le rfl (by norm_num) (hu1l 1)) (q2r_le (by norm_num) rfl hu1r')
        (q2r_le rfl (by norm_num) (hu1r 1))).1
  have hv_first : 1 / 100 ≤ b.vF lam p := by
    refine pwLin_first_ge ?_ ?_ hy0 hxp
    · exact (lerp_bounds (M := 1) hlam.1 hlam.2 (q2r_le (by norm_num) rfl hv0l)
        (q2r_le rfl (by norm_num) (hv1l 0)) (q2r_le (by norm_num) rfl hv0r)
        (q2r_le rfl (by norm_num) (hv1r 0))).1
    · exact (lerp_bounds (M := 1) hlam.1 hlam.2 (q2r_le (by norm_num) rfl hv1l')
        (q2r_le rfl (by norm_num) (hv1l 1)) (q2r_le (by norm_num) rfl hv1r')
        (q2r_le rfl (by norm_num) (hv1r 1))).1
  -- multipliers
  have hw : 0 ≤ b.wF lam ∧ b.wF lam ≤ 2 :=
    lerp_bounds hlam.1 hlam.2 (q2r_le (by norm_num) rfl hw0L) (q2r_le rfl (by norm_num) hwl)
      (q2r_le (by norm_num) rfl hw0R) (q2r_le rfl (by norm_num) hwr)
  have hℓ : 1 / 1000 ≤ b.ellF lam :=
    (lerp_bounds (M := max (b.left.ell : ℝ) (b.right.ell : ℝ)) hlam.1 hlam.2
      (q2r_le (by norm_num) rfl hℓl) (le_max_left _ _) (q2r_le (by norm_num) rfl hℓr)
      (le_max_right _ _)).1
  -- analytic bounds
  have hT0 : 0 < logMass lam p := by
    unfold logMass
    apply Real.log_pos
    rw [lt_div_iff₀ hp0]
    have := mul_le_mul_of_nonneg_right hl3 (by linarith : (0 : ℝ) ≤ 1 - p)
    linarith
  have hpT0 : 0 < p * logMass lam p := mul_pos hp0 hT0
  have hpT := p_mul_logMass_le hl (by linarith) hp0 hpe
  have hh0 := hFun_nonneg hp0.le hp1
  have hh1 := hFun_le_one hp0 hp1
  have hG := logG_le hl3 hp0 hpe
  have hφ := packPhi_nonneg hl hp0 hpq
  have hH := packH_nonneg hl hp0 hpq
  have hsrc := src_nonneg hl hp0.le hr0.le
  -- the payment, term by term
  have hAB := sq_max_add_sq_max z
  have hCD := sq_max_add_sq_max' z
  have hA0 : 0 ≤ (max (z - 1) 0) ^ 2 := sq_nonneg _
  have hB0 : 0 ≤ (max (1 - z) 0) ^ 2 := sq_nonneg _
  have hC0 : 0 ≤ (max (-z) 0) ^ 2 := sq_nonneg _
  have hD0 : 0 ≤ (max z 0) ^ 2 := sq_nonneg _
  have h13 : 13 * (p * logMass lam p) ≤ 1 / 100 := by linarith
  have hown_u : 13 * (max (z - 1) 0) ^ 2 ≤
      b.uF lam p * (max (z - 1) 0) ^ 2 / (p * logMass lam p) := by
    rw [le_div_iff₀ hpT0]
    linarith [mul_le_mul_of_nonneg_right (h13.trans hu_first) hA0]
  have hown_v : 13 * (max (1 - z) 0) ^ 2 ≤
      b.vF lam p * (max (1 - z) 0) ^ 2 / (p * logMass lam p) := by
    rw [le_div_iff₀ hpT0]
    linarith [mul_le_mul_of_nonneg_right (h13.trans hv_first) hB0]
  have huh : b.uF lam t * hFun p ≤ 1 := mul_le_one₀ hu_t.2 hh0 hh1
  have hvh : b.vF lam t * hFun p ≤ 1 := mul_le_one₀ hv_t.2 hh0 hh1
  have hinc : b.uF lam t * hFun p * (max (-z) 0) ^ 2 + b.vF lam t * hFun p * (max z 0) ^ 2 ≤
      z ^ 2 := by
    linarith [mul_le_mul_of_nonneg_right huh hC0, mul_le_mul_of_nonneg_right hvh hD0]
  have hsown : 0 ≤ r * b.sF lam p * (1 - z) ^ 2 / packH lam p :=
    div_nonneg (mul_nonneg (mul_nonneg hr0.le hs_p.1) (sq_nonneg _)) hH
  have hsk : (1 - r) * b.sF lam t * (1 - p) ≤ 4 := by
    have k1 : (1 - r) * b.sF lam t ≤ 1 * 4 :=
      mul_le_mul (by linarith) hs_t.2 hs_t.1 (by norm_num)
    have k2 : (1 - r) * b.sF lam t * (1 - p) ≤ 1 * 4 * 1 :=
      mul_le_mul k1 (by linarith) (by linarith) (by norm_num)
    linarith
  have hsinc : (1 - r) * b.sF lam t * (1 - p) * z ^ 2 ≤ 4 * z ^ 2 :=
    mul_le_mul_of_nonneg_right hsk (sq_nonneg z)
  have hr1p : r * (1 - p) ≤ 1 := mul_le_one₀ hr1 (by linarith) (by linarith)
  have hvar : r * (1 - p) * z ^ 2 ≤ z ^ 2 := by
    have := mul_le_mul_of_nonneg_right hr1p (sq_nonneg z)
    linarith
  -- the signed terms
  have habsτp : |b.tauF lam p| ≤ 4 := abs_le.mpr ⟨hτ_p.1, hτ_p.2⟩
  have habsτt : |b.tauF lam t| ≤ 4 := abs_le.mpr ⟨hτ_t.1, hτ_t.2⟩
  have e1 : |r * b.tauF lam p * (z - 1)| ≤ 4 * r * |z - 1| := by
    rw [abs_mul, abs_mul, abs_of_pos hr0]
    have := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right habsτp (abs_nonneg (z - 1))) hr0.le
    linarith
  have e2 : |(1 - r) * b.tauF lam t * z| ≤ 4 * (1 - r) * |z| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - r)]
    have := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right habsτt (abs_nonneg z)) (by linarith : (0 : ℝ) ≤ 1 - r)
    linarith
  have e3 : |z| ≤ |z - 1| + 1 := by
    have := abs_add_le (z - 1) 1
    rw [sub_add_cancel, abs_one] at this
    exact this
  have e4 : 4 * (1 - r) * |z| ≤ 4 * (1 - r) * (|z - 1| + 1) :=
    mul_le_mul_of_nonneg_left e3 (by linarith)
  have hτ : -(4 * |z - 1|) - 4 ≤ r * b.tauF lam p * (z - 1) + (1 - r) * b.tauF lam t * z := by
    have n1 := neg_abs_le (r * b.tauF lam p * (z - 1))
    have n2 := neg_abs_le ((1 - r) * b.tauF lam t * z)
    have hra : 0 ≤ r * |z - 1| := mul_nonneg hr0.le (abs_nonneg _)
    linarith
  have hwt : -(2 * |z - 1|) ≤ b.wF lam * (z - 1 + r * packPhi lam p) := by
    have w1 : b.wF lam * (-|z - 1|) ≤ b.wF lam * (z - 1) :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) hw.1
    have w2 : b.wF lam * |z - 1| ≤ 2 * |z - 1| := mul_le_mul_of_nonneg_right hw.2 (abs_nonneg _)
    have w3 : 0 ≤ b.wF lam * (r * packPhi lam p) := mul_nonneg hw.1 (mul_nonneg hr0.le hφ)
    have w4 : b.wF lam * (z - 1 + r * packPhi lam p) =
        b.wF lam * (z - 1) + b.wF lam * (r * packPhi lam p) := by ring
    have w5 : b.wF lam * (-|z - 1|) = -(b.wF lam * |z - 1|) := by ring
    linarith
  have hℓG : b.ellF lam * logG lam p / p ≤ -580 := by
    rw [div_le_iff₀ hp0]
    have hℓ0 : 0 ≤ b.ellF lam := le_trans (by norm_num) hℓ
    have := mul_le_mul_of_nonneg_left hG hℓ0
    linarith
  have hsrc' : 0 ≤ b.price lam * r * src lam p r := mul_nonneg (mul_nonneg hc hr0.le) hsrc
  have hq := quad_small z
  unfold Phi Ru Rv Rs Rtau Rw
  linarith only [hsrc', hvar, hown_u, hown_v, hinc, hsown, hsinc, hτ, hwt, hℓG, hAB, hq]

end BandData

/-! ### The 14 rows -/

theorem smallGuards_low : low.SmallGuards := by decide +kernel
theorem smallGuards_L1 : L1.SmallGuards := by decide +kernel
theorem smallGuards_L23 : L23.SmallGuards := by decide +kernel
theorem smallGuards_L4e : L4e.SmallGuards := by decide +kernel
theorem smallGuards_central0 : central0.SmallGuards := by decide +kernel
theorem smallGuards_central1 : central1.SmallGuards := by decide +kernel
theorem smallGuards_central2 : central2.SmallGuards := by decide +kernel
theorem smallGuards_central3 : central3.SmallGuards := by decide +kernel
theorem smallGuards_upperShoulder : upperShoulder.SmallGuards := by decide +kernel
theorem smallGuards_H1 : H1.SmallGuards := by decide +kernel
theorem smallGuards_H2b : H2b.SmallGuards := by decide +kernel
theorem smallGuards_H3b : H3b.SmallGuards := by decide +kernel
theorem smallGuards_H4b : H4b.SmallGuards := by decide +kernel
theorem smallGuards_H8 : H8.SmallGuards := by decide +kernel

end Erdos993Lean.Analytic.O2
