import Erdos993Lean.Analytic.Reserve.Entropy

/-!
# Analytic bounds for the reserve tails

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A13 (O1 by the two-generation reserve).
Sources: `LEAN/referee/astra_o1/snapshot_0730/TWO_GENERATION_RESERVE_PROOF.md` ("PROVED: stronger tails
used by the final finite cover"), `SHARP_FIRST_FOUR_RESERVE_PROOF.md` ("Complete parent tail Y>=4",
"Complete child tail T>=6, Y<=4"), `LOWER_SHARP_ALTERNATE_PROOF.md`, and the referee's list of analytic
inputs (`LEAN/referee/REVIEW_ASTRA_O1_PROOF.md`, TASK 4; `review_proof/r4_tails_exact.py`).

The reusable inputs of the analytic tails, in namespace `Erdos993Lean.Analytic.Reserve.Tails`:

* exponential constants from `e > 2.7182818283`: `fifty_lt_exp_four` (`e⁴ > 50`),
  `four_hundred_lt_exp_six` (`e⁶ > 400`); `exp_neg_le_of_four_le`, `exp_neg_le_of_six_le`
  (`e^{−X} ≤ 1/50` for `X ≥ 4`, `≤ 1/400` for `X ≥ 6`);
* `mul_exp_neg_le`: `X e^{−X} ≤ a e^{−a}` for `1 ≤ a ≤ X` (`t e^{−t}` decreases on `[1, ∞)`), with
  `mul_exp_neg_le_of_four_le` (`≤ 4/50`) and `mul_exp_neg_le_of_six_le` (`≤ 6/400`);
* message and log-mass bounds, with `u = λ e^{−X}`: `p ≤ u` (`msg_le_lamExp`), `p (1 + u) = u`
  (`msg_mul_one_add`), `p ≤ y₀` (`msg_le_lmass`), `y₀ ≤ u` (`lmass_le_lamExp`), `u ≤ λ` for `X ≥ 0`
  (`lamExp_le`);
* coefficient bounds: `0 < H ≤ (1 + γ) p` (`coefH_pos`, `coefH_le`), `A p − H ≥ −γ p` when `A ≥ 1`
  (`capA_sub_coefH_ge`), `0 ≤ J ≤ λ T e^{−T}` (`coefJ_nonneg`, `coefJ_le`), `L ≥ −H Y` (`coefL_ge`),
  `E ≥ 1 − p − y₀/Y` (`coefE_ge_parent`), `E y ≥ p T − y₀` when `y ≤ Y` (`coefE_mul_ge_child`),
  `0 ≤ s/y ≤ 1` (`msg_div_lmass_nonneg`, `msg_div_lmass_le_one`);
* band parameters: `0 < q` (`actQ_pos`), `A ≥ 1` when `D ≥ 1` (`capA_ge_one`).

Scalarity: every quantity here is a function of the actual messages `p = msg λ Y` (parent) and
`s = msg λ T` (child) of one parent–child pair and of the band's coefficient profile; the bounds are
consumed only by the two generic tail comparisons (`Reserve/TailGeneric.lean`).
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

namespace Tails

open Entropy

/-! ### Exponential constants -/

/-- `e⁴ > 50`. -/
theorem fifty_lt_exp_four : (50 : ℝ) < exp 4 := by
  have h : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (50 : ℝ) < 2.7182818283 ^ 4 := by norm_num
    _ < exp 1 ^ 4 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

/-- `e⁶ > 400`. -/
theorem four_hundred_lt_exp_six : (400 : ℝ) < exp 6 := by
  have h : exp 6 = exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (400 : ℝ) < 2.7182818283 ^ 6 := by norm_num
    _ < exp 1 ^ 6 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

/-- `e^{−X} ≤ e^{−a} = 1 / e^a` for `a ≤ X`. -/
theorem exp_neg_le_inv {a X : ℝ} (h : a ≤ X) : exp (-X) ≤ (exp a)⁻¹ := by
  rw [← Real.exp_neg]; exact exp_le_exp.mpr (by linarith)

/-- `e^{−X} ≤ 1/50` for `X ≥ 4`. -/
theorem exp_neg_le_of_four_le {X : ℝ} (hX : 4 ≤ X) : exp (-X) ≤ 1 / 50 := by
  have h1 := exp_neg_le_inv hX
  have h2 : (exp 4)⁻¹ ≤ 1 / 50 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) fifty_lt_exp_four.le
  linarith

/-- `e^{−X} ≤ 1/400` for `X ≥ 6`. -/
theorem exp_neg_le_of_six_le {X : ℝ} (hX : 6 ≤ X) : exp (-X) ≤ 1 / 400 := by
  have h1 := exp_neg_le_inv hX
  have h2 : (exp 6)⁻¹ ≤ 1 / 400 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) four_hundred_lt_exp_six.le
  linarith

/-- `t e^{−t}` decreases on `[1, ∞)`: `X e^{−X} ≤ a e^{−a}` for `1 ≤ a ≤ X`. -/
theorem mul_exp_neg_le {a X : ℝ} (ha : 1 ≤ a) (h : a ≤ X) : X * exp (-X) ≤ a * exp (-a) := by
  have h0 : 0 ≤ (a - 1) * (X - a) := mul_nonneg (by linarith) (by linarith)
  have h1 : X ≤ a * (1 + (X - a)) := by nlinarith
  have h2 : 1 + (X - a) ≤ exp (X - a) := by linarith [Real.add_one_le_exp (X - a)]
  have h3 : exp (X - a) * exp (-X) = exp (-a) := by rw [← Real.exp_add]; ring_nf
  have hx : 0 ≤ exp (-X) := (exp_pos _).le
  calc X * exp (-X) ≤ a * (1 + (X - a)) * exp (-X) := mul_le_mul_of_nonneg_right h1 hx
    _ ≤ a * exp (X - a) * exp (-X) := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = a * exp (-a) := by rw [mul_assoc, h3]

/-- `X e^{−X} ≤ 4/50` for `X ≥ 4`. -/
theorem mul_exp_neg_le_of_four_le {X : ℝ} (hX : 4 ≤ X) : X * exp (-X) ≤ 4 / 50 := by
  have h1 := mul_exp_neg_le (by norm_num : (1 : ℝ) ≤ 4) hX
  have h2 := exp_neg_le_of_four_le (le_refl (4 : ℝ))
  linarith

/-- `X e^{−X} ≤ 6/400` for `X ≥ 6`. -/
theorem mul_exp_neg_le_of_six_le {X : ℝ} (hX : 6 ≤ X) : X * exp (-X) ≤ 6 / 400 := by
  have h1 := mul_exp_neg_le (by norm_num : (1 : ℝ) ≤ 6) hX
  have h2 := exp_neg_le_of_six_le (le_refl (6 : ℝ))
  linarith

/-! ### Messages and log-masses -/

variable {lam : ℝ}

/-- `p ≤ λ e^{−X}`. -/
theorem msg_le_lamExp (hlam : 0 < lam) (X : ℝ) : msg lam X ≤ lam * exp (-X) := by
  unfold msg
  have h := lamExp_pos hlam X
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `p (1 + λ e^{−X}) = λ e^{−X}`. -/
theorem msg_mul_one_add (hlam : 0 < lam) (X : ℝ) :
    msg lam X * (1 + lam * exp (-X)) = lam * exp (-X) := by
  unfold msg; have h := lamExp_pos hlam X; field_simp

/-- `y₀ ≤ λ e^{−X}` (`log (1 + x) ≤ x`). -/
theorem lmass_le_lamExp (hlam : 0 < lam) (X : ℝ) : lmass lam X ≤ lam * exp (-X) := by
  unfold lmass
  have h := lamExp_pos hlam X
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + lam * exp (-X) by linarith)
  linarith

/-- `p ≤ y₀` (`−log (1 − p) ≥ p`). -/
theorem msg_le_lmass (hlam : 0 < lam) (X : ℝ) : msg lam X ≤ lmass lam X := by
  have h1 := log_one_sub_msg hlam X
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 1 - msg lam X by linarith [msg_lt_one hlam X])
  linarith

/-- `λ e^{−X} ≤ λ` for `X ≥ 0`. -/
theorem lamExp_le (hlam : 0 < lam) {X : ℝ} (hX : 0 ≤ X) : lam * exp (-X) ≤ lam := by
  have h : exp (-X) ≤ exp 0 := exp_le_exp.mpr (by linarith)
  rw [exp_zero] at h
  nlinarith

/-- `y₀ ≤ (1 + λ) p` for `X ≥ 0`. -/
theorem lmass_le_one_add_mul_msg (hlam : 0 < lam) {X : ℝ} (hX : 0 ≤ X) :
    lmass lam X ≤ (1 + lam) * msg lam X := by
  have h1 := lmass_le_lamExp hlam X
  have h2 := msg_mul_one_add hlam X
  have h3 := lamExp_le hlam hX
  have h4 := msg_pos hlam X
  nlinarith

theorem msg_div_lmass_nonneg (hlam : 0 < lam) (X : ℝ) : 0 ≤ msg lam X / lmass lam X :=
  div_nonneg (msg_pos hlam X).le (lmass_pos hlam X).le

theorem msg_div_lmass_le_one (hlam : 0 < lam) (X : ℝ) : msg lam X / lmass lam X ≤ 1 := by
  rw [div_le_one (lmass_pos hlam X)]; exact msg_le_lmass hlam X

/-! ### The coefficients of the comparisons -/

variable (c : Band)

theorem actQ_pos (hlam : 0 < lam) : 0 < actQ lam := by unfold actQ; positivity

/-- `A = 1 + (D − 1) q ≥ 1` when `D ≥ 1`. -/
theorem capA_ge_one (hD : 1 ≤ (c.D : ℝ)) (hlam : 0 < lam) : 1 ≤ capA c lam := by
  unfold capA; have := actQ_pos hlam; nlinarith

theorem coefH_pos (hlam : 0 < lam) (hγ : 0 ≤ gamma c lam) (Y : ℝ) : 0 < coefH c lam Y := by
  unfold coefH
  have hp := msg_pos hlam Y; have hp1 := msg_lt_one hlam Y; have hy := lmass_pos hlam Y
  have h1 : 0 < msg lam Y * (1 - msg lam Y) := mul_pos hp (by linarith)
  have h2 : 0 ≤ gamma c lam * msg lam Y ^ 2 / lmass lam Y := by positivity
  linarith

/-- `H ≤ (1 + γ) p`. -/
theorem coefH_le (hlam : 0 < lam) (hγ : 0 ≤ gamma c lam) (Y : ℝ) :
    coefH c lam Y ≤ (1 + gamma c lam) * msg lam Y := by
  unfold coefH
  have hp := msg_pos hlam Y; have hy := lmass_pos hlam Y; have hpy := msg_le_lmass hlam Y
  have h1 : msg lam Y ^ 2 / lmass lam Y ≤ msg lam Y := by
    rw [div_le_iff₀ hy]; nlinarith
  have h2 : gamma c lam * (msg lam Y ^ 2 / lmass lam Y) ≤ gamma c lam * msg lam Y :=
    mul_le_mul_of_nonneg_left h1 hγ
  have h3 : gamma c lam * msg lam Y ^ 2 / lmass lam Y =
      gamma c lam * (msg lam Y ^ 2 / lmass lam Y) := by ring
  nlinarith [sq_nonneg (msg lam Y)]

/-- `A p − H ≥ −γ p` when `A ≥ 1`. -/
theorem capA_sub_coefH_ge (hlam : 0 < lam) (hγ : 0 ≤ gamma c lam) (hA : 1 ≤ capA c lam)
    (Y : ℝ) : -(gamma c lam * msg lam Y) ≤ capA c lam * msg lam Y - coefH c lam Y := by
  have h1 := coefH_le c hlam hγ Y
  have hp := msg_pos hlam Y
  have h2 : msg lam Y ≤ capA c lam * msg lam Y := by nlinarith
  linarith

/-- `L ≥ −H Y`. -/
theorem coefL_ge (hlam : 0 < lam) (hγ : 0 ≤ gamma c lam) (Y : ℝ) :
    -(coefH c lam Y * Y) ≤ coefL c lam Y := by
  unfold coefL
  have := msg_lt_one hlam Y
  have : 0 ≤ gamma c lam * (1 - msg lam Y) := mul_nonneg hγ (by linarith)
  linarith

theorem coefJ_nonneg (hlam : 0 < lam) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ coefJ lam T := by
  unfold coefJ; have := lmass_pos hlam T; positivity

/-- `J = s² T / y ≤ s T ≤ λ T e^{−T}`. -/
theorem coefJ_le (hlam : 0 < lam) {T : ℝ} (hT : 0 ≤ T) : coefJ lam T ≤ lam * (T * exp (-T)) := by
  unfold coefJ
  have hs := msg_pos hlam T; have hy := lmass_pos hlam T; have hsy := msg_le_lmass hlam T
  have hsu := msg_le_lamExp hlam T
  rw [div_le_iff₀ hy]
  have h1 : msg lam T ^ 2 ≤ lam * exp (-T) * lmass lam T := by nlinarith
  calc msg lam T ^ 2 * T ≤ lam * exp (-T) * lmass lam T * T := mul_le_mul_of_nonneg_right h1 hT
    _ = lam * (T * exp (-T)) * lmass lam T := by ring

/-- `E ≥ 1 − p − y₀ / Y` (for `T ≥ 0`). -/
theorem coefE_ge_parent (hlam : 0 < lam) {T Y : ℝ} (hT : 0 ≤ T) :
    1 - msg lam Y - lmass lam Y / Y ≤ coefE lam T Y := by
  unfold coefE
  have := msg_pos hlam Y; have := lmass_pos hlam T
  have : 0 ≤ msg lam Y * T / lmass lam T := by positivity
  linarith

/-- `E y ≥ p T − y₀` (for `y ≤ Y`). -/
theorem coefE_mul_ge_child (hlam : 0 < lam) {T Y : ℝ} (hTY : lmass lam T ≤ Y) :
    msg lam Y * T - lmass lam Y ≤ coefE lam T Y * lmass lam T := by
  have hy := lmass_pos hlam T
  have hY : 0 < Y := lt_of_lt_of_le hy hTY
  have hid : coefE lam T Y * lmass lam T = lmass lam T * (1 - msg lam Y) + msg lam Y * T -
      lmass lam Y * (lmass lam T / Y) := by
    unfold coefE; field_simp
  have h1 : lmass lam T / Y ≤ 1 := by rw [div_le_one hY]; exact hTY
  have h2 : 0 ≤ lmass lam T * (1 - msg lam Y) :=
    mul_nonneg hy.le (by linarith [msg_lt_one hlam Y])
  have h3 : lmass lam Y * (lmass lam T / Y) ≤ lmass lam Y := by
    have := lmass_pos hlam Y
    calc lmass lam Y * (lmass lam T / Y) ≤ lmass lam Y * 1 := mul_le_mul_of_nonneg_left h1 this.le
      _ = lmass lam Y := mul_one _
  linarith

end Tails

end Erdos993Lean.Analytic.Reserve
