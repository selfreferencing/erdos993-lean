import Erdos993Lean.Analytic.Reserve.AnalyticBounds

/-!
# The two generic analytic tails of the reserve comparisons

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A13 (O1 by the two-generation reserve).
Sources: `LEAN/referee/astra_o1/snapshot_0730/TWO_GENERATION_RESERVE_PROOF.md` ("PROVED: stronger tails
used by the final finite cover", the 4/6 split), `SHARP_FIRST_FOUR_RESERVE_PROOF.md` ("Complete parent
tail Y>=4", "Complete child tail T>=6, Y<=4"), `LOWER_SHARP_ALTERNATE_PROOF.md`; referee check
`LEAN/referee/REVIEW_ASTRA_O1_PROOF.md`, TASK 4.

Both tails are proved for an arbitrary band `c` from four rational envelopes of its coefficient
profile on the band — `λ ≤ Λ`, `λ ≤ R γ` (i.e. `λ/γ ≤ R`), `γ ≤ Γ`, `α ≥ α₀ ≥ 0` — and `A ≥ 1`.
The written chains are followed in a form that uses `A` only through `A p − H ≥ −γ p`
(`capA_sub_coefH_ge`), so one statement serves the sharp bands and the lower band alike.

* `compOK_parent` (`Y ≥ 4`, every `T ≥ 0`): `p ≤ λ e^{−Y} ≤ λ/50`, `p Y ≤ 4λ/50`, `y₀ ≤ λ/50`
  (`parent_small`); `L ≥ γ ℓ > 0` with `ℓ = 1 − Λ/50 − (R + Λ)(2/25)` (`parent_coefL_ge`), so (Q0)
  and (QC) hold; `E ≥ 1 − Λ/40` (`parent_coefE_ge`), `(A p − H)/Y ≥ −Γ Λ/200` (`parent_capA_ge`)
  and `H² J/Z ≤ H²/L ≤ (1 + Γ)² Λ R/(2500 ℓ)` (`parent_square_le`), so (QB) holds when
  `Γ Λ/200 + (1 + Γ)² Λ R/(2500 ℓ) ≤ α₀ (1 − Λ/40)`.
* `compOK_child` (`T ≥ 6`, `y ≤ Y ≤ 4`): `y ≤ λ/400`, `J ≤ λ T e^{−T} ≤ 3λ/200` (`child_small`);
  `Z ≥ p γ κ` with `κ = 1 − (3/50)(1 + Γ) R > 0` (`child_coefZ_ge`); `E y ≥ p T − y₀ ≥ p (5 − Λ)`
  (`child_coefE_ge`); if `L < 0` then `p γ L (s/y)²/Z ≥ −W p` with `W = α₀ (5 − Λ)(400/Λ)` when
  `4 (1 + Γ) ≤ W κ` (`child_compC_nonneg`); `α E + (A p − H)/Y ≥ W' p` and `H² J/Z ≤ W' p` with
  `W' = (α₀ (5 − Λ) − Γ)(400/Λ)` when `(1 + Γ)² (3R/200) ≤ W' κ` (`child_compB_nonneg`).

Scalarity: `Λ, R, Γ, α₀` are envelopes of the band's coefficient profile (inputs, fixed per band in
`Reserve/Tail.lean`); `ℓ, κ, W, W'` and the margins are outputs of these chains; `p, y₀, s, y, T, Y`
are the actual parent–child messages and log-masses. The consumer is the tree induction (lane A11)
through `TailOK`.
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

namespace Tails

open Entropy

variable {lam : ℝ}

/-! ### The parent tail `Y ≥ 4` -/

/-- On the parent tail the parent message and log-mass are small: `p ≤ λ/50`, `p Y ≤ 4λ/50`,
`y₀ ≤ λ/50`. -/
theorem parent_small (hlam : 0 < lam) {Y : ℝ} (hY : 4 ≤ Y) :
    msg lam Y ≤ lam / 50 ∧ msg lam Y * Y ≤ lam * (4 / 50) ∧ lmass lam Y ≤ lam / 50 := by
  have he := exp_neg_le_of_four_le hY
  have heY := mul_exp_neg_le_of_four_le hY
  have hpu := msg_le_lamExp hlam Y
  have hyu := lmass_le_lamExp hlam Y
  have h1 : lam * exp (-Y) ≤ lam * (1 / 50) := mul_le_mul_of_nonneg_left he hlam.le
  have h2 : msg lam Y * Y ≤ lam * exp (-Y) * Y := mul_le_mul_of_nonneg_right hpu (by linarith)
  have h3 : lam * (Y * exp (-Y)) ≤ lam * (4 / 50) := mul_le_mul_of_nonneg_left heY hlam.le
  have h4 : lam * exp (-Y) * Y = lam * (Y * exp (-Y)) := by ring
  exact ⟨by linarith, by linarith, by linarith⟩

variable (c : Band)

/-- On the parent tail `L ≥ γ ℓ`, `ℓ = 1 − Λ/50 − (R + Λ)(2/25)`. -/
theorem parent_coefL_ge (hlam : 0 < lam) {Y Λ R : ℝ} (hY : 4 ≤ Y) (hΛ : lam ≤ Λ)
    (hR : lam ≤ R * gamma c lam) (hγ : 0 < gamma c lam) :
    gamma c lam * (1 - Λ / 50 - (R + Λ) * (2 / 25)) ≤ coefL c lam Y := by
  obtain ⟨hp50, hpY, -⟩ := parent_small hlam hY
  have hH := coefH_le c hlam hγ.le Y
  have hLdef : coefL c lam Y = gamma c lam * (1 - msg lam Y) - coefH c lam Y * Y := rfl
  have h1 : coefH c lam Y * Y ≤ (1 + gamma c lam) * msg lam Y * Y :=
    mul_le_mul_of_nonneg_right hH (by linarith)
  have h2 : (1 + gamma c lam) * (msg lam Y * Y) ≤ (1 + gamma c lam) * (lam * (4 / 50)) :=
    mul_le_mul_of_nonneg_left hpY (by linarith)
  have h3 : gamma c lam * lam ≤ gamma c lam * Λ := mul_le_mul_of_nonneg_left hΛ hγ.le
  have h4 : gamma c lam * msg lam Y ≤ gamma c lam * (lam / 50) :=
    mul_le_mul_of_nonneg_left hp50 hγ.le
  rw [hLdef]
  linarith

/-- On the parent tail `E ≥ 1 − Λ/40`. -/
theorem parent_coefE_ge (hlam : 0 < lam) {T Y Λ : ℝ} (hT : 0 ≤ T) (hY : 4 ≤ Y)
    (hΛ : lam ≤ Λ) : 1 - Λ / 40 ≤ coefE lam T Y := by
  obtain ⟨hp50, -, hy50⟩ := parent_small hlam hY
  have hE1 := coefE_ge_parent hlam (Y := Y) hT
  have hy0 := lmass_pos hlam Y
  have h1 : lmass lam Y / Y ≤ lmass lam Y / 4 :=
    div_le_div_of_nonneg_left hy0.le (by norm_num) hY
  linarith

/-- On the parent tail `(A p − H)/Y ≥ −Γ Λ/200`. -/
theorem parent_capA_ge (hlam : 0 < lam) {Y Λ Γ : ℝ} (hY : 4 ≤ Y) (hΛ : lam ≤ Λ)
    (hγ : 0 < gamma c lam) (hΓ : gamma c lam ≤ Γ) (hA : 1 ≤ capA c lam) :
    -(Γ * Λ / 200) ≤ (capA c lam * msg lam Y - coefH c lam Y) / Y := by
  obtain ⟨hp50, -, -⟩ := parent_small hlam hY
  have hAH := capA_sub_coefH_ge c hlam hγ.le hA Y
  have hp0 := msg_pos hlam Y
  have hΓ0 : 0 ≤ Γ := by linarith
  have hY0 : 0 < Y := by linarith
  rw [le_div_iff₀ hY0]
  have h1 : gamma c lam * msg lam Y ≤ Γ * (Λ / 50) :=
    mul_le_mul hΓ (by linarith) hp0.le hΓ0
  have h2 : Γ * (Λ / 50) * 4 ≤ Γ * (Λ / 50) * Y :=
    mul_le_mul_of_nonneg_left hY (mul_nonneg hΓ0 (by linarith))
  linarith

/-- On the parent tail `H² J / Z ≤ H²/L ≤ (1 + Γ)² Λ R / (2500 ℓ)`. -/
theorem parent_square_le (hlam : 0 < lam) {T Y Λ R Γ : ℝ} (hT : 0 ≤ T) (hY : 4 ≤ Y)
    (hΛ : lam ≤ Λ) (hR : lam ≤ R * gamma c lam) (hγ : 0 < gamma c lam) (hΓ : gamma c lam ≤ Γ)
    (hℓ : 0 < 1 - Λ / 50 - (R + Λ) * (2 / 25)) :
    coefH c lam Y ^ 2 * coefJ lam T / coefZ c lam T Y ≤
      (1 + Γ) ^ 2 * Λ * R / (2500 * (1 - Λ / 50 - (R + Λ) * (2 / 25))) := by
  obtain ⟨hp50, -, -⟩ := parent_small hlam hY
  have hp0 := msg_pos hlam Y
  have hΛ0 : 0 ≤ Λ := by linarith
  have hH := coefH_le c hlam hγ.le Y
  have hH0 := coefH_pos c hlam hγ.le Y
  have hJ0 : 0 ≤ coefJ lam T := coefJ_nonneg hlam hT
  have hL := parent_coefL_ge c hlam hY hΛ hR hγ
  have hγℓ := mul_pos hγ hℓ
  have hL0 : 0 < coefL c lam Y := lt_of_lt_of_le hγℓ hL
  have hZdef : coefZ c lam T Y = msg lam Y * gamma c lam + coefL c lam Y * coefJ lam T := rfl
  have hpγ : 0 < msg lam Y * gamma c lam := mul_pos hp0 hγ
  have hLJ : 0 ≤ coefL c lam Y * coefJ lam T := mul_nonneg hL0.le hJ0
  have hZLJ : coefL c lam Y * coefJ lam T ≤ coefZ c lam T Y := by rw [hZdef]; linarith
  have hZ0 : 0 < coefZ c lam T Y := by rw [hZdef]; linarith
  have s1 : coefH c lam Y ^ 2 * coefJ lam T / coefZ c lam T Y ≤
      coefH c lam Y ^ 2 / (gamma c lam * (1 - Λ / 50 - (R + Λ) * (2 / 25))) := by
    rw [div_le_div_iff₀ hZ0 hγℓ]
    have h1 : coefH c lam Y ^ 2 * (coefL c lam Y * coefJ lam T) ≤
        coefH c lam Y ^ 2 * coefZ c lam T Y :=
      mul_le_mul_of_nonneg_left hZLJ (sq_nonneg _)
    have h2 : coefH c lam Y ^ 2 * coefJ lam T *
          (gamma c lam * (1 - Λ / 50 - (R + Λ) * (2 / 25))) ≤
        coefH c lam Y ^ 2 * coefJ lam T * coefL c lam Y :=
      mul_le_mul_of_nonneg_left hL (mul_nonneg (sq_nonneg _) hJ0)
    linarith
  have s2 : coefH c lam Y ^ 2 / (gamma c lam * (1 - Λ / 50 - (R + Λ) * (2 / 25))) ≤
      (1 + Γ) ^ 2 * Λ * R / (2500 * (1 - Λ / 50 - (R + Λ) * (2 / 25))) := by
    rw [div_le_div_iff₀ hγℓ (mul_pos (by norm_num) hℓ)]
    have e1 : coefH c lam Y ^ 2 ≤ ((1 + gamma c lam) * msg lam Y) ^ 2 :=
      pow_le_pow_left₀ hH0.le hH 2
    have e2 : (1 + gamma c lam) * msg lam Y ≤ (1 + Γ) * (lam / 50) :=
      mul_le_mul (by linarith) hp50 hp0.le (by linarith)
    have e3 : ((1 + gamma c lam) * msg lam Y) ^ 2 ≤ ((1 + Γ) * (lam / 50)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hp0.le) e2 2
    have e4 : lam * lam ≤ Λ * (R * gamma c lam) := mul_le_mul hΛ hR hlam.le hΛ0
    have h6 : 2500 * ((1 + Γ) * (lam / 50)) ^ 2 = (1 + Γ) ^ 2 * (lam * lam) := by ring
    have h7 := mul_le_mul_of_nonneg_left e4 (sq_nonneg (1 + Γ))
    have e5 : 2500 * coefH c lam Y ^ 2 ≤ (1 + Γ) ^ 2 * (Λ * (R * gamma c lam)) := by linarith
    have e6 := mul_le_mul_of_nonneg_right e5 hℓ.le
    linarith
  linarith

/-- **The generic parent tail** `Y ≥ 4` (every `T ≥ 0`): the three comparisons from rational
envelopes `λ ≤ Λ`, `λ ≤ R γ`, `0 < γ ≤ Γ`, `α ≥ α₀ ≥ 0`, `A ≥ 1` and two rational conditions. -/
theorem compOK_parent {lam T Y Λ R Γ α₀ : ℝ}
    (hlam : 0 < lam) (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) (hY : 4 ≤ Y)
    (hΛ : lam ≤ Λ) (hR : lam ≤ R * gamma c lam) (hγ : 0 < gamma c lam)
    (hΓ : gamma c lam ≤ Γ) (hα : α₀ ≤ alpha c lam) (hα₀ : 0 ≤ α₀) (hA : 1 ≤ capA c lam)
    (hℓ : 0 < 1 - Λ / 50 - (R + Λ) * (2 / 25))
    (hm : Γ * Λ / 200 + (1 + Γ) ^ 2 * Λ * R / (2500 * (1 - Λ / 50 - (R + Λ) * (2 / 25))) ≤
      α₀ * (1 - Λ / 40)) :
    CompOK c lam T Y := by
  have hp0 := msg_pos hlam Y
  have hL := parent_coefL_ge c hlam hY hΛ hR hγ
  have hL0 : 0 < coefL c lam Y := lt_of_lt_of_le (mul_pos hγ hℓ) hL
  have hJ0 : 0 ≤ coefJ lam T := coefJ_nonneg hlam hT
  have hZdef : coefZ c lam T Y = msg lam Y * gamma c lam + coefL c lam Y * coefJ lam T := rfl
  have hpγ : 0 < msg lam Y * gamma c lam := mul_pos hp0 hγ
  have hLJ : 0 ≤ coefL c lam Y * coefJ lam T := mul_nonneg hL0.le hJ0
  have hZ0 : 0 < coefZ c lam T Y := by rw [hZdef]; linarith
  have hE := parent_coefE_ge hlam hT hY hΛ
  have hE0 : 0 ≤ coefE lam T Y := (entropyOK lam T Y hlam hT hTY).1
  have k1 : α₀ * (1 - Λ / 40) ≤ α₀ * coefE lam T Y := mul_le_mul_of_nonneg_left hE hα₀
  have k2 : α₀ * coefE lam T Y ≤ alpha c lam * coefE lam T Y :=
    mul_le_mul_of_nonneg_right hα hE0
  have hB2 := parent_capA_ge c hlam hY hΛ hγ hΓ hA
  have hB3 := parent_square_le c hlam hT hY hΛ hR hγ hΓ hℓ
  refine ⟨hZ0, Or.inl hL0.le, ?_⟩
  show 0 ≤ alpha c lam * coefE lam T Y + (capA c lam * msg lam Y - coefH c lam Y) / Y -
      coefH c lam Y ^ 2 * coefJ lam T / coefZ c lam T Y
  linarith

/-! ### The child tail `T ≥ 6`, `Y ≤ 4` -/

omit c in
/-- On the child tail the child log-mass and the grandchild weight are small: `y ≤ λ/400` and
`J ≤ 3λ/200`. -/
theorem child_small (hlam : 0 < lam) {T : ℝ} (hT : 6 ≤ T) :
    lmass lam T ≤ lam / 400 ∧ coefJ lam T ≤ 3 * lam / 200 := by
  have he := exp_neg_le_of_six_le hT
  have heT := mul_exp_neg_le_of_six_le hT
  have hyu := lmass_le_lamExp hlam T
  have hJ := coefJ_le hlam (by linarith : (0 : ℝ) ≤ T)
  have h1 : lam * exp (-T) ≤ lam * (1 / 400) := mul_le_mul_of_nonneg_left he hlam.le
  have h2 : lam * (T * exp (-T)) ≤ lam * (6 / 400) := mul_le_mul_of_nonneg_left heT hlam.le
  exact ⟨by linarith, by linarith⟩

/-- On the child tail `Z ≥ p γ κ`, `κ = 1 − (3/50)(1 + Γ) R`. -/
theorem child_coefZ_ge (hlam : 0 < lam) {T Y R Γ : ℝ} (hT : 6 ≤ T) (hY : Y ≤ 4)
    (hR : lam ≤ R * gamma c lam) (hγ : 0 < gamma c lam) (hΓ : gamma c lam ≤ Γ) :
    msg lam Y * gamma c lam * (1 - 3 / 50 * (1 + Γ) * R) ≤ coefZ c lam T Y := by
  obtain ⟨-, hJ3⟩ := child_small hlam hT
  have hp0 := msg_pos hlam Y
  have hJ0 : 0 ≤ coefJ lam T := coefJ_nonneg hlam (by linarith)
  have hH := coefH_le c hlam hγ.le Y
  have hH0 := coefH_pos c hlam hγ.le Y
  have hLge := coefL_ge c hlam hγ.le Y
  have h1 : coefH c lam Y * Y ≤ coefH c lam Y * 4 := mul_le_mul_of_nonneg_left hY hH0.le
  have hL4 : -(4 * ((1 + gamma c lam) * msg lam Y)) ≤ coefL c lam Y := by linarith
  have hZdef : coefZ c lam T Y = msg lam Y * gamma c lam + coefL c lam Y * coefJ lam T := rfl
  have h2 : -(4 * ((1 + gamma c lam) * msg lam Y)) * coefJ lam T ≤
      coefL c lam Y * coefJ lam T :=
    mul_le_mul_of_nonneg_right hL4 hJ0
  have hJR : coefJ lam T ≤ 3 / 200 * (R * gamma c lam) := by linarith
  have h3 : (1 + gamma c lam) * coefJ lam T ≤ (1 + Γ) * (3 / 200 * (R * gamma c lam)) :=
    mul_le_mul (by linarith) hJR hJ0 (by linarith)
  have h4 : msg lam Y * ((1 + gamma c lam) * coefJ lam T) ≤
      msg lam Y * ((1 + Γ) * (3 / 200 * (R * gamma c lam))) :=
    mul_le_mul_of_nonneg_left h3 hp0.le
  rw [hZdef]
  linarith

omit c in
/-- On the child tail `E y ≥ p T − y₀ ≥ p (5 − Λ)`. -/
theorem child_coefE_ge (hlam : 0 < lam) {T Y Λ : ℝ} (hT : 6 ≤ T) (hTY : lmass lam T ≤ Y)
    (hΛ : lam ≤ Λ) : msg lam Y * (5 - Λ) ≤ coefE lam T Y * lmass lam T := by
  have hp0 := msg_pos hlam Y
  have hy := lmass_pos hlam T
  have hY0 : 0 < Y := lt_of_lt_of_le hy hTY
  have hEy := coefE_mul_ge_child hlam hTY
  have hy0 := lmass_le_one_add_mul_msg hlam hY0.le
  have h1 : msg lam Y * (5 - Λ) ≤ msg lam Y * (T - (1 + lam)) :=
    mul_le_mul_of_nonneg_left (by linarith) hp0.le
  linarith

/-- On the child tail `α E ≥ α₀ (5 − Λ) (p / y)`. -/
theorem child_alphaE_ge (hlam : 0 < lam) {T Y Λ α₀ : ℝ} (hT : 6 ≤ T) (hTY : lmass lam T ≤ Y)
    (hΛ : lam ≤ Λ) (hα : α₀ ≤ alpha c lam) (hα₀ : 0 ≤ α₀) :
    α₀ * (5 - Λ) * (msg lam Y / lmass lam T) ≤ alpha c lam * coefE lam T Y := by
  have hy := lmass_pos hlam T
  have hEy := child_coefE_ge hlam hT hTY hΛ
  have hE : msg lam Y * (5 - Λ) / lmass lam T ≤ coefE lam T Y := by
    rw [div_le_iff₀ hy]; exact hEy
  have hE0 : 0 ≤ coefE lam T Y := (entropyOK lam T Y hlam (by linarith) hTY).1
  have k2 : α₀ * (5 - Λ) * (msg lam Y / lmass lam T) =
      α₀ * (msg lam Y * (5 - Λ) / lmass lam T) := by ring
  have k3 : α₀ * (msg lam Y * (5 - Λ) / lmass lam T) ≤ α₀ * coefE lam T Y :=
    mul_le_mul_of_nonneg_left hE hα₀
  have k4 : α₀ * coefE lam T Y ≤ alpha c lam * coefE lam T Y :=
    mul_le_mul_of_nonneg_right hα hE0
  linarith

omit c in
/-- On the child tail `p (400/Λ) ≤ p / y`. -/
theorem child_msg_div_ge (hlam : 0 < lam) {T Y Λ : ℝ} (hT : 6 ≤ T) (hΛ : lam ≤ Λ) :
    msg lam Y * (400 / Λ) ≤ msg lam Y / lmass lam T := by
  obtain ⟨hy400, -⟩ := child_small hlam hT
  have hy := lmass_pos hlam T
  have hp0 := msg_pos hlam Y
  have hΛ0 : 0 < Λ := by linarith
  rw [div_eq_mul_one_div (msg lam Y) (lmass lam T)]
  apply mul_le_mul_of_nonneg_left _ hp0.le
  rw [div_le_div_iff₀ hΛ0 hy]
  linarith

/-- (QC) on the child tail when `L < 0`: `p γ L (s/y)² ≥ −4 (1 + Γ) p · p γ`, `Z ≥ p γ κ` and
`α E ≥ W p`, `W = α₀ (5 − Λ)(400/Λ)`, `4 (1 + Γ) ≤ W κ`. -/
theorem child_compC_nonneg (hlam : 0 < lam) {T Y Λ R Γ α₀ : ℝ} (hT : 6 ≤ T)
    (hTY : lmass lam T ≤ Y) (hY : Y ≤ 4) (hΛ : lam ≤ Λ) (hR : lam ≤ R * gamma c lam)
    (hγ : 0 < gamma c lam) (hΓ : gamma c lam ≤ Γ) (hα : α₀ ≤ alpha c lam) (hα₀ : 0 ≤ α₀)
    (hΛ5 : Λ ≤ 5) (hκ : 0 < 1 - 3 / 50 * (1 + Γ) * R)
    (hC : 4 * (1 + Γ) ≤ α₀ * (5 - Λ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R))
    (hL0 : coefL c lam Y < 0) : 0 ≤ compC c lam T Y := by
  have hp0 := msg_pos hlam Y
  have hΛ0 : 0 < Λ := by linarith
  have hpγ : 0 < msg lam Y * gamma c lam := mul_pos hp0 hγ
  have hZ := child_coefZ_ge c hlam hT hY hR hγ hΓ
  have hZ0 : 0 < coefZ c lam T Y := lt_of_lt_of_le (mul_pos hpγ hκ) hZ
  have hαE := child_alphaE_ge c hlam hT hTY hΛ hα hα₀
  have hpy := child_msg_div_ge hlam (Y := Y) hT hΛ
  have hW : 0 ≤ α₀ * (5 - Λ) * (400 / Λ) :=
    mul_nonneg (mul_nonneg hα₀ (by linarith)) (div_nonneg (by norm_num) hΛ0.le)
  have hWE : α₀ * (5 - Λ) * (400 / Λ) * msg lam Y ≤ alpha c lam * coefE lam T Y := by
    have k1 : α₀ * (5 - Λ) * (msg lam Y * (400 / Λ)) ≤
        α₀ * (5 - Λ) * (msg lam Y / lmass lam T) :=
      mul_le_mul_of_nonneg_left hpy (mul_nonneg hα₀ (by linarith))
    linarith
  -- the square term
  have hsy0 := msg_div_lmass_nonneg hlam T
  have hsy1 := msg_div_lmass_le_one hlam T
  have hsq : (msg lam T / lmass lam T) ^ 2 ≤ 1 := pow_le_one₀ hsy0 hsy1
  have hX : -(4 * (1 + Γ) * msg lam Y * (msg lam Y * gamma c lam)) ≤
      msg lam Y * gamma c lam * coefL c lam Y * (msg lam T / lmass lam T) ^ 2 := by
    have k1 : coefL c lam Y * 1 ≤ coefL c lam Y * (msg lam T / lmass lam T) ^ 2 :=
      mul_le_mul_of_nonpos_left hsq hL0.le
    have hH := coefH_le c hlam hγ.le Y
    have hH0 := coefH_pos c hlam hγ.le Y
    have hLge := coefL_ge c hlam hγ.le Y
    have h1 : coefH c lam Y * Y ≤ coefH c lam Y * 4 := mul_le_mul_of_nonneg_left hY hH0.le
    have h2 : gamma c lam * msg lam Y ≤ Γ * msg lam Y := mul_le_mul_of_nonneg_right hΓ hp0.le
    have k2 : -(4 * (1 + Γ) * msg lam Y) ≤ coefL c lam Y := by linarith
    have k3 := mul_le_mul_of_nonneg_left k1 hpγ.le
    have k4 := mul_le_mul_of_nonneg_left k2 hpγ.le
    linarith
  have hXZ : -(α₀ * (5 - Λ) * (400 / Λ) * msg lam Y) ≤
      msg lam Y * gamma c lam * coefL c lam Y * (msg lam T / lmass lam T) ^ 2 /
        coefZ c lam T Y := by
    rw [le_div_iff₀ hZ0]
    have hWp : -(α₀ * (5 - Λ) * (400 / Λ) * msg lam Y) ≤ 0 := by
      have := mul_nonneg hW hp0.le; linarith
    have k1 : -(α₀ * (5 - Λ) * (400 / Λ) * msg lam Y) * coefZ c lam T Y ≤
        -(α₀ * (5 - Λ) * (400 / Λ) * msg lam Y) *
          (msg lam Y * gamma c lam * (1 - 3 / 50 * (1 + Γ) * R)) :=
      mul_le_mul_of_nonpos_left hZ hWp
    have k2 : 4 * (1 + Γ) * (msg lam Y * (msg lam Y * gamma c lam)) ≤
        α₀ * (5 - Λ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R) *
          (msg lam Y * (msg lam Y * gamma c lam)) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg hp0.le hpγ.le)
    linarith
  show 0 ≤ alpha c lam * coefE lam T Y + msg lam Y * gamma c lam * coefL c lam Y *
    (msg lam T / lmass lam T) ^ 2 / coefZ c lam T Y
  linarith

/-- (QB) on the child tail: `α E + (A p − H)/Y ≥ W' p ≥ H² J / Z`,
`W' = (α₀ (5 − Λ) − Γ)(400/Λ)`, when `(1 + Γ)² (3R/200) ≤ W' κ`. -/
theorem child_compB_nonneg (hlam : 0 < lam) {T Y Λ R Γ α₀ : ℝ} (hT : 6 ≤ T)
    (hTY : lmass lam T ≤ Y) (hY : Y ≤ 4) (hΛ : lam ≤ Λ) (hR : lam ≤ R * gamma c lam)
    (hγ : 0 < gamma c lam) (hΓ : gamma c lam ≤ Γ) (hα : α₀ ≤ alpha c lam) (hα₀ : 0 ≤ α₀)
    (hA : 1 ≤ capA c lam) (hm0 : Γ ≤ α₀ * (5 - Λ)) (hκ : 0 < 1 - 3 / 50 * (1 + Γ) * R)
    (hB : (1 + Γ) ^ 2 * (3 * R / 200) ≤
      (α₀ * (5 - Λ) - Γ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R)) :
    0 ≤ compB c lam T Y := by
  have hp0 := msg_pos hlam Y
  have hy := lmass_pos hlam T
  have hY0 : 0 < Y := lt_of_lt_of_le hy hTY
  have hΛ0 : 0 < Λ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  have hpγ : 0 < msg lam Y * gamma c lam := mul_pos hp0 hγ
  have hZ := child_coefZ_ge c hlam hT hY hR hγ hΓ
  have hZ0 : 0 < coefZ c lam T Y := lt_of_lt_of_le (mul_pos hpγ hκ) hZ
  have hαE := child_alphaE_ge c hlam hT hTY hΛ hα hα₀
  have hpy := child_msg_div_ge hlam (Y := Y) hT hΛ
  obtain ⟨-, hJ3⟩ := child_small hlam hT
  have hJ0 : 0 ≤ coefJ lam T := coefJ_nonneg hlam (by linarith)
  have hJR : coefJ lam T ≤ 3 / 200 * (R * gamma c lam) := by linarith
  have hH := coefH_le c hlam hγ.le Y
  have hH0 := coefH_pos c hlam hγ.le Y
  -- the linear terms
  have hAH := capA_sub_coefH_ge c hlam hγ.le hA Y
  have hB2 : -(Γ * (msg lam Y / lmass lam T)) ≤
      (capA c lam * msg lam Y - coefH c lam Y) / Y := by
    rw [le_div_iff₀ hY0]
    have hpyY : msg lam Y ≤ msg lam Y / lmass lam T * Y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hy]
      exact mul_le_mul_of_nonneg_left hTY hp0.le
    have k1 : Γ * msg lam Y ≤ Γ * (msg lam Y / lmass lam T * Y) :=
      mul_le_mul_of_nonneg_left hpyY hΓ0.le
    have k2 : gamma c lam * msg lam Y ≤ Γ * msg lam Y := mul_le_mul_of_nonneg_right hΓ hp0.le
    linarith
  have hB12 : (α₀ * (5 - Λ) - Γ) * (400 / Λ) * msg lam Y ≤
      alpha c lam * coefE lam T Y + (capA c lam * msg lam Y - coefH c lam Y) / Y := by
    have k1 : (α₀ * (5 - Λ) - Γ) * (msg lam Y * (400 / Λ)) ≤
        (α₀ * (5 - Λ) - Γ) * (msg lam Y / lmass lam T) :=
      mul_le_mul_of_nonneg_left hpy (by linarith)
    linarith
  -- the square term
  have hB3 : coefH c lam Y ^ 2 * coefJ lam T / coefZ c lam T Y ≤
      (α₀ * (5 - Λ) - Γ) * (400 / Λ) * msg lam Y := by
    rw [div_le_iff₀ hZ0]
    have hW : 0 ≤ (α₀ * (5 - Λ) - Γ) * (400 / Λ) :=
      mul_nonneg (by linarith) (div_nonneg (by norm_num) hΛ0.le)
    have k1 : (α₀ * (5 - Λ) - Γ) * (400 / Λ) * msg lam Y *
          (msg lam Y * gamma c lam * (1 - 3 / 50 * (1 + Γ) * R)) ≤
        (α₀ * (5 - Λ) - Γ) * (400 / Λ) * msg lam Y * coefZ c lam T Y :=
      mul_le_mul_of_nonneg_left hZ (mul_nonneg hW hp0.le)
    have k2 : (1 + Γ) ^ 2 * (3 * R / 200) * (msg lam Y ^ 2 * gamma c lam) ≤
        (α₀ * (5 - Λ) - Γ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R) *
          (msg lam Y ^ 2 * gamma c lam) :=
      mul_le_mul_of_nonneg_right hB (mul_nonneg (sq_nonneg _) hγ.le)
    have e1 : coefH c lam Y ^ 2 ≤ ((1 + gamma c lam) * msg lam Y) ^ 2 :=
      pow_le_pow_left₀ hH0.le hH 2
    have e2 : ((1 + gamma c lam) * msg lam Y) ^ 2 ≤ ((1 + Γ) * msg lam Y) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hp0.le)
        (mul_le_mul_of_nonneg_right (by linarith) hp0.le) 2
    have e3 : coefH c lam Y ^ 2 * coefJ lam T ≤
        ((1 + Γ) * msg lam Y) ^ 2 * (3 / 200 * (R * gamma c lam)) :=
      mul_le_mul (e1.trans e2) hJR hJ0 (sq_nonneg _)
    linarith
  show 0 ≤ alpha c lam * coefE lam T Y + (capA c lam * msg lam Y - coefH c lam Y) / Y -
    coefH c lam Y ^ 2 * coefJ lam T / coefZ c lam T Y
  linarith

/-- **The generic child tail** `T ≥ 6`, `lmass λ T ≤ Y ≤ 4`: the three comparisons from rational
envelopes `λ ≤ Λ ≤ 5`, `λ ≤ R γ`, `0 < γ ≤ Γ`, `α ≥ α₀ ≥ 0`, `A ≥ 1` and rational conditions. -/
theorem compOK_child {lam T Y Λ R Γ α₀ : ℝ}
    (hlam : 0 < lam) (hT : 6 ≤ T) (hTY : lmass lam T ≤ Y) (hY : Y ≤ 4)
    (hΛ : lam ≤ Λ) (hR : lam ≤ R * gamma c lam) (hγ : 0 < gamma c lam)
    (hΓ : gamma c lam ≤ Γ) (hα : α₀ ≤ alpha c lam) (hα₀ : 0 ≤ α₀) (hA : 1 ≤ capA c lam)
    (hΛ5 : Λ ≤ 5) (hm0 : Γ ≤ α₀ * (5 - Λ))
    (hκ : 0 < 1 - 3 / 50 * (1 + Γ) * R)
    (hC : 4 * (1 + Γ) ≤ α₀ * (5 - Λ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R))
    (hB : (1 + Γ) ^ 2 * (3 * R / 200) ≤
      (α₀ * (5 - Λ) - Γ) * (400 / Λ) * (1 - 3 / 50 * (1 + Γ) * R)) :
    CompOK c lam T Y := by
  have hp0 := msg_pos hlam Y
  have hZ := child_coefZ_ge c hlam hT hY hR hγ hΓ
  have hZ0 : 0 < coefZ c lam T Y := lt_of_lt_of_le (mul_pos (mul_pos hp0 hγ) hκ) hZ
  refine ⟨hZ0, ?_, child_compB_nonneg c hlam hT hTY hY hΛ hR hγ hΓ hα hα₀ hA hm0 hκ hB⟩
  by_cases hL0 : 0 ≤ coefL c lam Y
  · exact Or.inl hL0
  · exact Or.inr (child_compC_nonneg c hlam hT hTY hY hΛ hR hγ hΓ hα hα₀ hΛ5 hκ hC
      (lt_of_not_ge hL0))

end Tails

end Erdos993Lean.Analytic.Reserve
