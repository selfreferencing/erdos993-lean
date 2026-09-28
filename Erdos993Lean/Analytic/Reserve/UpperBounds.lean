import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperDefs
import Erdos993Lean.Analytic.Reserve.TailGeneric

/-!
# O1 on the upper band `[8/5, 7/3]`: envelopes and coefficient bounds (lane A14)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lane A14).  Sources: Astra's
`UPPER_SHARP_SIGNED_PORT_PROOF.md` (reviewed snapshot `LEAN/referee/astra_o1/snapshot_0845`), "Complete parent
tail Y>=4" and "Complete child tail T>=6, Y<=4", and the referee's list of the numeric facts
(`LEAN/referee/REVIEW_ASTRA_O1_UPPER_PROOF.md`, TASK 3 and "WHAT LEAN MUST ADD", item 4; script
`review_upper_proof/u3_tails_exact.py`).

The inputs of the analytic tails of the upper band (`Reserve/UpperTail.lean`), in namespace
`Erdos993Lean.Analytic.Reserve.Upper`:

* the coefficient profile on `λ ∈ [8/5, 7/3]` (`α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100`, `A = 1 + 3q/5`):
  `8/13 ≤ q ≤ 7/10` (`actQ_ge`, `actQ_le`), `α ≥ 4/13` (`uAlpha_ge`), `0 ≤ β ≤ 4/81` (`uBeta_nonneg`,
  `uBeta_le`), `62/125 ≤ γ ≤ 217/300` (`uGamma_ge`, `uGamma_le`), `A ≥ 1` (`uCapA_ge`), `3q/5 ≤ β + γ`
  (`capA_sub_le`), and PSD `β² ≤ 4αγ` (`upper_psd`);
* the coefficients of the comparisons for a general `γ ≥ 0`: `0 ≤ H ≤ (1 + γ) p` (`cH_nonneg`, `cH_le`),
  `L ≥ −H Y` (`cL_ge`);
* `e⁴ < 60` (`exp_four_lt`), the message identity `p (e^Y + λ) = λ` (`msg_mul_exp_add`), and on the child
  tail `T s² ≤ (3/20) p²` (`child_ratio`: `s ≤ (e^Y + λ) e^{−T} p ≤ 63 e^{−T} p` and
  `T e^{−2T} ≤ 6/160000`);
* on the parent tail `L ≥ γ/2` (`parent_cL_ge`: `H Y ≤ (1 + γ) p Y ≤ (1 + γ) 4λ/50` and `γ = 31λ/100`,
  `λ ≤ 75/31`).

Scalarity: `p, y₀` (parent) and `s, y` (child) are the actual messages and log-masses of one parent–child
pair of the rooted forest; `T`, `Y` are the grandchild and child log-mass sums of the actual lists;
the envelopes are fixed rational bounds of the band's coefficient profile (inputs); the consumer is
`upperTailOK` (and through it lane A11's `reserve_step_cert`).
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

namespace Upper

variable {lam : ℝ}

/-! ### The coefficient profile of the upper band -/

theorem actQ_ge (h : 8 / 5 ≤ lam) : 8 / 13 ≤ actQ lam := by
  unfold actQ
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem actQ_le (h0 : 0 ≤ lam) (h : lam ≤ 7 / 3) : actQ lam ≤ 7 / 10 := by
  unfold actQ
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem uAlpha_ge (h : 8 / 5 ≤ lam) : 4 / 13 ≤ uAlpha lam := by
  unfold uAlpha
  have := actQ_ge h
  linarith

theorem uBeta_nonneg (h : 8 / 5 ≤ lam) : 0 ≤ uBeta lam := by
  unfold uBeta
  linarith

theorem uBeta_le (h : lam ≤ 7 / 3) : uBeta lam ≤ 4 / 81 := by
  unfold uBeta
  linarith

theorem uGamma_ge (h : 8 / 5 ≤ lam) : 62 / 125 ≤ uGamma lam := by
  unfold uGamma
  linarith

theorem uGamma_le (h : lam ≤ 7 / 3) : uGamma lam ≤ 217 / 300 := by
  unfold uGamma
  linarith

theorem uCapA_ge (h : 8 / 5 ≤ lam) : 1 ≤ uCapA lam := by
  unfold uCapA
  have := actQ_ge h
  linarith

/-- `3q/5 ≤ β + γ` on the band (the linear BC term `A − β − (1 + γ) = 3q/5 − β − γ` is nonpositive). -/
theorem capA_sub_le (h1 : 8 / 5 ≤ lam) (h2 : lam ≤ 7 / 3) :
    3 / 5 * actQ lam ≤ uBeta lam + uGamma lam := by
  have := actQ_le (by linarith) h2
  have := uBeta_nonneg h1
  have := uGamma_ge h1
  linarith

/-- **PSD on the upper band**: `β² ≤ 4αγ` (`4αγ ≥ 992/1625`, `β² ≤ 16/6561`). -/
theorem upper_psd (h1 : 8 / 5 ≤ lam) (h2 : lam ≤ 7 / 3) :
    uBeta lam ^ 2 ≤ 4 * uAlpha lam * uGamma lam := by
  have ha := uAlpha_ge h1
  have hb0 := uBeta_nonneg h1
  have hb := uBeta_le h2
  have hg := uGamma_ge h1
  have hb2 : uBeta lam ^ 2 ≤ (4 / 81) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  have hag : 4 / 13 * (62 / 125) ≤ uAlpha lam * uGamma lam :=
    mul_le_mul ha hg (by norm_num) (by linarith)
  nlinarith

/-! ### The coefficients for a general `γ` -/

theorem cH_nonneg {γ : ℝ} (hlam : 0 < lam) (hγ : 0 ≤ γ) (Y : ℝ) : 0 ≤ cH γ lam Y := by
  unfold cH
  have hp := msg_pos hlam Y
  have hp1 := msg_lt_one hlam Y
  have hy := lmass_pos hlam Y
  have h1 : 0 ≤ msg lam Y * (1 - msg lam Y) := mul_nonneg hp.le (by linarith)
  have h2 : 0 ≤ γ * msg lam Y ^ 2 / lmass lam Y := by positivity
  linarith

/-- `H ≤ (1 + γ) p` (`p ≤ y₀`). -/
theorem cH_le {γ : ℝ} (hlam : 0 < lam) (hγ : 0 ≤ γ) (Y : ℝ) :
    cH γ lam Y ≤ (1 + γ) * msg lam Y := by
  unfold cH
  have hp := msg_pos hlam Y
  have hy := lmass_pos hlam Y
  have hpy := Tails.msg_le_lmass hlam Y
  have h1 : msg lam Y ^ 2 / lmass lam Y ≤ msg lam Y := by
    rw [div_le_iff₀ hy]
    nlinarith
  have h2 : γ * (msg lam Y ^ 2 / lmass lam Y) ≤ γ * msg lam Y := mul_le_mul_of_nonneg_left h1 hγ
  have h3 : γ * msg lam Y ^ 2 / lmass lam Y = γ * (msg lam Y ^ 2 / lmass lam Y) := by ring
  nlinarith [sq_nonneg (msg lam Y)]

/-- `L ≥ −H Y`. -/
theorem cL_ge {γ : ℝ} (hlam : 0 < lam) (hγ : 0 ≤ γ) (Y : ℝ) :
    -(cH γ lam Y * Y) ≤ cL γ lam Y := by
  unfold cL
  have := msg_lt_one hlam Y
  have : 0 ≤ γ * (1 - msg lam Y) := mul_nonneg hγ (by linarith)
  linarith

/-! ### Exponential facts -/

/-- `e⁴ < 60`. -/
theorem exp_four_lt : exp 4 < 60 := by
  have h : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc exp 1 ^ 4 < 2.7182818286 ^ 4 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    _ < 60 := by norm_num

/-- The message identity `p (e^Y + λ) = λ`. -/
theorem msg_mul_exp_add (hlam : 0 < lam) (Y : ℝ) : msg lam Y * (exp Y + lam) = lam := by
  unfold msg
  have h1 : 0 < 1 + lam * exp (-Y) := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff h1.ne']
  have h2 : exp (-Y) * exp Y = 1 := by rw [← Real.exp_add]; simp
  linear_combination lam * h2

/-- **The child/parent message ratio on the child tail**: for `T ≥ 6`, `Y ≤ 4` and `0 < λ ≤ 7/3`,
`T s² ≤ (3/20) p²` (`s ≤ λ e^{−T} = (e^Y + λ) e^{−T} p < 63 e^{−T} p` and `T e^{−2T} ≤ 6/160000`). -/
theorem child_ratio (hlam : 0 < lam) (hhi : lam ≤ 7 / 3) {T Y : ℝ} (hT : 6 ≤ T) (hY : Y ≤ 4) :
    T * msg lam T ^ 2 ≤ 3 / 20 * msg lam Y ^ 2 := by
  have hs := Tails.msg_le_lamExp hlam T
  have hs0 := msg_pos hlam T
  have hp0 := msg_pos hlam Y
  have hpe := msg_mul_exp_add hlam Y
  have heY : exp Y < 60 := lt_of_le_of_lt (exp_le_exp.mpr hY) exp_four_lt
  have hE := exp_pos (-T)
  have h1 : msg lam T ≤ 63 * msg lam Y * exp (-T) := by
    calc msg lam T ≤ lam * exp (-T) := hs
      _ = msg lam Y * (exp Y + lam) * exp (-T) := by rw [hpe]
      _ ≤ 63 * msg lam Y * exp (-T) := by
          apply mul_le_mul_of_nonneg_right _ hE.le
          nlinarith
  have h2 : msg lam T ^ 2 ≤ (63 * msg lam Y * exp (-T)) ^ 2 := pow_le_pow_left₀ hs0.le h1 2
  have h3 := Tails.mul_exp_neg_le_of_six_le hT
  have h4 := Tails.exp_neg_le_of_six_le hT
  have h5 : T * exp (-T) * exp (-T) ≤ 6 / 400 * (1 / 400) := mul_le_mul h3 h4 hE.le (by norm_num)
  calc T * msg lam T ^ 2 ≤ T * (63 * msg lam Y * exp (-T)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = 3969 * msg lam Y ^ 2 * (T * exp (-T) * exp (-T)) := by ring
    _ ≤ 3969 * msg lam Y ^ 2 * (6 / 400 * (1 / 400)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ 3 / 20 * msg lam Y ^ 2 := by nlinarith [sq_nonneg (msg lam Y)]

/-! ### The parent tail: `L ≥ γ/2` -/

/-- On the parent tail `Y ≥ 4` of the upper band, `L ≥ γ/2`: `H Y ≤ (1 + γ) p Y ≤ (1 + γ) 4λ/50`,
`γ p ≤ γ λ/50`, and `γ/2 − γλ/50 − (1 + γ) 4λ/50 = λ (75 − 31λ)/1000 ≥ 0` for `γ = 31λ/100`, `λ ≤ 7/3`. -/
theorem parent_cL_ge (h1 : 8 / 5 ≤ lam) (h2 : lam ≤ 7 / 3) {Y : ℝ} (hY : 4 ≤ Y) :
    uGamma lam / 2 ≤ cL (uGamma lam) lam Y := by
  have hlam : 0 < lam := by linarith
  have hγ0 : 0 ≤ uGamma lam := by have := uGamma_ge h1; linarith
  obtain ⟨hp50, hpY, -⟩ := Tails.parent_small hlam hY
  have hH := cH_le hlam hγ0 Y
  have hY0 : 0 < Y := by linarith
  have hHY : cH (uGamma lam) lam Y * Y ≤ (1 + uGamma lam) * msg lam Y * Y :=
    mul_le_mul_of_nonneg_right hH hY0.le
  have hpY' : (1 + uGamma lam) * (msg lam Y * Y) ≤ (1 + uGamma lam) * (lam * (4 / 50)) :=
    mul_le_mul_of_nonneg_left hpY (by linarith)
  have hγp : uGamma lam * msg lam Y ≤ uGamma lam * (lam / 50) :=
    mul_le_mul_of_nonneg_left hp50 hγ0
  have hpoly : 0 ≤ lam * (75 - 31 * lam) := mul_nonneg hlam.le (by linarith)
  unfold cL
  have e : uGamma lam = 31 * lam / 100 := rfl
  rw [e] at hHY hpY' hγp ⊢
  nlinarith

end Upper

end Erdos993Lean.Analytic.Reserve
