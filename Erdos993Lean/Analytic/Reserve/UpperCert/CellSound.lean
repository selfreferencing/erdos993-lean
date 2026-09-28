import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperCert.Forms
import Erdos993Lean.Analytic.Reserve.Cert.CellSound
import Erdos993Lean.Analytic.Reserve.Entropy
import Erdos993Lean.Analytic.TailCert.ExpLog
import Erdos993Lean.Analytic.Reserve.UpperCert.Compute.Cell

/-!
# Soundness of the cell check of O1's upper finite box (lane A15)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  Sources: the referee's replay of Astra's upper certificate
(`LEAN/referee/REVIEW_ASTRA_O1_UPPER_REPLAY.md`, `review_upper_replay/upcore.py`), whose normalized forms and monotone
enclosures the computable checker `Erdos993Lean/Analytic/Reserve/UpperCert/Compute/Cell.lean` follows; lane A12's cell
soundness for `β = 0` (`Erdos993Lean/Analytic/Reserve/Cert/CellSound.lean`: `InCell`, `mem_yFun`, `mem_sqI`,
`mem_meet`), lane A10's interval soundness (`Erdos993Lean/Analytic/TailCert/IvalSound.lean`, `ExpLog.lean`), lane
A13's entropy facts (`Reserve.entropyOK`).

**Theorem (`cellOKU_sound`).**  If `cellOKU cell = true`, then at every point `(λ, T, r)` of the cell the four
comparisons of `UpperBoxOK` hold at `(λ, T, Y)`, `Y = y + (4 − y) r`, `y = lmass λ T` (`UGoal`): `Z > 0`,
`β² T ≤ 8 α Z`, `CB ≥ 0`, `BC ≥ 0` with the upper coefficients `α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100`,
`A = 1 + 3q/5`.

The proof follows the checker value by value: every interval of `mkValsU` contains the corresponding real number
(`mem_*` of lane A10 for the operations; `v = λe^{−T}` between its values at the corners of `(λ, T)`, `y`, `s`
monotone in `v`; `phi_encl2` for `σ = s/y` and `ρ = p/y₀` through `φ` decreasing (`phiF_anti`, `phiF_log`); `yF_mono`
for `Y`; `Rf_corner_lo`/`Rf_corner_hi` for `R`, each corner from one side of one logarithm; `mem_meet` for the two
enclosures of `L`); the floor of `E` is `max(0, E_direct, E_f)` by `entropyOK` (`E ≥ 0` and
`E y ≥ 2δ² + (Y − y)(p + y₀/Y)`); the normalized forms `cZ_eq`, `compCB_eq`, `compBC_eq`
(`Erdos993Lean/Analytic/Reserve/UpperCert/Forms.lean`) turn the interval bounds into the four comparisons.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert

open Real Erdos993Lean.Analytic Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.Reserve.Cert
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.Reserve.Cert.Compute Erdos993Lean.Analytic.Reserve.UpperCert.Compute

theorem toR_one_add (w : ℤ) : toR (one + w) = 1 + toR w := by rw [toR_add, toR_one]

/-- `1 − 1/(1 + w) ∈ msgPt w`. -/
theorem mem_msgPt {w : ℤ} (hw : 0 < one + w) : (msgPt w).Mem (1 - 1 / (1 + toR w)) := by
  have h := mem_sub mem_oneI (mem_div mem_oneI (mem_pt (one + w)) hw)
  rwa [toR_one_add] at h

/-- `φ(t) ∈ [s/y at whi, s/y at wlo]` for `t ∈ [log(1 + wlo), log(1 + whi)]` (`φ` decreases). -/
theorem phi_encl2 {wlo whi : ℤ} {Sl Sh Yl Yh : Ival} {t : ℝ}
    (hl : 0 < one + wlo) (hh : 0 < one + whi)
    (mSl : Sl.Mem (1 - 1 / (1 + toR wlo))) (mSh : Sh.Mem (1 - 1 / (1 + toR whi)))
    (mYl : Yl.Mem (log (1 + toR wlo))) (mYh : Yh.Mem (log (1 + toR whi)))
    (hYl : 0 < Yl.lo) (hYh : 0 < Yh.lo)
    (ht1 : log (1 + toR wlo) ≤ t) (ht2 : t ≤ log (1 + toR whi)) :
    (⟨(div Sh Yh).lo, (div Sl Yl).hi⟩ : Ival).Mem (phiF t) := by
  have hl' : 0 < 1 + toR wlo := by rw [← toR_one_add]; exact toR_pos.mpr hl
  have hh' : 0 < 1 + toR whi := by rw [← toR_one_add]; exact toR_pos.mpr hh
  have hlpos : 0 < log (1 + toR wlo) := (toR_pos.mpr hYl).trans_le mYl.1
  constructor
  · have h1 := (mem_div mSh mYh hYh).1
    rw [← phiF_log hh'] at h1
    exact h1.trans (phiF_anti (hlpos.trans_le ht1) ht2)
  · have h1 := (mem_div mSl mYl hYl).2
    rw [← phiF_log hl'] at h1
    exact (phiF_anti hlpos ht1).trans h1

/-- The four comparisons of `UpperBoxOK` at one point `(λ, T, Y)`. -/
def UGoal (lam T Y : ℝ) : Prop :=
  0 < cZ (uGamma lam) lam T Y ∧
    uBeta lam ^ 2 * T ≤ 8 * uAlpha lam * cZ (uGamma lam) lam T Y ∧
    0 ≤ compCB (uGamma lam) lam (uAlpha lam) (uBeta lam) T Y ∧
    0 ≤ compBC (uGamma lam) lam (uAlpha lam) (uBeta lam) (uCapA lam) T Y

/-- **Soundness of the cell check**: a passing cell satisfies the four comparisons of `UpperBoxOK` at every point
`(λ, T, Y)`, `Y = y + (4 − y) r`, with `(λ, T, r)` in the cell. -/
theorem cellOKU_sound {cell : Cell} (h : cellOKU cell = true) {lam T r : ℝ} (hin : InCell cell lam T r) :
    UGoal lam T (yF (lmass lam T) r) := by
  simp only [cellOKU, sideOKU, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha0, ha4⟩, ht0⟩, hr0⟩, hr1⟩, hvlo⟩, hvhi⟩, hw0⟩, hw1⟩, hyl⟩, hyh⟩, hR⟩,
    hy0l⟩, hy0h⟩, hY⟩, hZb⟩, hyZ⟩, hK⟩, hCB⟩, hBC⟩ := h
  set V := mkValsU cell with hV
  have one0 := one_pos'
  unfold UGoal
  -- the point
  have hlam0 : 0 < lam := (toR_pos.mpr ha0).trans_le hin.a0
  have hT0 : 0 ≤ T := (toR_nonneg.mpr ht0).trans hin.t0
  have hrr0 : 0 ≤ r := (toR_nonneg.mpr hr0).trans hin.r0
  have hr1R : toR cell.r1 ≤ 1 := by rw [← toR_one]; exact toR_le_toR.mpr hr1
  have hrr1 : r ≤ 1 := hin.r1.trans hr1R
  have ha1_4 : toR cell.a1 ≤ 4 := by
    have := toR_le_toR.mpr ha4; rw [toR_int_mul_one] at this; exact_mod_cast this
  have hlam4 : lam ≤ 4 := hin.a1.trans ha1_4
  have ha0R : 0 < toR cell.a0 := toR_pos.mpr ha0
  have ha1R : 0 < toR cell.a1 := hlam0.trans_le hin.a1
  have ht0R : 0 ≤ toR cell.t0 := toR_nonneg.mpr ht0
  set y := lmass lam T with hydef
  set Y := yF y r with hYdef
  have hy4 : y ≤ 4 := (Cert.lmass_le hlam0.le hT0).trans hlam4
  have hypos : 0 < y := lmass_pos hlam0 T
  -- `λ`, `q`, `α`, `β`, `γ`
  have mL : (⟨cell.a0, cell.a1⟩ : Ival).Mem lam := ⟨hin.a0, hin.a1⟩
  have mT : (⟨cell.t0, cell.t1⟩ : Ival).Mem T := ⟨hin.t0, hin.t1⟩
  have mr : (⟨cell.r0, cell.r1⟩ : Ival).Mem r := ⟨hin.r0, hin.r1⟩
  have p1L : 0 < (add oneI (⟨cell.a0, cell.a1⟩ : Ival)).lo := by
    show 0 < one + cell.a0; omega
  have mq : V.q.Mem (actQ lam) := by
    rw [Cert.actQ_eq hlam0.le]
    exact mem_sub mem_oneI (mem_div mem_oneI (mem_add mem_oneI mL) p1L)
  have mal : V.al.Mem (uAlpha lam) := by
    have h := mem_divNat mq (show (0:ℕ) < 2 by norm_num)
    rw [show uAlpha lam = actQ lam / ((2 : ℕ) : ℝ) by unfold uAlpha; norm_num]
    exact h
  have mbe : V.be.Mem (uBeta lam) := by
    have h := mem_divNat (mem_sub mL mem_oneI) (show (0:ℕ) < 27 by norm_num)
    rw [show uBeta lam = (lam - 1) / ((27 : ℕ) : ℝ) by unfold uBeta; norm_num]
    exact h
  have mgam : V.gam.Mem (uGamma lam) := by
    have h := mem_divNat (mem_mulNat mL 31) (show (0:ℕ) < 100 by norm_num)
    rw [show uGamma lam = lam * ((31 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) by unfold uGamma; push_cast; ring]
    exact h
  -- the child: `v`, `y`, `s`, `σ`, `Y`
  have mE0 : V.E0.Mem (exp (-toR cell.t0)) := by
    have := mem_expPt (-cell.t0); rwa [toR_neg] at this
  have mE1 : V.E1.Mem (exp (-toR cell.t1)) := by
    have := mem_expPt (-cell.t1); rwa [toR_neg] at this
  have hvlo_le : toR V.vlo ≤ lam * exp (-T) := by
    have h1 := (mem_mul (mem_pt cell.a0) mE1).1
    have h2 : toR cell.a0 * exp (-toR cell.t1) ≤ lam * exp (-T) :=
      mul_le_mul hin.a0 (exp_le_exp.mpr (by linarith [hin.t1])) (exp_pos _).le hlam0.le
    exact h1.trans h2
  have hvhi_ge : lam * exp (-T) ≤ toR V.vhi := by
    have h1 := (mem_mul (mem_pt cell.a1) mE0).2
    have h2 : lam * exp (-T) ≤ toR cell.a1 * exp (-toR cell.t0) :=
      mul_le_mul hin.a1 (exp_le_exp.mpr (by linarith [hin.t0])) (exp_pos _).le ha1R.le
    exact h2.trans h1
  have h1vlo : 0 < 1 + toR V.vlo := by rw [← toR_one_add]; exact toR_pos.mpr hvlo
  have myl : V.yl.Mem (log (1 + toR V.vlo)) := by
    have := mem_logPt hvlo; rwa [toR_one_add] at this
  have myh : V.yh.Mem (log (1 + toR V.vhi)) := by
    have := mem_logPt hvhi; rwa [toR_one_add] at this
  have hv1 : 0 < 1 + lam * exp (-T) := Cert.one_add_pos hlam0.le
  have hyv_lo : log (1 + toR V.vlo) ≤ y := log_le_log h1vlo (by linarith)
  have hyv_hi : y ≤ log (1 + toR V.vhi) := log_le_log hv1 (by linarith)
  have my : V.y.Mem y := ⟨myl.1.trans hyv_lo, hyv_hi.trans myh.2⟩
  have msl := mem_msgPt hvlo
  have msh := mem_msgPt hvhi
  have ms : V.s.Mem (msg lam T) := by
    rw [Cert.msg_eq hlam0.le]
    exact ⟨msl.1.trans (one_sub_inv_mono h1vlo hvlo_le), (one_sub_inv_mono hv1 hvhi_ge).trans msh.2⟩
  have msig : V.sig.Mem (msg lam T / y) := by
    rw [hydef, Cert.msg_div_lmass hlam0.le]
    exact phi_encl2 hvlo hvhi msl msh myl myh hyl hyh hyv_lo hyv_hi
  have mY : V.Y.Mem Y := by
    constructor
    · exact (mem_yFun (mem_pt _) (mem_pt _)).1.trans
        (yF_mono my.1 (my.1.trans hy4) hin.r0 hrr1)
    · exact (yF_mono my.2 hy4 hin.r1 hr1R).trans (mem_yFun (mem_pt _) (mem_pt _)).2
  -- the parent: `R` at the corners, `p`, `y₀`, `ρ`
  have hyc0 : lmass (toR cell.a0) (toR cell.t0) ≤ toR V.yc0 := by
    have h1 := (mem_logPt hw0).2
    rw [toR_one_add] at h1
    have h2 : toR cell.a0 * exp (-toR cell.t0) ≤ toR V.w0 := (mem_mul (mem_pt cell.a0) mE0).2
    unfold lmass
    exact (log_le_log (Cert.one_add_pos ha0R.le) (by linarith)).trans h1
  have hyc1 : toR V.yc1 ≤ lmass (toR cell.a1) (toR cell.t1) := by
    have h1 := (mem_logPt hw1).1
    rw [toR_one_add] at h1
    have h2 : toR V.w1 ≤ toR cell.a1 * exp (-toR cell.t1) := (mem_mul (mem_pt cell.a1) mE1).1
    have h1w1 : 0 < 1 + toR V.w1 := by rw [← toR_one_add]; exact toR_pos.mpr hw1
    unfold lmass
    exact h1.trans (log_le_log h1w1 (by linarith))
  have mR : V.R.Mem (lam * exp (-Y)) := by
    have hRf : lam * exp (-Y) = Rf lam T r := rfl
    rw [hRf]
    constructor
    · have h1 := (mem_mul (mem_pt cell.a0) (mem_expPt (-(yFun (pt V.yc0) (pt cell.r1)).hi))).1
      rw [toR_neg] at h1
      have h2 := (mem_yFun (mem_pt V.yc0) (mem_pt cell.r1)).2
      have h2' : yF (lmass (toR cell.a0) (toR cell.t0)) (toR cell.r1) ≤ yF (toR V.yc0) (toR cell.r1) :=
        yF_mono hyc0 ((Cert.lmass_le ha0R.le ht0R).trans (hin.a0.trans hlam4)) le_rfl hr1R
      have h3 : toR cell.a0 * exp (-toR (yFun (pt V.yc0) (pt cell.r1)).hi) ≤
          Rf (toR cell.a0) (toR cell.t0) (toR cell.r1) := by
        unfold Rf
        exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) ha0R.le
      have h4 := Rf_corner_lo ha0R hin.a0 ht0R hin.t0 hrr0 hin.r1 hrr1 (hin.a0.trans hlam4)
      exact h1.trans (h3.trans h4)
    · have h1 := (mem_mul (mem_pt cell.a1) (mem_expPt (-(yFun (pt V.yc1) (pt cell.r0)).lo))).2
      rw [toR_neg] at h1
      have h2 := (mem_yFun (mem_pt V.yc1) (mem_pt cell.r0)).1
      have hlm4 : lmass (toR cell.a1) (toR cell.t1) ≤ 4 :=
        (Cert.lmass_le ha1R.le (hT0.trans hin.t1)).trans ha1_4
      have h2' : yF (toR V.yc1) (toR cell.r0) ≤ yF (lmass (toR cell.a1) (toR cell.t1)) (toR cell.r0) :=
        yF_mono hyc1 (hyc1.trans hlm4) le_rfl (hin.r0.trans hrr1)
      have h3 : Rf (toR cell.a1) (toR cell.t1) (toR cell.r0) ≤
          toR cell.a1 * exp (-toR (yFun (pt V.yc1) (pt cell.r0)).lo) := by
        unfold Rf
        exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) ha1R.le
      have h4 := Rf_corner_hi hlam0 hin.a1 hT0 hin.t1 hrr0 hin.r0 hrr1 ha1_4
      exact h4.trans (h3.trans h1)
  have hRle : V.R.lo ≤ V.R.hi := mR.lo_le_hi
  have hR1lo : 0 < one + V.R.lo := by omega
  have hR1hi : 0 < one + V.R.hi := by omega
  have p1R : 0 < (add oneI V.R).lo := by show 0 < one + V.R.lo; omega
  have momp : V.omp.Mem (1 - msg lam Y) := by
    rw [Cert.one_sub_msg hlam0.le]; exact mem_div mem_oneI (mem_add mem_oneI mR) p1R
  have mp : V.p.Mem (msg lam Y) := by
    have := mem_sub mem_oneI momp; rwa [sub_sub_cancel] at this
  have h1Rlo : 0 < 1 + toR V.R.lo := by rw [← toR_one_add]; exact toR_pos.mpr hR1lo
  have my0l : V.y0l.Mem (log (1 + toR V.R.lo)) := by
    have := mem_logPt hR1lo; rwa [toR_one_add] at this
  have my0h : V.y0h.Mem (log (1 + toR V.R.hi)) := by
    have := mem_logPt hR1hi; rwa [toR_one_add] at this
  have hy0v_lo : log (1 + toR V.R.lo) ≤ lmass lam Y := log_le_log h1Rlo (by linarith [mR.1])
  have hy0v_hi : lmass lam Y ≤ log (1 + toR V.R.hi) :=
    log_le_log (Cert.one_add_pos hlam0.le) (by linarith [mR.2])
  have my0 : V.y0.Mem (lmass lam Y) := ⟨my0l.1.trans hy0v_lo, hy0v_hi.trans my0h.2⟩
  have mrho : V.rho.Mem (msg lam Y / lmass lam Y) := by
    rw [Cert.msg_div_lmass hlam0.le]
    exact phi_encl2 hR1lo hR1hi (mem_msgPt hR1lo) (mem_msgPt hR1hi) my0l my0h hy0l hy0h hy0v_lo hy0v_hi
  -- the composites
  have mh : V.h.Mem (hU (uGamma lam) lam Y) := mem_add momp (mem_mul mgam mrho)
  have mJ : V.J.Mem (coefJ lam T) := by
    rw [Cert.coefJ_eq]; exact mem_mul (mem_mul ms msig) mT
  have mLp : V.Lp.Mem (LpU (uGamma lam) lam Y) := mem_sub (mem_div mgam mR hR) (mem_mul mh mY)
  have mLL : V.L.Mem (cL (uGamma lam) lam Y) := by
    apply mem_meet
    · rw [cL_eq']; exact mem_sub (mem_mul mgam momp) (mem_mul (mem_mul mp mh) mY)
    · rw [cL_eq _ lam Y hlam0]; exact mem_mul mp mLp
  have mZb : V.Zb.Mem (ZbU (uGamma lam) lam T Y) := mem_add mgam (mem_mul mJ mLp)
  -- the bounds
  have hp0 : 0 < msg lam Y := msg_pos hlam0 Y
  have hZb0 : 0 < ZbU (uGamma lam) lam T Y := (toR_pos.mpr hZb).trans_le mZb.1
  have hY0 : 0 < Y := (toR_pos.mpr hY).trans_le mY.1
  have hy00 : 0 < lmass lam Y := lmass_pos hlam0 Y
  have mpZb : V.pZb.Mem (msg lam Y * ZbU (uGamma lam) lam T Y) := mem_mul mp mZb
  have myZ : V.yZ.Mem (y * (msg lam Y * ZbU (uGamma lam) lam T Y)) := mem_mul my mpZb
  have mbe2 : V.be2.Mem (uBeta lam ^ 2) := mem_sqI mbe
  have mK : V.K.Mem (uAlpha lam * (msg lam Y * ZbU (uGamma lam) lam T Y) * ((2 : ℕ) : ℝ) -
      uBeta lam ^ 2 * T / ((4 : ℕ) : ℝ)) :=
    mem_sub (mem_mulNat (mem_mul mal mpZb) 2) (mem_divNat (mem_mul mbe2 mT) (by norm_num))
  have md : V.d.Mem (msg lam T - msg lam Y) := mem_sub ms mp
  have md2 : V.d2.Mem ((msg lam T - msg lam Y) ^ 2) := mem_sqI md
  have my0Y : V.y0Y.Mem (lmass lam Y / Y) := mem_div my0 mY hY
  have mu : V.u.Mem (T / y) := mem_div mT my hyl
  have mEd : V.Ed.Mem (coefE lam T Y) := by
    rw [Cert.coefE_eq]; exact mem_sub (mem_add momp (mem_mul mp mu)) my0Y
  have mEf : V.Ef.Mem (((msg lam T - msg lam Y) ^ 2 * ((2 : ℕ) : ℝ) +
      (4 - y) * r * (msg lam Y + lmass lam Y / Y)) / y) :=
    mem_div (mem_add (mem_mulNat md2 2)
      (mem_mul (mem_mul (mem_sub mem_fourI my) mr) (mem_add mp my0Y))) my hyl
  -- the floor of `E` (`EntropyOK`)
  have hgap : Y - y = (4 - y) * r := yF_sub y r
  have hyY : y ≤ Y := by
    have : 0 ≤ (4 - y) * r := mul_nonneg (by linarith) hrr0
    linarith
  obtain ⟨hE0, hEy⟩ := entropyOK lam T Y hlam0 hT0 hyY
  have hEf : toR V.Ef.lo ≤ coefE lam T Y := by
    refine mEf.1.trans ?_
    rw [div_le_iff₀ hypos]
    have e : (msg lam T - msg lam Y) ^ 2 * ((2 : ℕ) : ℝ) + (4 - y) * r * (msg lam Y + lmass lam Y / Y) =
        2 * (msg lam Y - msg lam T) ^ 2 + (Y - y) * (msg lam Y + lmass lam Y / Y) := by
      rw [hgap]; push_cast; ring
    rw [e]
    exact hEy
  have hElo : toR V.Elo ≤ coefE lam T Y := by
    show toR (max 0 (max V.Ed.lo V.Ef.lo)) ≤ coefE lam T Y
    rw [toR_max, toR_max, toR_zero]
    exact max_le hE0 (max_le mEd.1 hEf)
  have hal0 : 0 ≤ uAlpha lam := by
    unfold uAlpha actQ
    exact div_nonneg (div_nonneg hlam0.le (by linarith)) (by norm_num)
  have haE : toR V.aE ≤ uAlpha lam * coefE lam T Y := by
    have h1 := (mem_mul mal (mem_pt V.Elo)).1
    exact h1.trans (mul_le_mul_of_nonneg_left hElo hal0)
  -- `Q`, `X`, `W`, the regrouped BC
  have hyZ4 : 0 < (mulNat V.yZ 4).lo := by
    show 0 < V.yZ.lo * ((4 : ℕ) : ℤ)
    push_cast; omega
  have mQt : V.Qt.Mem (uBeta lam ^ 2 * (msg lam T - msg lam Y) ^ 2 * T /
      (y * (msg lam Y * ZbU (uGamma lam) lam T Y) * ((4 : ℕ) : ℝ))) :=
    mem_div (mem_mul (mem_mul mbe2 md2) mT) (mem_mulNat myZ 4) hyZ4
  have mX : V.X.Mem (msg lam T / y * (uBeta lam * uGamma lam + cL (uGamma lam) lam Y * (msg lam T / y) *
      (uGamma lam + uBeta lam * T)) / ZbU (uGamma lam) lam T Y) :=
    mem_div (mem_mul msig (mem_add (mem_mul mbe mgam)
      (mem_mul (mem_mul mLL msig) (mem_add mgam (mem_mul mbe mT))))) mZb hZb
  have mk : (divNat (mulNat V.q 3) 5).Mem (3 / 5 * actQ lam) := by
    have h := mem_divNat (mem_mulNat mq 3) (show (0 : ℕ) < 5 by norm_num)
    rw [show 3 / 5 * actQ lam = actQ lam * ((3 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by push_cast; ring]
    exact h
  have mW : V.W.Mem (msg lam Y * (3 / 5 * actQ lam - uBeta lam + msg lam Y -
      uGamma lam * (msg lam Y / lmass lam Y)) / Y) :=
    mem_div (mem_mul mp (mem_sub (mem_add (mem_sub mk mbe) mp) (mem_mul mgam mrho))) mY hY
  have mbr : V.br.Mem (msg lam Y * (uAlpha lam * ZbU (uGamma lam) lam T Y -
      (hU (uGamma lam) lam Y * msg lam T) ^ 2) -
      hU (uGamma lam) lam Y * uBeta lam * ((msg lam T - msg lam Y) * msg lam T)) :=
    mem_sub (mem_mul mp (mem_sub (mem_mul mal mZb) (mem_sqI (mem_mul mh ms))))
      (mem_mul (mem_mul mh mbe) (mem_mul md ms))
  have mBC : V.BC.Mem (uAlpha lam * ((1 - msg lam Y) - lmass lam Y / Y) +
      msg lam Y * (3 / 5 * actQ lam - uBeta lam + msg lam Y - uGamma lam * (msg lam Y / lmass lam Y)) / Y +
      T / y * (msg lam Y * (uAlpha lam * ZbU (uGamma lam) lam T Y - (hU (uGamma lam) lam Y * msg lam T) ^ 2) -
        hU (uGamma lam) lam Y * uBeta lam * ((msg lam T - msg lam Y) * msg lam T)) /
        ZbU (uGamma lam) lam T Y) :=
    mem_add (mem_add (mem_mul mal (mem_sub momp my0Y)) mW) (mem_div (mem_mul mu mbr) mZb hZb)
  -- the four comparisons
  have hQ := mQt.2
  push_cast at hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cZ_eq _ lam T Y hlam0]
    exact mul_pos hp0 hZb0
  · rw [cZ_eq _ lam T Y hlam0]
    have h1 := (toR_nonneg.mpr hK).trans mK.1
    push_cast at h1
    linarith
  · rw [compCB_eq _ lam _ _ T Y hlam0 hypos hZb0.ne', ← hydef]
    have h1 : 0 ≤ toR V.aE - toR V.Qt.hi + toR V.X.lo := by
      rw [← toR_sub, ← toR_add]; exact toR_nonneg.mpr hCB
    have h3 := mX.1
    linarith
  · rw [show uCapA lam = 1 + 3 / 5 * actQ lam from rfl,
      compBC_eq _ lam _ _ _ T Y hlam0 hypos hY0.ne' hy00.ne' hZb0.ne', ← hydef]
    have h1 : 0 ≤ toR V.BC.lo - toR V.Qt.hi := by
      rw [← toR_sub]; exact toR_nonneg.mpr hBC
    have h3 := mBC.1
    linarith

end Erdos993Lean.Analytic.Reserve.UpperCert
