import Mathlib
import Erdos993Lean.Analytic.Reserve.Cert.Real
import Erdos993Lean.Analytic.TailCert.ExpLog
import Erdos993Lean.Analytic.Reserve.Cert.Compute.Cell

/-!
# Soundness of the cell check of O1's finite box (lane A12)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  Sources: the referee's replay of Astra's O1 cell
certificates (`LEAN/referee/REVIEW_ASTRA_O1_REPLAY.md`, `review_replay/o1core.py`), whose evaluator the computable
checker `Erdos993Lean/Analytic/Reserve/Cert/Compute/Cell.lean` follows; lane A10's interval soundness
(`Erdos993Lean/Analytic/TailCert/IvalSound.lean`, `ExpLog.lean`).

**Theorem (`cellOK_sound`).**  For every band `c`: if `cellOK (mkConsts c.D c.aCoef c.gDen) cell = true`, then
`CompOK c λ T (y + (4 − y) r)` (`y = lmass λ T`) at every point `(λ, T, r)` of the cell.

The proof follows the checker value by value: every interval of `mkVals` contains the corresponding real number
(`mem_*` of lane A10 for the operations, `phi_encl` for `σ = s/y` and `ρ = p/y₀` through `φ` decreasing,
`yF_mono` for `Y`, `Rf_corner_lo`/`Rf_corner_hi` for `R`, `mem_meet` for the two enclosures of `L`, and the direct
enclosure of `E` — no floor of `E`, so neither `EntropyOK` nor a sign of `aCoef` is used); the normalized forms
`coefZ_eq`, `compC_eq`, `compB_eq` turn the three interval bounds into `(Q0)`, `(QC)`, `(QB)`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.Reserve.Cert

open Real Erdos993Lean.Analytic Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.Reserve.Cert.Compute

/-! ## Interval helpers -/

theorem toR_int_mul_one (k : ℤ) : toR (k * one) = k := by
  unfold toR; rw [one_eq]; push_cast; field_simp

theorem one_pos' : (0 : ℤ) < one := by decide

theorem mem_oneI : oneI.Mem 1 := by
  have := mem_pt one; rwa [toR_one] at this

theorem mem_threeI : threeI.Mem 3 := by
  have := mem_pt (3 * one); rw [toR_int_mul_one] at this; exact_mod_cast this

theorem mem_fourI : fourI.Mem 4 := by
  have := mem_pt (4 * one); rw [toR_int_mul_one] at this; exact_mod_cast this

/-- `φ(t) ∈ phiPt t` for `t > 0`. -/
theorem mem_phiPt {t : ℤ} (ht : 0 < t) : (phiPt t).Mem (phiF (toR t)) := by
  have h1 := mem_sub mem_oneI (mem_expPt (-t))
  rw [toR_neg] at h1
  exact mem_div h1 (mem_pt t) ht

/-- `φ(t) ∈ [φ(t_hi), φ(t_lo)]` for `t ∈ [t_lo, t_hi]`, `t_lo > 0` (`φ` decreases). -/
theorem phi_encl {A : Ival} {t : ℝ} (hA : A.Mem t) (hpos : 0 < A.lo) :
    (⟨(phiPt A.hi).lo, (phiPt A.lo).hi⟩ : Ival).Mem (phiF t) := by
  have hhi : 0 < A.hi := lt_of_lt_of_le hpos hA.lo_le_hi
  have htl : 0 < toR A.lo := toR_pos.mpr hpos
  constructor
  · exact (mem_phiPt hhi).1.trans (phiF_anti (htl.trans_le hA.1) hA.2)
  · exact (phiF_anti htl hA.1).trans (mem_phiPt hpos).2

theorem mem_yFun {A B : Ival} {y r : ℝ} (hA : A.Mem y) (hB : B.Mem r) : (yFun A B).Mem (yF y r) :=
  mem_add hA (mem_mul (mem_sub mem_fourI hA) hB)

/-- The square of an interval of either sign. -/
theorem mem_sqI {A : Ival} {x : ℝ} (hA : A.Mem x) : (sqI A).Mem (x ^ 2) := by
  unfold sqI
  split_ifs with h1 h2
  · exact mem_sqr hA h1
  · have := mem_sqr (mem_neg hA) (by show 0 ≤ -A.hi; omega)
    simpa using this
  · constructor
    · show toR 0 ≤ x ^ 2
      rw [toR_zero]; positivity
    · show x ^ 2 ≤ toR (cdivP (max (A.lo * A.lo) (A.hi * A.hi)))
      refine le_trans ?_ (le_toR_cdivP _)
      have e : ((max (A.lo * A.lo) (A.hi * A.hi) : ℤ) : ℝ) / 2 ^ prec / 2 ^ prec =
          max (toR A.lo * toR A.lo) (toR A.hi * toR A.hi) := by
        rw [toR_mul_toR, toR_mul_toR, Int.cast_max, max_div_div_right (by positivity),
          max_div_div_right (by positivity)]
      rw [e]
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (by nlinarith [hA.2])
      · exact le_max_of_le_left (by nlinarith [hA.1])

/-- The intersection of two enclosures of `x` encloses `x`. -/
theorem mem_meet {A B : Ival} {x : ℝ} (hA : A.Mem x) (hB : B.Mem x) : (meet A B).Mem x := by
  unfold meet Ival.Mem
  simp only [toR_max, toR_min]
  exact ⟨max_le hA.1 hB.1, le_min hA.2 hB.2⟩

/-! ## The cell -/

/-- The point `(λ, T, r)` lies in the cell. -/
structure InCell (cell : Cell) (lam T r : ℝ) : Prop where
  a0 : toR cell.a0 ≤ lam
  a1 : lam ≤ toR cell.a1
  t0 : toR cell.t0 ≤ T
  t1 : T ≤ toR cell.t1
  r0 : toR cell.r0 ≤ r
  r1 : r ≤ toR cell.r1

/-- **Soundness of the cell check**: a passing cell satisfies the three comparisons `CompOK` at every point
`(λ, T, Y)`, `Y = y + (4 − y) r`, with `(λ, T, r)` in the cell. -/
theorem cellOK_sound (c : Band) {cell : Cell}
    (h : cellOK (mkConsts c.D c.aCoef c.gDen) cell = true) {lam T r : ℝ} (hin : InCell cell lam T r) :
    CompOK c lam T (yF (lmass lam T) r) := by
  simp only [cellOK, sideOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha0, ha4⟩, ht0⟩, hr0⟩, hr1⟩, hv⟩, hy⟩, hc0⟩, hc1⟩, hR⟩, hy0⟩, hY⟩, hZb⟩, hB⟩,
    hC⟩ := h
  set K := mkConsts c.D c.aCoef c.gDen with hK
  set V := mkVals K cell with hV
  have one0 := one_pos'
  -- the point
  have hlam0 : 0 < lam := (toR_pos.mpr ha0).trans_le hin.a0
  have hT0 : 0 ≤ T := (toR_nonneg.mpr ht0).trans hin.t0
  have hrr0 : 0 ≤ r := (toR_nonneg.mpr hr0).trans hin.r0
  have hr1R : toR cell.r1 ≤ 1 := by rw [← toR_one]; exact toR_le_toR.mpr hr1
  have hrr1 : r ≤ 1 := hin.r1.trans hr1R
  have ha1_4 : toR cell.a1 ≤ 4 := by
    have := toR_le_toR.mpr ha4; rw [toR_int_mul_one] at this; exact_mod_cast this
  have hlam4 : lam ≤ 4 := hin.a1.trans ha1_4
  set y := lmass lam T with hydef
  set Y := yF y r with hYdef
  have hy4 : y ≤ 4 := (lmass_le hlam0.le hT0).trans hlam4
  have hypos : 0 < y := lmass_pos hlam0
  -- `λ`, `q`, `α`, `γ`
  have mL : (⟨cell.a0, cell.a1⟩ : Ival).Mem lam := ⟨hin.a0, hin.a1⟩
  have mT : (⟨cell.t0, cell.t1⟩ : Ival).Mem T := ⟨hin.t0, hin.t1⟩
  have p1L : 0 < (add oneI (⟨cell.a0, cell.a1⟩ : Ival)).lo := by
    show 0 < one + cell.a0; omega
  have mq : V.q.Mem (actQ lam) := by
    rw [actQ_eq hlam0.le]
    exact mem_sub mem_oneI (mem_div mem_oneI (mem_add mem_oneI mL) p1L)
  have mal : V.al.Mem (alpha c lam) := mem_mul (mem_ofRat c.aCoef) mq
  have mgam : V.gam.Mem (gamma c lam) := by
    have h := mem_mul (mem_mul mL (mem_add mem_threeI mL)) (mem_ofRat (1 / c.gDen))
    have e : lam * (3 + lam) * (((1 / c.gDen : ℚ)) : ℝ) = gamma c lam := by
      unfold gamma; push_cast; ring
    rw [e] at h; exact h
  -- the child: `v`, `y`, `s`, `σ`, `Y`
  have mE0 : V.E0.Mem (exp (-toR cell.t0)) := by
    have := mem_expPt (-cell.t0); rwa [toR_neg] at this
  have mE1 : V.E1.Mem (exp (-toR cell.t1)) := by
    have := mem_expPt (-cell.t1); rwa [toR_neg] at this
  have meT : (⟨V.E1.lo, V.E0.hi⟩ : Ival).Mem (exp (-T)) :=
    ⟨mE1.1.trans (exp_le_exp.mpr (by linarith [hin.t1])),
      (exp_le_exp.mpr (by linarith [hin.t0])).trans mE0.2⟩
  have mv : V.v.Mem (lam * exp (-T)) := mem_mul mL meT
  have my : V.y.Mem y := mem_logI (mem_add mem_oneI mv) hv
  have ms : V.s.Mem (msg lam T) := by
    rw [msg_eq hlam0.le]
    exact mem_sub mem_oneI (mem_div mem_oneI (mem_add mem_oneI mv) hv)
  have msig : V.sig.Mem (msg lam T / y) := by
    rw [hydef, msg_div_lmass hlam0.le]; exact phi_encl my hy
  have mY : V.Y.Mem Y := by
    constructor
    · exact (mem_yFun (mem_pt _) (mem_pt _)).1.trans
        (yF_mono my.1 (my.1.trans hy4) hin.r0 hrr1)
    · exact (yF_mono my.2 hy4 hin.r1 hr1R).trans (mem_yFun (mem_pt _) (mem_pt _)).2
  -- the parent: `R` at the corners, `p`, `y₀`, `ρ`
  have mc0 : V.yc0.Mem (lmass (toR cell.a0) (toR cell.t0)) :=
    mem_logI (mem_add mem_oneI (mem_mul (mem_pt cell.a0) mE0)) hc0
  have mc1 : V.yc1.Mem (lmass (toR cell.a1) (toR cell.t1)) :=
    mem_logI (mem_add mem_oneI (mem_mul (mem_pt cell.a1) mE1)) hc1
  have ha0R : 0 < toR cell.a0 := toR_pos.mpr ha0
  have mR : V.R.Mem (lam * exp (-Y)) := by
    have hRf : lam * exp (-Y) = Rf lam T r := rfl
    rw [hRf]
    constructor
    · have h1 := (mem_mul (mem_pt cell.a0) (mem_expPt (-(yFun V.yc0 (pt cell.r1)).hi))).1
      rw [toR_neg] at h1
      have h2 := (mem_yFun mc0 (mem_pt cell.r1)).2
      have h3 : toR cell.a0 * exp (-toR (yFun V.yc0 (pt cell.r1)).hi) ≤
          Rf (toR cell.a0) (toR cell.t0) (toR cell.r1) := by
        unfold Rf
        exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) ha0R.le
      have h4 := Rf_corner_lo ha0R hin.a0 (toR_nonneg.mpr ht0) hin.t0 hrr0 hin.r1 hrr1
        (hin.a0.trans hlam4)
      exact h1.trans (h3.trans h4)
    · have h1 := (mem_mul (mem_pt cell.a1) (mem_expPt (-(yFun V.yc1 (pt cell.r0)).lo))).2
      rw [toR_neg] at h1
      have h2 := (mem_yFun mc1 (mem_pt cell.r0)).1
      have ha1R : 0 < toR cell.a1 := hlam0.trans_le hin.a1
      have h3 : Rf (toR cell.a1) (toR cell.t1) (toR cell.r0) ≤
          toR cell.a1 * exp (-toR (yFun V.yc1 (pt cell.r0)).lo) := by
        unfold Rf
        exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) ha1R.le
      have h4 := Rf_corner_hi hlam0 hin.a1 hT0 hin.t1 hrr0 hin.r0 hrr1 ha1_4
      exact h4.trans (h3.trans h1)
  have p1R : 0 < (add oneI V.R).lo := by show 0 < one + V.R.lo; omega
  have momp : V.omp.Mem (1 - msg lam Y) := by
    rw [one_sub_msg hlam0.le]; exact mem_div mem_oneI (mem_add mem_oneI mR) p1R
  have mp : V.p.Mem (msg lam Y) := by
    have := mem_sub mem_oneI momp; rwa [sub_sub_cancel] at this
  have my0 : V.y0.Mem (lmass lam Y) := mem_logI (mem_add mem_oneI mR) p1R
  have mrho : V.rho.Mem (msg lam Y / lmass lam Y) := by
    rw [msg_div_lmass hlam0.le]; exact phi_encl my0 hy0
  -- the composites
  have mh : V.h.Mem (hF c lam Y) := mem_add momp (mem_mul mgam mrho)
  have mJ : V.J.Mem (coefJ lam T) := by
    rw [coefJ_eq]; exact mem_mul (mem_mul ms msig) mT
  have mLp : V.Lp.Mem (LpF c lam Y) := mem_sub (mem_div mgam mR hR) (mem_mul mh mY)
  have mLL : V.L.Mem (coefL c lam Y) := by
    apply mem_meet
    · rw [coefL_eq']; exact mem_sub (mem_mul mgam momp) (mem_mul (mem_mul mp mh) mY)
    · rw [coefL_eq c lam Y hlam0]; exact mem_mul mp mLp
  have mZb : V.Zb.Mem (ZbF c lam T Y) := mem_add mgam (mem_mul mJ mLp)
  -- `α E`
  have mEd : V.Ed.Mem (coefE lam T Y) := by
    rw [coefE_eq]; exact mem_sub (mem_add momp (mem_mul mp (mem_div mT my hy))) (mem_div my0 mY hY)
  have maE : V.aE.Mem (alpha c lam * coefE lam T Y) := mem_mul mal mEd
  -- `(Q0)`
  have hp0 : 0 < msg lam Y := msg_pos hlam0
  have hZb0 : 0 < ZbF c lam T Y := (toR_pos.mpr hZb).trans_le mZb.1
  refine ⟨?_, ?_, ?_⟩
  · rw [coefZ_eq c lam T Y hlam0]
    exact mul_pos hp0 hZb0
  -- `(QC)`
  · rcases hC with (hL | hLp) | hCC
    · left; exact (toR_nonneg.mpr hL).trans mLL.1
    · left
      rw [coefL_eq c lam Y hlam0]
      exact mul_nonneg hp0.le ((toR_nonneg.mpr hLp).trans mLp.1)
    · right
      have mC : V.C.Mem (alpha c lam * coefE lam T Y +
          gamma c lam * coefL c lam Y * (msg lam T / y) ^ 2 / ZbF c lam T Y) :=
        mem_add maE (mem_div (mem_mul (mem_mul mgam mLL) (mem_sqI msig)) mZb hZb)
      rw [compC_eq c lam T Y hlam0]
      exact (toR_nonneg.mpr hCC).trans mC.1
  -- `(QB)`
  · have mD : K.Dm1.Mem ((c.D : ℝ) - 1) := by
      have := mem_ofRat (c.D - 1)
      rw [show (((c.D - 1 : ℚ)) : ℝ) = (c.D : ℝ) - 1 by push_cast; ring] at this
      exact this
    have mKq : V.Kq.Mem ((actQ lam * ((c.D : ℝ) - 1) + msg lam Y -
        gamma c lam * (msg lam Y / lmass lam Y)) / Y - hF c lam Y ^ 2 * coefJ lam T / ZbF c lam T Y) :=
      mem_sub (mem_div (mem_sub (mem_add (mem_mul mq mD) mp) (mem_mul mgam mrho)) mY hY)
        (mem_div (mem_mul (mem_sqI mh) mJ) mZb hZb)
    have mB : V.B.Mem (alpha c lam * coefE lam T Y + msg lam Y * ((actQ lam * ((c.D : ℝ) - 1) +
        msg lam Y - gamma c lam * (msg lam Y / lmass lam Y)) / Y -
          hF c lam Y ^ 2 * coefJ lam T / ZbF c lam T Y)) :=
      mem_add maE (mem_mul mp mKq)
    rw [compB_eq c lam T Y hlam0]
    exact (toR_nonneg.mpr hB).trans mB.1

end Erdos993Lean.Analytic.Reserve.Cert
