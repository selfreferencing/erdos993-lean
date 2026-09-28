import Mathlib
import Erdos993Lean.Analytic.TailCert.Cells

/-!
# Soundness of the cell checker of the repaired T3 potential (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  Sources: `SOUL/O3/repaired_potential_proof.md`
§"Positive-domain interval checker" and §"Unbounded domains", `SOUL/O3/certify_repaired_potential.py`,
`LEAN/referee/REVIEW_SOUL_ROUND2.md` item 3.

**Theorem (`checkBand_sound`).**  If `checkBand l0 l1 a ℓ z = true` (the computable checker of
`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`), then `Tail.T3UNonneg λ z a ℓ` holds for
every activity `λ ∈ [l0, l1]`.

The domain `Y_B > 0`, `Y_C ≥ 0` is covered by four pieces: `Y_B ≥ 30` (`tailB_sound`: the gain is
at least `ρ Y_B − log(1 + λ)`, the x-part at least `Y_B I` with `ρ + I > 0`), and for `Y_B ≤ 30` the
line `Y_C = 0` (`coverLine_sound`), the rectangle `0 < Y_C ≤ 30` (`coverRect_sound`) and the strip
`Y_C ≥ 30` (`coverStrip_sound`), each an adaptive bisection whose accepted cells are sound
(`lineOK_sound`, `rectOK_sound`, `stripOK_sound`: `U = gain + H + Y_B ψ_c(x)`, `T3U_split`, with
each term bounded below by the corresponding interval computation).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.TailCert

open Compute Tail

section CellSound

variable {S : Setup}

/-- `T3U = [gain − a L(p_c)] + [(a − k) Y_C + [Y_C > 0] k That_+(Y_C)] + Y_B ψ_c(x)`. -/
theorem T3U_split (lam z a ell YB YC x : ℝ) :
    T3U lam z a ell YB YC x =
      (-Real.log (pC lam (YB + YC) + (1 - pC lam (YB + YC)) * Real.exp (-(rFallback lam z * YB))) -
        a * Lf (pC lam (YB + YC))) +
      ((a - kK lam a) * YC + (if 0 < YC then kK lam a * ThatPlus lam YC else 0)) +
      YB * psiF lam a (T3c lam ell (YB + YC)) x := by
  unfold T3U T3A
  rw [T3phi_div_Lf]
  ring

/-- `λ e^{−(Y_B + Y_C)} ≤ l1 e^{−b0} e^{−c0}` (the upper bound `W` of the rectangle). -/
theorem W_bound (hS : BandOK S) {lam YB YC b0 c0 : ℝ} {EB EC : Ival} (hlam : InBand S lam)
    (hEB : EB.Mem (Real.exp (-b0))) (hEC : EC.Mem (Real.exp (-c0))) (hb : b0 ≤ YB) (hc : c0 ≤ YC) :
    lam * Real.exp (-(YB + YC)) ≤ toR (mul S.L1 (mul EB EC)).hi := by
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hm := (mem_mul hS.memL1 (mem_mul hEB hEC)).2
  refine le_trans ?_ hm
  rw [← Real.exp_add]
  exact mul_le_mul hlam.2 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    (hlam0.le.trans hlam.2)

/-- `e^{−ρ Y_B} ≤ Er` for `Y_B ≥ b0 ≥ 0`. -/
theorem E_bound (hS : BandOK S) {B0 : Coord} (hB0 : CoordOK S B0) (hb0 : 0 ≤ B0.b) {lam YB : ℝ}
    (hlam : InBand S lam) (hYB : toR B0.b ≤ YB) :
    Real.exp (-(rFallback lam S.z * YB)) ≤ toR B0.er.hi := by
  refine le_trans ?_ hB0.er.2
  apply Real.exp_le_exp.mpr
  have h1 := hS.rhole lam hlam
  have h2 : 0 ≤ toR B0.b := toR_nonneg.mpr hb0
  nlinarith [hS.rho0]

/-- **The line cell** `Y_C = 0`, `Y_B ∈ [b0, b1]`. -/
theorem lineOK_sound (hS : BandOK S) {B0 B1 : Coord} (hB0 : CoordOK S B0) (hB1 : CoordOK S B1)
    (h : lineOK S B0 B1 = true) {lam YB x : ℝ} (hlam : InBand S lam) (hYB0 : 0 < YB)
    (hb0 : toR B0.b ≤ YB) (hb1 : YB ≤ toR B1.b) (hx0 : 0 < x) (hxq : x ≤ actQ lam)
    (hxY : x ≤ 1 - Real.exp (-YB)) : 0 ≤ T3U lam S.z S.a S.ell YB 0 x := by
  simp only [lineOK, lineChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hg, hh⟩, hq⟩, hB0b⟩, hval⟩ := h
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hW : lam * Real.exp (-(YB + 0)) ≤ toR (mul S.L1 B0.eb).hi := by
    refine le_trans ?_ (mem_mul hS.memL1 hB0.eb).2
    rw [add_zero]
    exact mul_le_mul hlam.2 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (hlam0.le.trans hlam.2)
  have hgain := gainVal_le hS hg hlam hYB0.le hW (E_bound hS hB0 hB0b hlam hb0)
  have hc := T3c_le_cfOf hS hh hlam (s := YB + 0) (s1 := toR B1.b) (by linarith) hB1.eb.1
  have hx := xpartVal_le hS hB1 hq hlam hYB0 hb1 hc.1 hc.2 hx0 hxq hxY
  rw [T3U_split]
  unfold lineVal at hval
  rw [← toR_nonneg, toR_add] at hval
  simp only [mul_zero, lt_irrefl, if_false, add_zero] at hgain hx ⊢
  linarith

/-- **The rectangle** `Y_B ∈ [b0, b1]`, `Y_C ∈ [c0, c1]`, `Y_C > 0`. -/
theorem rectOK_sound (hS : BandOK S) {B0 B1 C0 C1 : Coord} (hB0 : CoordOK S B0)
    (hB1 : CoordOK S B1) (hC0 : CoordOK S C0) (hC1 : CoordOK S C1)
    (h : rectOK S B0 B1 C0 C1 = true) {lam YB YC x : ℝ} (hlam : InBand S lam) (hYB0 : 0 < YB)
    (hb0 : toR B0.b ≤ YB) (hb1 : YB ≤ toR B1.b) (hYC0 : 0 < YC) (hc0 : toR C0.b ≤ YC)
    (hc1 : YC ≤ toR C1.b) (hx0 : 0 < x) (hxq : x ≤ actQ lam) (hxY : x ≤ 1 - Real.exp (-YB)) :
    0 ≤ T3U lam S.z S.a S.ell YB YC x := by
  simp only [rectOK, rectChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hg, hh⟩, hq⟩, hB0b⟩, hC0b⟩, hval⟩ := h
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hW := W_bound hS hlam hB0.eb hC0.eb hb0 hc0
  have hgain := gainVal_le hS hg hlam hYB0.le hW (E_bound hS hB0 hB0b hlam hb0)
  have hU : toR (mul B1.eb C1.eb).lo ≤ Real.exp (-(toR B1.b + toR C1.b)) := by
    have := (mem_mul hB1.eb hC1.eb).1
    rwa [← Real.exp_add, ← neg_add] at this
  have hc := T3c_le_cfOf hS hh hlam (s := YB + YC) (by linarith) hU
  have hx := xpartVal_le hS hB1 hq hlam hYB0 hb1 hc.1 hc.2 hx0 hxq hxY
  -- the C-children credit
  have hk0 : 0 ≤ kK lam S.a := kK_nonneg hlam0 hS.a0
  have hk1 := hS.lek1 lam hlam
  have hH : toR (HVal S C0 C1) ≤
      (S.a - kK lam S.a) * YC + (if 0 < YC then kK lam S.a * ThatPlus lam YC else 0) := by
    rw [if_pos hYC0]
    unfold HVal
    rw [toR_add]
    have h1 := (mem_mul (mem_sub hS.memA (mem_pt S.k1)) (mem_pt C0.b)).1
    have hc0R : 0 ≤ toR C0.b := toR_nonneg.mpr hC0b
    have hak : 0 ≤ S.a - toR S.k1 := by linarith [hS.k1le]
    have h1' : (S.a - toR S.k1) * toR C0.b ≤ (S.a - kK lam S.a) * YC :=
      mul_le_mul (by linarith) hc0 hc0R (by linarith)
    have h2 : toR (if C1.thok && decide (0 < C1.th) then (mul (pt S.k0) (pt C1.th)).lo else 0) ≤
        kK lam S.a * ThatPlus lam YC := by
      split_ifs with hth
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hth
        obtain ⟨hthok, hthpos⟩ := hth
        obtain ⟨_, hthle⟩ := hC1.th hthok
        have hm := (mem_mul (mem_pt S.k0) (mem_pt C1.th)).1
        refine hm.trans ?_
        have hthR : 0 < toR C1.th := toR_pos.mpr hthpos
        have hT : toR C1.th ≤ ThatPlus lam YC :=
          hthle.trans ((That_mono hS.l0pos hlam.1 hYC0 hc1).trans (That_le_ThatPlus _ _))
        exact mul_le_mul (hS.k0le lam hlam) hT hthR.le hk0
      · rw [toR_zero]; exact mul_nonneg hk0 (ThatPlus_nonneg _ _)
    linarith
  rw [T3U_split]
  unfold rectVal at hval
  rw [← toR_nonneg, toR_add, toR_add] at hval
  linarith

/-- **The strip** `Y_B ∈ [b0, b1]`, `Y_C ≥ 30`. -/
theorem stripOK_sound (hS : BandOK S) {B0 B1 : Coord} (hB0 : CoordOK S B0) (hB1 : CoordOK S B1)
    (h : stripOK S B0 B1 = true) {lam YB YC x : ℝ} (hlam : InBand S lam) (hYB0 : 0 < YB)
    (hb0 : toR B0.b ≤ YB) (hb1 : YB ≤ toR B1.b) (hYC : 30 ≤ YC) (hx0 : 0 < x)
    (hxq : x ≤ actQ lam) (hxY : x ≤ 1 - Real.exp (-YB)) :
    0 ≤ T3U lam S.z S.a S.ell YB YC x := by
  simp only [stripOK, stripChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg, hq⟩, hB0b⟩, hval⟩ := h
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hW := W_bound hS hlam hB0.eb hS.e30 hb0 hYC
  have hgain := gainVal_le hS hg hlam hYB0.le hW (E_bound hS hB0 hB0b hlam hb0)
  have hc := T3c_le_cAll hS hlam (s := YB + YC)
  have hx := xpartVal_le hS hB1 hq hlam hYB0 hb1 hc.1 hc.2 hx0 hxq hxY
  have hk0 : 0 ≤ kK lam S.a := kK_nonneg hlam0 hS.a0
  have hk1 := hS.lek1 lam hlam
  have hH : toR (mul (sub S.A (pt S.k1)) (pt (30 * one))).lo ≤
      (S.a - kK lam S.a) * YC + (if 0 < YC then kK lam S.a * ThatPlus lam YC else 0) := by
    rw [if_pos (by linarith)]
    have h1 := (mem_mul (mem_sub hS.memA (mem_pt S.k1)) (mem_pt (30 * one))).1
    rw [toR_intMul_one] at h1
    have hak : 0 ≤ S.a - toR S.k1 := by linarith [hS.k1le]
    have h1' : (S.a - toR S.k1) * ((30 : ℤ) : ℝ) ≤ (S.a - kK lam S.a) * YC :=
      mul_le_mul (by linarith) (by push_cast; exact hYC) (by norm_num) (by linarith)
    have h2 : 0 ≤ kK lam S.a * ThatPlus lam YC := mul_nonneg hk0 (ThatPlus_nonneg _ _)
    linarith
  rw [T3U_split]
  unfold stripVal at hval
  rw [← toR_nonneg, toR_add, toR_add] at hval
  linarith

end CellSound

/-! ## The covers -/

section Covers

variable {S : Setup}

theorem coverLine_sound (hS : BandOK S) : ∀ (f : ℕ) (B0 B1 : Coord), CoordOK S B0 →
    CoordOK S B1 → coverLine S f B0 B1 = true →
    ∀ lam, InBand S lam → ∀ YB x, toR B0.b ≤ YB → YB ≤ toR B1.b → 0 < YB → 0 < x →
      x ≤ actQ lam → x ≤ 1 - Real.exp (-YB) → 0 ≤ T3U lam S.z S.a S.ell YB 0 x := by
  intro f
  induction f with
  | zero =>
    intro B0 B1 hB0 hB1 h lam hlam YB x hb0 hb1 hYB hx0 hxq hxY
    exact lineOK_sound hS hB0 hB1 h hlam hYB hb0 hb1 hx0 hxq hxY
  | succ f ih =>
    intro B0 B1 hB0 hB1 h lam hlam YB x hb0 hb1 hYB hx0 hxq hxY
    simp only [coverLine, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact lineOK_sound hS hB0 hB1 h hlam hYB hb0 hb1 hx0 hxq hxY
    · have hM : CoordOK S (mid S B0 B1) := mkCoord_ok hS ((B0.b + B1.b) >>> (1 : ℕ))
      rcases le_total YB (toR (mid S B0 B1).b) with hm | hm
      · exact ih B0 _ hB0 hM h1 lam hlam YB x hb0 hm hYB hx0 hxq hxY
      · exact ih _ B1 hM hB1 h2 lam hlam YB x hm hb1 hYB hx0 hxq hxY

theorem coverStrip_sound (hS : BandOK S) : ∀ (f : ℕ) (B0 B1 : Coord), CoordOK S B0 →
    CoordOK S B1 → coverStrip S f B0 B1 = true →
    ∀ lam, InBand S lam → ∀ YB YC x, toR B0.b ≤ YB → YB ≤ toR B1.b → 0 < YB → 30 ≤ YC →
      0 < x → x ≤ actQ lam → x ≤ 1 - Real.exp (-YB) → 0 ≤ T3U lam S.z S.a S.ell YB YC x := by
  intro f
  induction f with
  | zero =>
    intro B0 B1 hB0 hB1 h lam hlam YB YC x hb0 hb1 hYB hYC hx0 hxq hxY
    exact stripOK_sound hS hB0 hB1 h hlam hYB hb0 hb1 hYC hx0 hxq hxY
  | succ f ih =>
    intro B0 B1 hB0 hB1 h lam hlam YB YC x hb0 hb1 hYB hYC hx0 hxq hxY
    simp only [coverStrip, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact stripOK_sound hS hB0 hB1 h hlam hYB hb0 hb1 hYC hx0 hxq hxY
    · have hM : CoordOK S (mid S B0 B1) := mkCoord_ok hS ((B0.b + B1.b) >>> (1 : ℕ))
      rcases le_total YB (toR (mid S B0 B1).b) with hm | hm
      · exact ih B0 _ hB0 hM h1 lam hlam YB YC x hb0 hm hYB hYC hx0 hxq hxY
      · exact ih _ B1 hM hB1 h2 lam hlam YB YC x hm hb1 hYB hYC hx0 hxq hxY

theorem coverRect_sound (hS : BandOK S) : ∀ (f : ℕ) (B0 B1 C0 C1 : Coord), CoordOK S B0 →
    CoordOK S B1 → CoordOK S C0 → CoordOK S C1 → coverRect S f B0 B1 C0 C1 = true →
    ∀ lam, InBand S lam → ∀ YB YC x, toR B0.b ≤ YB → YB ≤ toR B1.b → toR C0.b ≤ YC →
      YC ≤ toR C1.b → 0 < YB → 0 < YC → 0 < x → x ≤ actQ lam → x ≤ 1 - Real.exp (-YB) →
      0 ≤ T3U lam S.z S.a S.ell YB YC x := by
  intro f
  induction f with
  | zero =>
    intro B0 B1 C0 C1 hB0 hB1 hC0 hC1 h lam hlam YB YC x hb0 hb1 hc0 hc1 hYB hYC hx0 hxq hxY
    exact rectOK_sound hS hB0 hB1 hC0 hC1 h hlam hYB hb0 hb1 hYC hc0 hc1 hx0 hxq hxY
  | succ f ih =>
    intro B0 B1 C0 C1 hB0 hB1 hC0 hC1 h lam hlam YB YC x hb0 hb1 hc0 hc1 hYB hYC hx0 hxq hxY
    simp only [coverRect, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · exact rectOK_sound hS hB0 hB1 hC0 hC1 h hlam hYB hb0 hb1 hYC hc0 hc1 hx0 hxq hxY
    · have hMB : CoordOK S (mid S B0 B1) := mkCoord_ok hS ((B0.b + B1.b) >>> (1 : ℕ))
      have hMC : CoordOK S (mid S C0 C1) := mkCoord_ok hS ((C0.b + C1.b) >>> (1 : ℕ))
      rcases le_total YB (toR (mid S B0 B1).b) with hm | hm <;>
        rcases le_total YC (toR (mid S C0 C1).b) with hn | hn
      · exact ih B0 _ C0 _ hB0 hMB hC0 hMC h1 lam hlam YB YC x hb0 hm hc0 hn hYB hYC hx0 hxq hxY
      · exact ih B0 _ _ C1 hB0 hMB hMC hC1 h3 lam hlam YB YC x hb0 hm hn hc1 hYB hYC hx0 hxq hxY
      · exact ih _ B1 C0 _ hMB hB1 hC0 hMC h2 lam hlam YB YC x hm hb1 hc0 hn hYB hYC hx0 hxq hxY
      · exact ih _ B1 _ C1 hMB hB1 hMC hC1 h4 lam hlam YB YC x hm hb1 hn hc1 hYB hYC hx0 hxq hxY

end Covers

/-! ## The tail `Y_B ≥ 30` -/

theorem tailB_sound {S : Setup} (hS : BandOK S) (h : tailBOK S = true) {lam YB YC x : ℝ}
    (hlam : InBand S lam) (hYB : 30 ≤ YB) (hYC : 0 ≤ YC) (hx0 : 0 < x) (hxq : x ≤ actQ lam) :
    0 ≤ T3U lam S.z S.a S.ell YB YC x := by
  simp only [tailBOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hq, hri⟩, hX⟩, htB⟩ := h
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  set I := queryVal S S.q1hi S.cAll
  have hc := T3c_le_cAll hS hlam (s := YB + YC)
  have hI : toR I ≤ psiF lam S.a (T3c lam S.ell (YB + YC)) x :=
    query_sound hS.toConstOK hS.arr hS.allp hS.tiny hS.dC hq hlam hc.1 hc.2 hx0
      (hxq.trans (hS.q1 lam hlam))
  have hρ1 := rFallback_le_one hlam0 hS.z0 (z := S.z)
  have hρ0 := rFallback_nonneg hlam0 hS.z0 hS.z1
  have hρ := hS.rhole lam hlam
  set ρ := rFallback lam S.z
  set s := YB + YC
  set E := Real.exp (-(ρ * YB))
  set p := pC lam s
  -- the gain: `−log(p + (1 − p) E) ≥ ρ Y_B − log(1 + λ)`
  have hp0 : 0 < p := pC_pos hlam0 s
  have hp1 : p ≤ lam * Real.exp (-s) := by
    show pC lam s ≤ _
    unfold pC
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hlam0 (Real.exp_pos (-s))]
  have hes : Real.exp (-s) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
  have hE0 : 0 < E := Real.exp_pos _
  have hgainarg : p + (1 - p) * E ≤ (1 + lam) * E := by nlinarith
  have hG : ρ * YB - Real.log (1 + lam) ≤ -Real.log (p + (1 - p) * E) := by
    have h1 : 0 < p + (1 - p) * E := by nlinarith [pC_lt_one hlam0 s]
    have h2 := Real.log_le_log h1 hgainarg
    rw [Real.log_mul (by linarith) hE0.ne', Real.log_exp] at h2
    linarith
  have hlog1 : Real.log (1 + lam) ≤ toR S.log1l1.hi :=
    (Real.log_le_log (by linarith) (by linarith [hlam.2])).trans hS.log1l1
  -- the term `−a L(p_c)`
  have hXmem : (add (pt one) (mul S.L1 S.e30)).Mem (1 + S.l1 * Real.exp (-30)) := by
    have := mem_add (mem_pt one) (mem_mul hS.memL1 hS.e30); rwa [toR_one] at this
  have hlogX := mem_mul hS.memA (mem_logI hXmem hX)
  have hLp : Lf p ≤ Real.log (1 + S.l1 * Real.exp (-30)) := by
    rw [Lf_pC hlam0]
    apply Real.log_le_log (by positivity)
    have : Real.exp (-s) ≤ Real.exp (-30) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.exp_pos (-s), hlam.2, hlam0]
  have haL : S.a * Real.log (1 + S.l1 * Real.exp (-30)) ≤ toR (mul S.A (logI (add (pt one) (mul S.L1 S.e30)))).hi :=
    hlogX.2
  -- the C-children credit
  have hk1 := hS.lek1 lam hlam
  have hk0 : 0 ≤ kK lam S.a := kK_nonneg hlam0 hS.a0
  have hH : 0 ≤ (S.a - kK lam S.a) * YC + (if 0 < YC then kK lam S.a * ThatPlus lam YC else 0) := by
    have h1 : 0 ≤ (S.a - kK lam S.a) * YC := mul_nonneg (by linarith [hS.k1le]) hYC
    split_ifs
    · exact add_nonneg h1 (mul_nonneg hk0 (ThatPlus_nonneg _ _))
    · simpa using h1
  -- the table value
  have hri' : 0 < toR S.rho + toR I := by rw [← toR_add]; exact toR_pos.mpr hri
  have hYBpsi : YB * toR I ≤ YB * psiF lam S.a (T3c lam S.ell (YB + YC)) x :=
    mul_le_mul_of_nonneg_left hI (by linarith)
  -- the final number
  have htB' : 0 ≤ 30 * (toR S.rho + toR I) - toR S.log1l1.hi -
      toR (mul S.A (logI (add (pt one) (mul S.L1 S.e30)))).hi := by
    have h1 := (toR_nonneg.mpr htB)
    unfold sub at h1
    simp only [toR_sub] at h1
    have h2 := (mem_mul (mem_pt (30 * one)) (mem_pt (S.rho + I))).1
    rw [toR_intMul_one, toR_add] at h2
    push_cast at h2
    linarith
  rw [T3U_split]
  have haLf : -(S.a * Lf p) ≥ -(S.a * Real.log (1 + S.l1 * Real.exp (-30))) := by
    have := mul_le_mul_of_nonneg_left hLp hS.a0; linarith
  have hrhoYB : toR S.rho * YB ≤ ρ * YB := mul_le_mul_of_nonneg_right hρ (by linarith)
  nlinarith

/-! ## The band theorem -/

/-- **Soundness of the band check**: `checkBand l0 l1 a ell z = true` implies the reduced unit
inequality `Tail.T3UNonneg λ z a ℓ` at every activity `λ ∈ [l0, l1]`. -/
theorem checkBand_sound {l0 l1 a ell z : ℚ} (h : checkBand l0 l1 a ell z = true) :
    ∀ lam : ℝ, (l0 : ℝ) ≤ lam → lam ≤ l1 → T3UNonneg lam z a ell := by
  intro lam hl0 hl1
  set S := mkSetup l0 l1 a ell z with hSdef
  simp only [checkBand, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hset, hline⟩, hrect⟩, hstrip⟩, htail⟩ := h
  have hS := bandOK_of_setupOK hset
  have hlam : InBand S lam := ⟨hl0, hl1⟩
  have hB0 := mkCoord_ok hS 0
  have hB1 := mkCoord_ok hS (30 * one)
  have h0 : toR (mkCoord S 0).b = 0 := toR_zero
  have h30 : toR (mkCoord S (30 * one)).b = 30 := by
    show toR (30 * one) = 30; simpa using toR_intMul_one 30
  intro YB YC x hYB hYC hx0 hxq hxY
  show 0 ≤ T3U lam S.z S.a S.ell YB YC x
  rcases le_or_gt 30 YB with hB | hB
  · exact tailB_sound hS htail hlam hB hYC hx0 hxq
  rcases eq_or_lt_of_le hYC with hC | hC
  · subst hC
    exact coverLine_sound hS fuel _ _ hB0 hB1 hline lam hlam YB x (by rw [h0]; exact hYB.le)
      (by rw [h30]; exact hB.le) hYB hx0 hxq hxY
  rcases le_or_gt YC 30 with hC' | hC'
  · exact coverRect_sound hS fuel _ _ _ _ hB0 hB1 hB0 hB1 hrect lam hlam YB YC x
      (by rw [h0]; exact hYB.le) (by rw [h30]; exact hB.le) (by rw [h0]; exact hC.le)
      (by rw [h30]; exact hC') hYB hC hx0 hxq hxY
  · exact coverStrip_sound hS fuel _ _ hB0 hB1 hstrip lam hlam YB YC x
      (by rw [h0]; exact hYB.le) (by rw [h30]; exact hB.le) hYB hC'.le hx0 hxq hxY

end Erdos993Lean.Analytic.TailCert
