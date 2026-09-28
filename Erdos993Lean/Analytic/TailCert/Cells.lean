import Mathlib
import Erdos993Lean.Analytic.TailCert.Table

/-!
# The band constants, the coordinates and the terms of the cell bound: soundness (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.

* `bandOK_of_setupOK`: when `setupOK (mkSetup l0 l1 a ℓ z)` passes, the band constants are sound
  for every `λ ∈ [l0, l1]` (`BandOK`): `k0 ≤ a r(λ) ≤ k1 ≤ a`, `rho ≤ ρ(λ, z)`, `ℓ/q(λ) ≤ cAll`,
  `q(λ) ≤ q1hi`, the grid cells and the table (`ArrOK`, `pcellOK`, `tinyOK`), `e^{−30} ∈ e30`;
* `mkCoord_ok`: the data of a coordinate (`CoordOK`): `e^{−b} ∈ eb`, `e^{−ρ b} ∈ er`,
  `min(q, 1 − e^{−b}) ≤ pm`, `th ≤ That_{l0}(b)` (when `thok`);
* `gainVal_le`: `gainVal ≤ −log(p_c + (1 − p_c) e^{−ρ Y_B}) − a L(p_c)` (`gain_anti`, `pC_le_of_le`);
* `T3c_le_cfOf`, `T3c_le_cAll`: `0 ≤ c(λ, s) ≤ cf` (`hmin_pC_ge`);
* `xpartVal_le`: `xpartVal ≤ Y_B ψ_c(x)` — the table bound `b1 I` (`query_sound`, `I ≤ 0`) and the
  near bound `a That_{l0}(b1)_+ − (k1 + cf) b1` (from `T_λ(x) ≥ That_λ(Y_B) ≥ That_{l0}(b1)`,
  `L(x) ≤ Y_B`, `x ≤ L(x)`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.TailCert

open Compute Tail

/-! ## The band constants -/

theorem toR_intMul_one (k : ℤ) : toR (k * one) = k := by
  unfold toR; rw [one_eq]; push_cast; field_simp

theorem sqrtPt_lo_nonneg (n : ℤ) : 0 ≤ (sqrtPt n).lo := by
  unfold sqrtPt
  simp only
  split_ifs <;> simp

/-- `r(λ) ∈ rI λ`. -/
theorem rI_mem (l : ℚ) (h0 : 0 ≤ (ofRat (1 + 4 * l)).lo) : (rI l).Mem (rK l) := by
  have hs := mem_sqrtI (mem_ofRat (1 + 4 * l)) h0
  have hadd := mem_add (mem_pt one) hs
  have hpos : 0 < (add (pt one) (sqrtI (ofRat (1 + 4 * l)))).lo := by
    show 0 < one + (sqrtPt (ofRat (1 + 4 * l)).lo).lo
    have := sqrtPt_lo_nonneg (ofRat (1 + 4 * l)).lo
    have h1 : (0 : ℤ) < one := by decide
    omega
  have hdiv := mem_div (mem_pt (2 * one)) hadd hpos
  have hsub := mem_sub (mem_pt one) hdiv
  have e2 : toR (2 * one) = 2 := by simpa using toR_intMul_one 2
  rw [toR_one, e2] at hsub
  unfold rI rK
  convert hsub using 3
  push_cast
  ring

/-- The facts about a band setup that the cells use. -/
structure BandOK (S : Setup) : Prop extends ConstOK S where
  arr : ArrOK S
  l0l1 : (S.l0 : ℝ) ≤ S.l1
  l1six : (S.l1 : ℝ) ≤ 6
  z0 : (0 : ℝ) ≤ S.z
  z1 : (S.z : ℝ) ≤ 1
  ell0 : (0 : ℝ) ≤ S.ell
  k1le : toR S.k1 ≤ S.a
  rhole : ∀ lam, InBand S lam → toR S.rho ≤ rFallback lam S.z
  rho0 : 0 ≤ toR S.rho
  cAll : ∀ lam, InBand S lam → S.ell / actQ lam ≤ toR S.cAll
  q1 : ∀ lam, InBand S lam → actQ lam ≤ toR S.q1hi
  dC : 0 < S.dC
  allp : allLt S.N (pcellOK S) = true
  tiny : tinyOK S = true
  e30 : S.e30.Mem (Real.exp (-30))
  log1l1 : Real.log (1 + S.l1) ≤ toR S.log1l1.hi

/-- **The band constants are sound** when `setupOK` passes. -/
theorem bandOK_of_setupOK {l0 l1 a ell z : ℚ} (h : setupOK (mkSetup l0 l1 a ell z) = true) :
    BandOK (mkSetup l0 l1 a ell z) := by
  set S := mkSetup l0 l1 a ell z with hSdef
  simp only [setupOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩ := h
  have hl0 : (0 : ℝ) < S.l0 := by exact_mod_cast h1
  have hl01 : (S.l0 : ℝ) ≤ S.l1 := by exact_mod_cast h2
  have hl1 : (0 : ℝ) < S.l1 := hl0.trans_le hl01
  have ha : (0 : ℝ) ≤ S.a := by exact_mod_cast h6
  have hz0 : (0 : ℝ) ≤ S.z := by exact_mod_cast h4
  have hz1 : (S.z : ℝ) ≤ 1 := by exact_mod_cast h5
  have hell : (0 : ℝ) ≤ S.ell := by exact_mod_cast h7
  have memA : S.A.Mem S.a := mem_ofRat a
  have memL0 : S.L0.Mem S.l0 := mem_ofRat l0
  have memL1 : S.L1.Mem S.l1 := mem_ofRat l1
  have hlam0 : ∀ lam, InBand S lam → 0 < lam := fun lam hlam => hl0.trans_le hlam.1
  have hk0' : toR S.k0 ≤ S.a * rK S.l0 := (mem_mul memA (rI_mem l0 h14)).1
  have hk1' : S.a * rK S.l1 ≤ toR S.k1 := (mem_mul memA (rI_mem l1 h15)).2
  refine
    { l0pos := hl0, a0 := ha, memA := memA, memL0 := memL0, memL1 := memL1,
      k0le := ?_, lek1 := ?_, k0nn := toR_nonneg.mpr h8, q0 := ?_, arr := arrOK_mkSetup _ _ _ _ _,
      l0l1 := hl01, l1six := by exact_mod_cast h3, z0 := hz0, z1 := hz1, ell0 := hell,
      k1le := (toR_le_toR.mpr h9).trans memA.1, rhole := ?_, rho0 := ?_, cAll := ?_, q1 := ?_,
      dC := h10, allp := h16, tiny := h17, e30 := ?_, log1l1 := ?_ }
  · intro lam hlam
    exact hk0'.trans (mul_le_mul_of_nonneg_left (rK_mono hlam.1) ha)
  · intro lam hlam
    exact (mul_le_mul_of_nonneg_left (rK_mono hlam.2) ha).trans hk1'
  · intro lam hlam
    have hq := (mem_ofRat (l0 / (1 + l0))).1
    have : (((l0 / (1 + l0) : ℚ)) : ℝ) = actQ (S.l0 : ℝ) := by unfold actQ; push_cast; rfl
    rw [this] at hq
    exact hq.trans (actQ_mono hl0.le hlam.1)
  · intro lam hlam
    have hN := mem_logI (mem_ofRat ((1 + l1) / (1 + l1 * z))) h13
    have hD := mem_logI (mem_ofRat (1 + l1)) h12
    have hq := mem_div hN hD h11
    have heq : Real.log (((1 + l1) / (1 + l1 * z) : ℚ) : ℝ) / Real.log (((1 + l1 : ℚ)) : ℝ) =
        rFallback (S.l1 : ℝ) S.z := by
      unfold rFallback; push_cast; rfl
    rw [heq] at hq
    have hr0 := rFallback_nonneg hl1 hz0 hz1
    have hmono := rFallback_anti (hlam0 lam hlam) hlam.2 hz0 hz1
    show toR (rhoOf l1 z) ≤ _
    unfold rhoOf
    rw [toR_max, toR_zero]
    exact max_le (hq.1.trans hmono) (hr0.trans hmono)
  · show 0 ≤ toR (rhoOf l1 z)
    unfold rhoOf
    rw [toR_max, toR_zero]
    exact le_max_right _ _
  · intro lam hlam
    have hc := (mem_ofRat (ell * (1 + l0) / l0)).2
    have hl0' : (l0 : ℝ) ≠ 0 := hl0.ne'
    have : (((ell * (1 + l0) / l0 : ℚ)) : ℝ) = (ell : ℝ) / actQ (l0 : ℝ) := by
      unfold actQ; push_cast
      field_simp
    rw [this] at hc
    refine le_trans ?_ hc
    exact div_le_div_of_nonneg_left hell (actQ_pos hl0) (actQ_mono hl0.le hlam.1)
  · intro lam hlam
    have hq := (mem_ofRat (l1 / (1 + l1))).2
    have : (((l1 / (1 + l1) : ℚ)) : ℝ) = actQ (S.l1 : ℝ) := by unfold actQ; push_cast; rfl
    rw [this] at hq
    exact (actQ_mono (hlam0 lam hlam).le hlam.2).trans hq
  · have := mem_expPt (-(30 * one))
    rwa [toR_neg, toR_intMul_one] at this
  · have hl1' : (0 : ℝ) < l1 := hl1
    have := le_logI_hi (mem_ofRat (1 + l1)) (by push_cast; linarith)
    push_cast at this
    exact this

/-! ## Coordinates -/

section Coords

variable {S : Setup}

/-- The data of a coordinate `b` are enclosures of the functions of `b` the cells use. -/
structure CoordOK (S : Setup) (B : Coord) : Prop where
  eb : B.eb.Mem (Real.exp (-toR B.b))
  er : B.er.Mem (Real.exp (-(toR S.rho * toR B.b)))
  pm : ∀ lam, InBand S lam → ∀ x, x ≤ actQ lam → x ≤ 1 - Real.exp (-toR B.b) → x ≤ toR B.pm
  th : B.thok = true → 0 < toR B.b ∧ toR B.th ≤ That S.l0 (toR B.b)

theorem mkCoord_ok (hS : BandOK S) (b : ℤ) : CoordOK S (mkCoord S b) := by
  have heb : (expPt (-b)).Mem (Real.exp (-toR b)) := by
    have := mem_expPt (-b); rwa [toR_neg] at this
  refine ⟨heb, ?_, ?_, ?_⟩
  · have := mem_expI (mem_neg (mem_mul (mem_pt S.rho) (mem_pt b)))
    exact this
  · intro lam hlam x hxq hxb
    have hbb : (mkCoord S b).b = b := rfl
    rw [hbb] at hxb
    show x ≤ toR (min S.q1hi (one - (expPt (-b)).lo))
    rw [toR_min, toR_sub, toR_one]
    exact le_min (hxq.trans (hS.q1 lam hlam)) (hxb.trans (by linarith [heb.1]))
  · intro hth
    show 0 < toR b ∧ toR (logI (thArg S.L0 (expPt (-b)))).lo ≤ That S.l0 (toR b)
    simp only [mkCoord, Bool.and_eq_true, decide_eq_true_eq] at hth
    obtain ⟨⟨⟨hb, he⟩, hd⟩, hta⟩ := hth
    have hbR : 0 < toR b := toR_pos.mpr hb
    refine ⟨hbR, ?_⟩
    have hden : (thDen (expPt (-b))).Mem (Real.exp (toR b) - 1) := by
      have := mem_sub (mem_div (mem_pt one) heb he) (mem_pt one)
      rw [toR_one, Real.exp_neg, one_div, inv_inv] at this
      simpa using this
    have harg := mem_div hS.memL0 hden hd
    rw [That_eq hS.l0pos hbR]
    exact logI_lo_le harg hta

end Coords

/-! ## The cells -/

section CellBounds

variable {S : Setup}

/-- **The gain**: `gainVal ≤ −log(p + (1 − p) E) − a L(p)` for `p = p_c(λ, s)`, `E = e^{−ρ Y_B}`. -/
theorem gainVal_le (hS : BandOK S) {W Er : ℤ} (hc : gainChk W Er = true) {lam s YB : ℝ}
    (hlam : InBand S lam) (hYB : 0 ≤ YB) (hW : lam * Real.exp (-s) ≤ toR W)
    (hE : Real.exp (-(rFallback lam S.z * YB)) ≤ toR Er) :
    toR (gainVal S.A W Er) ≤
      -Real.log (pC lam s + (1 - pC lam s) * Real.exp (-(rFallback lam S.z * YB))) -
        S.a * Lf (pC lam s) := by
  simp only [gainChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hW0, harg⟩, hP⟩ := hc
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  set p := pC lam s
  set E := Real.exp (-(rFallback lam S.z * YB))
  have hρ := rFallback_nonneg hlam0 hS.z0 hS.z1
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hp0 : 0 < p := pC_pos hlam0 s
  have hWR : 0 ≤ toR W := toR_nonneg.mpr hW0
  have hpos1 : 0 < (add (pt one) (pt W)).lo := by
    show 0 < one + W
    have : (0 : ℤ) < one := by decide
    omega
  have hPmem := mem_div (mem_pt W) (mem_add (mem_pt one) (mem_pt W)) hpos1
  rw [toR_one] at hPmem
  have hpp : p ≤ toR (pUp W) := (pC_le_of_le hlam0 hW).trans hPmem.2
  have hP1 : toR (pUp W) < 1 := toR_lt_one hP
  -- the gain
  have hg := gain_anti hp0.le hpp hP1.le hE0 hE1 hE
  have hargmem := mem_add (mem_pt (pUp W)) (mem_mul (mem_sub (mem_pt one) (mem_pt (pUp W)))
    (mem_pt Er))
  rw [toR_one] at hargmem
  have hlog := le_logI_hi hargmem ((toR_pos.mpr harg).trans_le hargmem.1)
  -- the term `−a L(p)`
  have hom : 0 < (sub (pt one) (pt (pUp W))).lo := by show 0 < one - pUp W; omega
  have hmL := mem_mul hS.memA (mem_logI (mem_sub (mem_pt one) (mem_pt (pUp W))) hom)
  rw [toR_one] at hmL
  have hLf : Lf p ≤ Lf (toR (pUp W)) := Lf_mono hpp hP1
  have haL : -S.a * Lf p ≥ S.a * Real.log (1 - toR (pUp W)) := by
    unfold Lf at hLf ⊢
    nlinarith [hS.a0]
  unfold gainVal
  show toR ((neg (logI (gainArg (pUp W) Er))).lo + _) ≤ _
  rw [toR_add]
  show toR (-(logI (gainArg (pUp W) Er)).hi) + _ ≤ _
  rw [toR_neg]
  have : toR (mul S.A (logI (sub (pt one) (pt (pUp W))))).lo ≤ S.a * Real.log (1 - toR (pUp W)) :=
    hmL.1
  unfold gainArg
  linarith

/-- **The coefficient `c`**: `0 ≤ c(λ, s) ≤ cfOf cAll L0 U1` for `s ≤ s1`, `U1 ≤ e^{−s1}`. -/
theorem T3c_le_cfOf (hS : BandOK S) {U1 : ℤ} (hc : hChk S.L0 U1 = true) {lam s s1 : ℝ}
    (hlam : InBand S lam) (hss : s ≤ s1) (hU : toR U1 ≤ Real.exp (-s1)) :
    0 ≤ T3c lam S.ell s ∧ T3c lam S.ell s ≤ toR (cfOf S.cAll S.L0 U1) := by
  simp only [hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hU0, hden⟩ := hc
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hU0R : 0 ≤ toR U1 := toR_nonneg.mpr hU0
  have hdenmem : (hDen S.L0 U1).Mem (1 + S.l0 + S.l0 * toR U1) := by
    have := mem_add (mem_add (mem_pt one) hS.memL0) (mem_mul hS.memL0 (mem_pt U1))
    rwa [toR_one] at this
  have hhmem := mem_div (mem_mul hS.memL0 (mem_pt U1)) hdenmem hden
  have hexp : Real.exp (-s1) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have hh : toR (hLo S.L0 U1) ≤ hmin lam (pC lam s) :=
    hhmem.1.trans (hmin_pC_ge hS.l0pos hlam.1 hU0R (hU.trans hexp))
  have hq : 0 < actQ lam := actQ_pos hlam0
  have hc1 : 0 ≤ S.ell / actQ lam := div_nonneg hS.ell0 hq.le
  have h1h : 0 ≤ 1 - hmin lam (pC lam s) := by linarith [hmin_pC_le_one hlam0 (s := s)]
  have hcAll := hS.cAll lam hlam
  unfold T3c
  refine ⟨mul_nonneg hc1 h1h, ?_⟩
  have hm := (mem_mul (mem_pt S.cAll) (mem_sub (mem_pt one) (mem_pt (hLo S.L0 U1)))).2
  rw [toR_one] at hm
  refine le_trans ?_ hm
  exact mul_le_mul hcAll (by linarith) h1h (hc1.trans hcAll)

theorem T3c_le_cAll (hS : BandOK S) {lam s : ℝ} (hlam : InBand S lam) :
    0 ≤ T3c lam S.ell s ∧ T3c lam S.ell s ≤ toR S.cAll := by
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hc1 : 0 ≤ S.ell / actQ lam := div_nonneg hS.ell0 (actQ_pos hlam0).le
  have h0 := hmin_pC_nonneg hlam0 (s := s)
  have h1 := hmin_pC_le_one hlam0 (s := s)
  unfold T3c
  refine ⟨mul_nonneg hc1 (by linarith), ?_⟩
  calc S.ell / actQ lam * (1 - hmin lam (pC lam s)) ≤ S.ell / actQ lam * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hc1
    _ ≤ toR S.cAll := by rw [mul_one]; exact hS.cAll lam hlam

/-- **The x-part**: `xpartVal ≤ Y_B ψ_c(x)` (the table bound `b1 I` and the near bound). -/
theorem xpartVal_le (hS : BandOK S) {B1 : Coord} (hB1 : CoordOK S B1) {cf : ℤ}
    (hq : queryChk S B1.pm cf = true) {lam YB c x : ℝ} (hlam : InBand S lam) (hYB0 : 0 < YB)
    (hYB1 : YB ≤ toR B1.b) (hc0 : 0 ≤ c) (hc1 : c ≤ toR cf) (hx0 : 0 < x) (hxq : x ≤ actQ lam)
    (hxY : x ≤ 1 - Real.exp (-YB)) :
    toR (xpartVal S B1 cf) ≤ YB * psiF lam S.a c x := by
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hxb1 : x ≤ 1 - Real.exp (-toR B1.b) :=
    hxY.trans (by linarith [Real.exp_le_exp.mpr (neg_le_neg hYB1)])
  have hxpm := hB1.pm lam hlam x hxq hxb1
  have hI := query_sound hS.toConstOK hS.arr hS.allp hS.tiny hS.dC hq hlam hc0 hc1 hx0 hxpm
  have hI0 : toR (queryVal S B1.pm cf) ≤ 0 := by
    rw [← toR_zero]; exact toR_le_toR.mpr (queryVal_nonpos hS.arr hq hS.dC)
  have hb1 : 0 < toR B1.b := hYB0.trans_le hYB1
  -- the table bound
  have hv : toR (fdivP (B1.b * queryVal S B1.pm cf)) ≤ YB * psiF lam S.a c x := by
    refine (toR_fdivP_le _).trans ?_
    rw [← toR_mul_toR]
    calc toR B1.b * toR (queryVal S B1.pm cf) ≤ YB * toR (queryVal S B1.pm cf) := by nlinarith
      _ ≤ YB * psiF lam S.a c x := mul_le_mul_of_nonneg_left hI hYB0.le
  unfold xpartVal
  split_ifs with hth
  · rw [toR_max]
    refine max_le hv ?_
    obtain ⟨_, hthle⟩ := hB1.th hth
    -- the near bound
    have hxlt1 : x < 1 := hxq.trans_lt (actQ_lt_one hlam0.le)
    have hL : 0 < Lf x := Lf_pos hx0 hxlt1
    have hLY : Lf x ≤ YB := Lf_le_of_le hxY
    have hT0 : 0 ≤ Tf lam x := Tf_nonneg hlam0 hx0 hxq
    have hTth : toR B1.th ≤ Tf lam x :=
      hthle.trans ((That_mono hS.l0pos hlam.1 hYB0 hYB1).trans (That_le_Tf hlam0 hYB0 hx0 hxY))
    have hTmax : max (toR B1.th) 0 ≤ Tf lam x := max_le hTth hT0
    have hk0 : 0 ≤ kK lam S.a := kK_nonneg hlam0 hS.a0
    have hk1 := hS.lek1 lam hlam
    have hind0 : 0 ≤ (if x < actQ lam then kK lam S.a * ThatPlus lam (Tf lam x) else 0) := by
      split_ifs
      · exact mul_nonneg hk0 (ThatPlus_nonneg _ _)
      · exact le_rfl
    have hxL : x ≤ Lf x := le_Lf hxlt1
    have hnum : S.a * Tf lam x ≤ YB / Lf x * (S.a * Tf lam x +
        (if x < actQ lam then kK lam S.a * ThatPlus lam (Tf lam x) else 0)) := by
      have h1 : 1 ≤ YB / Lf x := (one_le_div hL).mpr hLY
      have h2 : 0 ≤ S.a * Tf lam x := mul_nonneg hS.a0 hT0
      nlinarith
    have hpsi : YB * psiF lam S.a c x = YB / Lf x * (S.a * Tf lam x +
        (if x < actQ lam then kK lam S.a * ThatPlus lam (Tf lam x) else 0)) -
        kK lam S.a * YB - c * (x / Lf x) * YB := by
      unfold psiF; field_simp
    have hcx : c * (x / Lf x) * YB ≤ toR cf * toR B1.b := by
      have h1 : x / Lf x ≤ 1 := (div_le_one hL).mpr hxL
      have h2 : c * (x / Lf x) ≤ c := by nlinarith [div_nonneg hx0.le hL.le]
      nlinarith [div_nonneg hx0.le hL.le]
    have hkY : kK lam S.a * YB ≤ toR S.k1 * toR B1.b := mul_le_mul hk1 hYB1 hYB0.le (hk0.trans hk1)
    have hnear : toR (nearVal S B1.th B1.b cf) ≤
        S.a * max (toR B1.th) 0 - (toR S.k1 + toR cf) * toR B1.b := by
      unfold nearVal
      rw [toR_sub]
      have h1 := (mem_mul hS.memA (mem_pt (max B1.th 0))).1
      rw [toR_max, toR_zero] at h1
      have h2 := le_toR_cdivP ((S.k1 + cf) * B1.b)
      rw [← toR_mul_toR, toR_add] at h2
      linarith
    have haT : S.a * max (toR B1.th) 0 ≤ S.a * Tf lam x := mul_le_mul_of_nonneg_left hTmax hS.a0
    rw [hpsi]
    nlinarith
  · exact hv

end CellBounds

end Erdos993Lean.Analytic.TailCert
