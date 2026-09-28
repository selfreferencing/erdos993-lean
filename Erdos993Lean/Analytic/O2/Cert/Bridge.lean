import Mathlib
import Erdos993Lean.Analytic.O2.Cert.CoverSound
import Erdos993Lean.Analytic.O2.Leaf

/-!
# O2 certificate checker (lane A18): from the certified cells to `LocalPaymentOK` and `LeafOK`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The checker works with the real functions of its band
data (`SegData`); here they are identified with lane A16's (`Erdos993Lean/Analytic/O2/Defs.lean`):

* `Matches sd b`: the checker's tables are the band's; `BandFacts sd`: `λ ∈ [1/3, 7/3]`, `γ ≥ 0` and the zero
  knot values `u₈ = v₈ = s₈ = 0` (all decidable on the data);
* **`phi_eq_payK`**: for `p = qx`, `r = 1 − qY`, `t = qτ`, `0 < x < 1`, A16's payment `Φ` (eq. (11)) is the
  checker's `payK`, in both branches of the own coefficients (the kernel branch through `kR`, with `j = 0` in the
  packing for `x ≥ 7/8`, `packJ_kern`); **`phi_leaf_payK`**: the same at the leaf `x = 1`, `z = 1` (A16's
  `packPhi_actQ`, `logG_actQ`);
* **`phi_nonneg_of_point`**: A16's parent-knot reduction `phi_nonneg_of_knots` (with `t_lo = 1 − r`,
  `t_hi = qP = λ(1−p)/(1+λ(1−p))`, `thi_eq`) turns a certified point into `Φ ≥ 0` at every physical record;
* **`localPaymentOK_of_checks`**, **`leafOK_of_checks`**: twelve passing root-box checks of a band give A16's
  `LocalPaymentOK` and `LeafOK`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The checker's band tables are A16's -/

/-- The rational data of a checker band are those of an O2 band. -/
structure Matches (sd : SegData) (b : BandData) : Prop where
  lo : sd.lo = b.lo
  hi : sd.hi = b.hi
  gamma : sd.gamma = b.gamma
  u : ∀ i : Fin 9, sd.Lu[(i : ℕ)]! = b.left.u i ∧ sd.Ru[(i : ℕ)]! = b.right.u i
  v : ∀ i : Fin 9, sd.Lv[(i : ℕ)]! = b.left.v i ∧ sd.Rv[(i : ℕ)]! = b.right.v i
  s : ∀ i : Fin 9, sd.Ls[(i : ℕ)]! = b.left.s i ∧ sd.Rs[(i : ℕ)]! = b.right.s i
  tau : ∀ i : Fin 9, sd.Ltau[(i : ℕ)]! = b.left.tau i ∧ sd.Rtau[(i : ℕ)]! = b.right.tau i
  w : sd.Lw = b.left.w ∧ sd.Rw = b.right.w
  ell : sd.Lell = b.left.ell ∧ sd.Rell = b.right.ell

/-- The range and sign facts of a checker band used by the bridge (all decidable on the data). -/
structure BandFacts (sd : SegData) : Prop where
  lo : (1 / 3 : ℚ) ≤ sd.lo
  hi : sd.hi ≤ 7 / 3
  gamma : 0 ≤ sd.gamma
  u8 : sd.Lu[8]! = 0 ∧ sd.Ru[8]! = 0
  v8 : sd.Lv[8]! = 0 ∧ sd.Rv[8]! = 0
  s8 : sd.Ls[8]! = 0 ∧ sd.Rs[8]! = 0

section Bridge

variable {sd : SegData} {b : BandData}

theorem lerpR_eq_lerp (lo hi a c : ℚ) (l : ℝ) : lerpR lo hi a c l = lerp lo hi a c l := by
  unfold lerpR lerp; push_cast; try ring

theorem pR_eq (l x : ℝ) : pR l x = actQ l * x := by unfold pR; rw [qR_eq_actQ]

theorem fieldR_eq_pwLin (hm : Matches sd b) (sel : CoeffTable → Fin 9 → ℚ) (L R : Array ℚ)
    (h : ∀ i : Fin 9, L[(i : ℕ)]! = sel b.left i ∧ R[(i : ℕ)]! = sel b.right i) (l w : ℝ) :
    fieldR sd L R l w = pwLin (b.knots sel l) w := by
  unfold fieldR BandData.knots
  congr 1
  funext i
  rw [(h i).1, (h i).2, hm.lo, hm.hi, lerpR_eq_lerp]

/-- A16's field at `p = qw` is the checker's field at `w`. -/
theorem field_eq (hm : Matches sd b) (sel : CoeffTable → Fin 9 → ℚ) (L R : Array ℚ)
    (h : ∀ i : Fin 9, L[(i : ℕ)]! = sel b.left i ∧ R[(i : ℕ)]! = sel b.right i) {l : ℝ} (hl : 0 < l) (w : ℝ) :
    b.field sel l (actQ l * w) = fieldR sd L R l w := by
  rw [fieldR_eq_pwLin hm sel L R h]
  unfold BandData.field
  have : actQ l ≠ 0 := by unfold actQ; positivity
  congr 1
  field_simp

theorem field_kern (L R : Array ℚ) (h8 : L[8]! = 0 ∧ R[8]! = 0) {l x : ℝ} (hx : 7 / 8 ≤ x) (hx1 : x ≤ 1) :
    fieldR sd L R l x = lerpR sd.lo sd.hi L[7]! R[7]! l * 8 * (1 - x) := by
  unfold fieldR
  rw [pwLin_eq_cell _ 7 (by norm_num) (by push_cast; linarith) (by push_cast; linarith)]
  have e8 : lerpR sd.lo sd.hi L[8]! R[8]! l = 0 := by rw [h8.1, h8.2]; unfold lerpR; simp
  simp only [e8]
  push_cast
  ring

theorem le1R_pos {l x : ℝ} (hl : 0 < l) (hx1 : x ≤ 1) : 0 < le1R l x := by
  unfold le1R; nlinarith

theorem logMass_eq {l x : ℝ} (hl : 0 < l) (hx0 : 0 < x) (hx1 : x < 1) :
    logMass l (pR l x) = Real.log (le1R l x / x) := by
  unfold logMass
  congr 1
  unfold le1R pR qR
  have h1 : l + 1 ≠ 0 := by positivity
  have h2 : x ≠ 0 := hx0.ne'
  have h3 : l ≠ 0 := hl.ne'
  field_simp
  ring

theorem logMass_kern {l x : ℝ} (hl : 0 < l) (hl7 : l ≤ 7 / 3) (hx : 7 / 8 ≤ x) (hx1 : x < 1) :
    logMass l (pR l x) = (1 - x) * kR (1 - x) l := by
  rw [logMass_eq hl (by linarith) hx1, kR_mul (by linarith) (by linarith) hl.le (by nlinarith),
    ← Real.log_div (by nlinarith) (by linarith)]
  congr 1
  unfold le1R
  ring_nf

theorem packJ_kern {l x : ℝ} (hl : 1 / 3 ≤ l) (hx : 7 / 8 ≤ x) (hx1 : x < 1) : packJ l (pR l x) = 0 := by
  unfold packJ
  rw [Nat.floor_eq_zero]
  have hL : 0 < Real.log (1 + l) := Real.log_pos (by linarith)
  rw [div_lt_one hL, logMass_eq (by linarith) (by linarith) hx1]
  apply Real.log_lt_log (div_pos (le1R_pos (by linarith) hx1.le) (by linarith))
  rw [div_lt_iff₀ (by linarith)]
  unfold le1R
  nlinarith

theorem exp_logMass {l x : ℝ} (hl : 0 < l) (hx0 : 0 < x) (hx1 : x < 1) :
    Real.exp (logMass l (pR l x)) = le1R l x / x := by
  rw [logMass_eq hl hx0 hx1, Real.exp_log (div_pos (le1R_pos hl hx1.le) hx0)]

/-- The own coefficients of the kernel branch are A16's (`7/8 ≤ x < 1`, `u₈ = v₈ = s₈ = 0`). -/
theorem own_kern (L R : Array ℚ) (h8 : L[8]! = 0 ∧ R[8]! = 0) {l x : ℝ} (hl0 : 0 < l) (hl7 : l ≤ 7 / 3)
    (hx : 7 / 8 ≤ x) (hx1 : x < 1) :
    fieldR sd L R l x / (pR l x * logMass l (pR l x)) =
      lerpR sd.lo sd.hi L[7]! R[7]! l * 8 / (pR l x * kR (1 - x) l) := by
  rw [field_kern L R h8 hx hx1.le, logMass_kern hl0 hl7 hx hx1]
  have he : 1 - x ≠ 0 := by linarith
  have hp : pR l x ≠ 0 := by unfold pR qR; have : 0 < x := by linarith
                             positivity
  by_cases hk : kR (1 - x) l = 0
  · rw [hk]; simp
  · field_simp

theorem so_kern (L R : Array ℚ) (h8 : L[8]! = 0 ∧ R[8]! = 0) {l x : ℝ} (hl : 1 / 3 ≤ l) (hx : 7 / 8 ≤ x)
    (hx1 : x < 1) :
    fieldR sd L R l x / packH l (pR l x) = lerpR sd.lo sd.hi L[7]! R[7]! l * 8 * x / (l + 1) := by
  have hl0 : 0 < l := by linarith
  have hx0 : 0 < x := by linarith
  rw [field_kern L R h8 hx hx1.le]
  unfold packH packRes
  rw [packJ_kern hl hx hx1]
  simp only [Nat.cast_zero, zero_mul, sub_zero, zero_add]
  rw [exp_logMass hl0 hx0 hx1]
  unfold le1R
  have he : 1 - x ≠ 0 := by linarith
  have h1 : l + 1 ≠ 0 := by positivity
  have h2 : (l * (1 - x) + 1) / x - 1 = (1 - x) * (l + 1) / x := by field_simp; ring
  rw [h2]
  field_simp

theorem phi_kern {l x : ℝ} (hl : 1 / 3 ≤ l) (hx : 7 / 8 ≤ x) (hx1 : x < 1) :
    packPhi l (pR l x) = (l + 1) * (1 - x) / le1R l x := by
  have hl0 : 0 < l := by linarith
  have hx0 : 0 < x := by linarith
  unfold packPhi packRes
  rw [packJ_kern hl hx hx1]
  simp only [Nat.cast_zero, zero_mul, sub_zero, zero_add]
  rw [Real.exp_neg, exp_logMass hl0 hx0 hx1]
  have hle := le1R_pos hl0 hx1.le
  unfold le1R at *
  field_simp
  ring

theorem omp_eq {l x : ℝ} (hl : 0 < l) : 1 - pR l x = le1R l x / (l + 1) := by
  unfold pR qR le1R
  have h1 : l + 1 ≠ 0 := by positivity
  field_simp
  try ring

theorem logG_eq {l x : ℝ} (hl : 0 < l) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    logG l (pR l x) = Real.log ((l + 1) * x / (le1R l x * le1R l x)) := by
  unfold logG
  congr 1
  have hle := le1R_pos hl hx1
  rw [omp_eq hl]
  have hp : pR l x = l * x / (l + 1) := by unfold pR qR; ring
  rw [hp, div_pow]
  have h1 : l + 1 ≠ 0 := by positivity
  have h3 : l ≠ 0 := hl.ne'
  have h5 : le1R l x ≠ 0 := hle.ne'
  field_simp
  try ring

/-- **The local payment in the checker's variables** (`p = qx`, `r = 1 − qY`, `t = qτ`, `0 < x < 1`): A16's `Φ`
is the checker's `payK` (for either branch of the own coefficients, the kernel branch for `x ≥ 7/8`). -/
theorem phi_eq_payK (hm : Matches sd b) (hf : BandFacts sd) (kern : Bool) {l x Y τ z : ℝ}
    (hl0 : (sd.lo : ℝ) ≤ l) (hl1 : l ≤ sd.hi) (hx0 : 0 < x) (hx1 : x < 1) (hk : kern = true → 7 / 8 ≤ x) :
    b.Phi l (actQ l * x) (1 - actQ l * Y) (actQ l * τ) z = payK sd kern l x Y τ z := by
  have hlo' : ((1 / 3 : ℚ) : ℝ) ≤ (sd.lo : ℝ) := Rat.cast_le.mpr hf.lo
  have hhi' : (sd.hi : ℝ) ≤ ((7 / 3 : ℚ) : ℝ) := Rat.cast_le.mpr hf.hi
  norm_num at hlo' hhi'
  have hlo : (1 / 3 : ℝ) ≤ l := le_trans hlo' hl0
  have hhi : l ≤ 7 / 3 := hl1.trans hhi'
  have hl : 0 < l := by linarith
  have hq : qR l = actQ l := qR_eq_actQ l
  -- own coefficients
  have hAu : b.uF l (pR l x) / (pR l x * logMass l (pR l x)) = auR sd kern l x := by
    unfold BandData.uF
    rw [pR_eq, field_eq hm CoeffTable.u sd.Lu sd.Ru hm.u hl, ← pR_eq]
    cases kern
    · simp only [auR, Bool.false_eq_true, if_false]; rw [logMass_eq hl hx0 hx1]
    · simp only [auR, if_true]; exact own_kern sd.Lu sd.Ru hf.u8 hl hhi (hk rfl) hx1
  have hAv : b.vF l (pR l x) / (pR l x * logMass l (pR l x)) = avR sd kern l x := by
    unfold BandData.vF
    rw [pR_eq, field_eq hm CoeffTable.v sd.Lv sd.Rv hm.v hl, ← pR_eq]
    cases kern
    · simp only [avR, Bool.false_eq_true, if_false]; rw [logMass_eq hl hx0 hx1]
    · simp only [avR, if_true]; exact own_kern sd.Lv sd.Rv hf.v8 hl hhi (hk rfl) hx1
  have hso : b.sF l (pR l x) / packH l (pR l x) = soR sd kern l x := by
    unfold BandData.sF
    rw [pR_eq, field_eq hm CoeffTable.s sd.Ls sd.Rs hm.s hl, ← pR_eq]
    cases kern
    · simp only [soR, Bool.false_eq_true, if_false]
    · simp only [soR, if_true]; exact so_kern sd.Ls sd.Rs hf.s8 hlo (hk rfl) hx1
  have hphi : packPhi l (pR l x) = phiR kern l x := by
    cases kern
    · simp only [phiR, Bool.false_eq_true, if_false]
    · simp only [phiR, if_true]; exact phi_kern hlo (hk rfl) hx1
  -- parent and own fields, multipliers
  have hut : b.uF l (actQ l * τ) = fieldR sd sd.Lu sd.Ru l τ := field_eq hm CoeffTable.u sd.Lu sd.Ru hm.u hl τ
  have hvt : b.vF l (actQ l * τ) = fieldR sd sd.Lv sd.Rv l τ := field_eq hm CoeffTable.v sd.Lv sd.Rv hm.v hl τ
  have hst : b.sF l (actQ l * τ) = fieldR sd sd.Ls sd.Rs l τ := field_eq hm CoeffTable.s sd.Ls sd.Rs hm.s hl τ
  have htt : b.tauF l (actQ l * τ) = fieldR sd sd.Ltau sd.Rtau l τ :=
    field_eq hm CoeffTable.tau sd.Ltau sd.Rtau hm.tau hl τ
  have htp : b.tauF l (pR l x) = fieldR sd sd.Ltau sd.Rtau l x := by
    rw [pR_eq]; exact field_eq hm CoeffTable.tau sd.Ltau sd.Rtau hm.tau hl x
  have hw : b.wF l = lerpR sd.lo sd.hi sd.Lw sd.Rw l := by
    unfold BandData.wF; rw [lerpR_eq_lerp, hm.lo, hm.hi, hm.w.1, hm.w.2]
  have hell : b.ellF l = lerpR sd.lo sd.hi sd.Lell sd.Rell l := by
    unfold BandData.ellF; rw [lerpR_eq_lerp, hm.lo, hm.hi, hm.ell.1, hm.ell.2]
  have hC : b.price l = 1 / (l + 1) * (sd.gamma : ℝ) := by
    unfold BandData.price; rw [hm.gamma]; ring
  have hG := logG_eq hl hx0 hx1.le
  have hh : hFun (pR l x) = pR l x / -Real.log (1 - pR l x) := rfl
  -- assemble
  rw [← pR_eq]
  unfold BandData.Phi BandData.Ru BandData.Rv BandData.Rs BandData.Rtau Rw payK payE
  rw [← hAu, ← hAv, ← hso, ← hphi, hut, hvt, hst, htt, htp, hw, hell, hC, hG, hq]
  unfold hFun
  ring

end Bridge

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

section Final

variable {sd : SegData} {b : BandData}

/-- **The leaf payment in the checker's variables** (`x = 1`, `z = 1`). -/
theorem phi_leaf_payK (hm : Matches sd b) (kern : Bool) {l Y τ : ℝ} (hl : 0 < l) :
    b.Phi l (actQ l) (1 - actQ l * Y) (actQ l * τ) 1 = payK sd kern l 1 Y τ 1 := by
  have hp1 : pR l 1 = actQ l := by rw [pR_eq, mul_one]
  have hphi : phiR kern l 1 = 0 := by
    cases kern
    · simp only [phiR, Bool.false_eq_true, if_false]; rw [hp1]; exact packPhi_actQ hl
    · simp only [phiR, if_true]; simp
  have hG : Real.log ((l + 1) * 1 / (le1R l 1 * le1R l 1)) = logG l (actQ l) := by
    rw [logG_actQ hl]; unfold le1R; congr 1; ring
  have hut : b.uF l (actQ l * τ) = fieldR sd sd.Lu sd.Ru l τ := field_eq hm CoeffTable.u sd.Lu sd.Ru hm.u hl τ
  have hvt : b.vF l (actQ l * τ) = fieldR sd sd.Lv sd.Rv l τ := field_eq hm CoeffTable.v sd.Lv sd.Rv hm.v hl τ
  have hst : b.sF l (actQ l * τ) = fieldR sd sd.Ls sd.Rs l τ := field_eq hm CoeffTable.s sd.Ls sd.Rs hm.s hl τ
  have htt : b.tauF l (actQ l * τ) = fieldR sd sd.Ltau sd.Rtau l τ :=
    field_eq hm CoeffTable.tau sd.Ltau sd.Rtau hm.tau hl τ
  have htp : b.tauF l (actQ l) = fieldR sd sd.Ltau sd.Rtau l 1 := by
    have := field_eq hm CoeffTable.tau sd.Ltau sd.Rtau hm.tau hl 1; rwa [mul_one] at this
  have hw : b.wF l = lerpR sd.lo sd.hi sd.Lw sd.Rw l := by
    unfold BandData.wF; rw [lerpR_eq_lerp, hm.lo, hm.hi, hm.w.1, hm.w.2]
  have hell : b.ellF l = lerpR sd.lo sd.hi sd.Lell sd.Rell l := by
    unfold BandData.ellF; rw [lerpR_eq_lerp, hm.lo, hm.hi, hm.ell.1, hm.ell.2]
  have hC : b.price l = 1 / (l + 1) * (sd.gamma : ℝ) := by
    unfold BandData.price; rw [hm.gamma]; ring
  have e1 : max ((1 : ℝ) - 1) 0 = 0 := by norm_num
  have e2 : max (-(1 : ℝ)) 0 = 0 := by norm_num
  have e3 : max (1 : ℝ) 0 = 1 := by norm_num
  unfold BandData.Phi BandData.Ru BandData.Rv BandData.Rs BandData.Rtau Rw payK payE
  rw [hphi, ← hG, hp1, packPhi_actQ hl, hut, hvt, hst, htt, htp, hw, hell, hC, qR_eq_actQ, e1, e2, e3]
  unfold hFun
  ring

/-- `qP = λ(1 − p)/(1 + λ(1 − p))`: the parent's upper bound of Lemma 1 at `p = qx`. -/
theorem thi_eq {l x : ℝ} (hl : 0 < l) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    l * (1 - actQ l * x) / (1 + l * (1 - actQ l * x)) = actQ l * upR l x := by
  have hq0 : 0 < actQ l := by unfold actQ; positivity
  have hq1 : actQ l < 1 := by unfold actQ; rw [div_lt_one (by linarith)]; linarith
  have hql : actQ l * (1 + l) = l := by unfold actQ; field_simp
  have hd1 : 0 < 1 + l * (1 - actQ l * x) := by nlinarith
  have hd2 : 0 < 1 - actQ l * (actQ l * x) := by nlinarith
  unfold upR pR
  rw [qR_eq_actQ, mul_div_assoc', div_eq_div_iff hd1.ne' hd2.ne']
  linear_combination (-(1 - actQ l * x)) * hql

/-- **The knot reduction for a certified point**: if `(λ, x)` is certified, then `Φ ≥ 0` at every physical
record with `p = qx` (every response if `x < 1`, `z = 1` at `x = 1`). -/
theorem phi_nonneg_of_point {l x p r t z : ℝ} (hl : 0 < l) (hx0 : 0 < x) (hx1 : x ≤ 1) (hp : p = actQ l * x)
    (hphys : PhysRecord l p r t)
    (hpt : ∀ Y τ, 0 ≤ Y → Y ≤ upR l x → ParentCase (upR l x) Y τ → 0 ≤ b.Phi l p (1 - actQ l * Y) (actQ l * τ) z) :
    0 ≤ b.Phi l p r t z := by
  obtain ⟨hp0, -, hr1, ht1, ht2, -⟩ := hphys
  have hq : 0 < actQ l := by unfold actQ; positivity
  have hP1 := upR_lt_one hl hx0 hx1
  have hP0 := upR_pos hl hx0 hx1
  have hthi : l * (1 - p) / (1 + l * (1 - p)) = actQ l * upR l x := by rw [hp]; exact thi_eq hl hx0 hx1
  set Y := (1 - r) / actQ l with hYdef
  have hr : r = 1 - actQ l * Y := by rw [hYdef]; field_simp; ring
  have hY0 : 0 ≤ Y := div_nonneg (by linarith) hq.le
  have hYP : Y ≤ upR l x := by
    rw [hYdef, div_le_iff₀ hq]; nlinarith [ht1.trans ht2]
  have key : ∀ τ, ParentCase (upR l x) Y τ → 0 ≤ b.Phi l p r (actQ l * τ) z := by
    intro τ hτ; rw [hr]; exact hpt Y τ hY0 hYP hτ
  refine b.phi_nonneg_of_knots (tlo := 1 - r) (thi := l * (1 - p) / (1 + l * (1 - p))) hq (by linarith)
    (by rw [hthi]; nlinarith) ?_ ?_ ?_ ht1 ht2
  · have := key Y (Or.inl rfl)
    rwa [show actQ l * Y = 1 - r by rw [hr]; ring] at this
  · rw [hthi]; exact key (upR l x) (Or.inr (Or.inl rfl))
  · intro j hj8 hj1 hj2
    rw [show actQ l * (j : ℝ) / 8 = actQ l * ((j : ℝ) / 8) by ring] at hj1 hj2 ⊢
    rw [hthi] at hj2
    have hjP : (j : ℝ) / 8 ≤ upR l x := le_of_mul_le_mul_left hj2 hq
    have hYj : Y ≤ (j : ℝ) / 8 := by
      have : actQ l * Y ≤ actQ l * ((j : ℝ) / 8) := by linarith [hr, hj1]
      exact le_of_mul_le_mul_left this hq
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      have hY : Y = 0 := le_antisymm (by simpa using hYj) hY0
      exact key _ (Or.inl (by rw [hY]; simp))
    · by_cases h8 : j = 8
      · subst h8; norm_num at hjP; linarith
      · exact key _ (Or.inr (Or.inr ⟨j, hpos, by omega, hYj, hjP, rfl⟩))

/-- **The certified local payment of a band** from its twelve root-box checks. -/
theorem localPaymentOK_of_checks (hm : Matches sd b) (hf : BandFacts sd) (hxmin : b.xmin = 1 / 65536)
    {toks : List String} (hc : ∀ i < 12, checkRoot sd i (toks.getD i "") = true) : b.LocalPaymentOK := by
  intro l hlam p r t z hphys hxm hpq
  have hlo' : ((1 / 3 : ℚ) : ℝ) ≤ (sd.lo : ℝ) := Rat.cast_le.mpr hf.lo
  norm_num at hlo'
  have hl0 : (sd.lo : ℝ) ≤ l := by rw [hm.lo]; exact hlam.1
  have hl1 : l ≤ sd.hi := by rw [hm.hi]; exact hlam.2
  have hl : 0 < l := by linarith
  have hγ : 0 ≤ (sd.gamma : ℝ) := by exact_mod_cast hf.gamma
  have hq : 0 < actQ l := by unfold actQ; positivity
  set x := p / actQ l with hxdef
  have hp : p = actQ l * x := by rw [hxdef]; field_simp
  have hx0 : (1 / 65536 : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ hq]; rw [hxmin] at hxm; push_cast at hxm; linarith
  have hx1 : x < 1 := by rw [hxdef, div_lt_one hq]; exact hpq
  obtain ⟨kern, hk, hgood⟩ := band_good hγ hc hl0 hl1 hx0 hx1.le
  refine phi_nonneg_of_point hl (by linarith) hx1.le hp hphys (fun Y τ h1 h2 h3 => ?_)
  rw [hp, phi_eq_payK hm hf kern hl0 hl1 (by linarith) hx1 hk]
  exact hgood Y τ z h1 h2 h3

/-- **The leaf endpoint of a band** from its twelve root-box checks. -/
theorem leafOK_of_checks (hm : Matches sd b) (hf : BandFacts sd) {toks : List String}
    (hc : ∀ i < 12, checkRoot sd i (toks.getD i "") = true) : b.LeafOK := by
  intro l hlam r t hphys
  have hlo' : ((1 / 3 : ℚ) : ℝ) ≤ (sd.lo : ℝ) := Rat.cast_le.mpr hf.lo
  norm_num at hlo'
  have hl0 : (sd.lo : ℝ) ≤ l := by rw [hm.lo]; exact hlam.1
  have hl1 : l ≤ sd.hi := by rw [hm.hi]; exact hlam.2
  have hl : 0 < l := by linarith
  have hγ : 0 ≤ (sd.gamma : ℝ) := by exact_mod_cast hf.gamma
  obtain ⟨kern, -, hgood⟩ := band_good hγ hc hl0 hl1 (by norm_num) le_rfl
  refine phi_nonneg_of_point hl one_pos le_rfl (by ring) hphys (fun Y τ h1 h2 h3 => ?_)
  rw [phi_leaf_payK hm kern hl]
  exact hgood Y τ 1 h1 h2 h3

end Final

end Erdos993Lean.Analytic.O2.Cert
