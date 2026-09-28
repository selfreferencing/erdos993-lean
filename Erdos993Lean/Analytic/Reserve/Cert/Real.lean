import Mathlib
import Erdos993Lean.Analytic.Reserve.Defs

/-!
# O1's finite box: the real facts behind the cell checker (lane A12)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  Sources: the referee's independent replay of Astra's
O1 cell certificates (`LEAN/referee/REVIEW_ASTRA_O1_REPLAY.md`, `review_replay/o1core.py`), which uses exactly these
monotone enclosures and normalized forms.  The quantities are those of `Erdos993Lean/Analytic/Reserve/Defs.lean`.

* `phiF_anti`: `φ(t) = (1 − e^{−t})/t` decreases on `(0, ∞)` (convexity of `exp`); with
  `one_sub_exp_neg_lmass` (`1 − e^{−lmass λ X} = msg λ X`) it gives the enclosures of `σ = s/y = φ(y)` and
  `ρ = p/y₀ = φ(y₀)`;
* `yF_mono`: `Y = y + (4 − y) r` increases in `y` (for `r ≤ 1`) and in `r` (for `y ≤ 4`);
* `Rf_anti_r`, `Rf_mono_T`, `Rf_mono_lam`: `R(λ, T, r) = λ e^{−Y}` decreases in `r` and increases in `T` and `λ`
  (`log R = log λ − 4r − (1 − r) log(1 + λ e^{−T})`); `Rf_corner_lo`, `Rf_corner_hi`: `R` lies between its values at
  the corners `(λ_lo, T_lo, r_hi)` and `(λ_hi, T_hi, r_lo)` of a cell;
* the normalized forms (`R = λ e^{−Y}`, `p = msg λ Y`, `h = 1 − p + γ p/y₀`, `L/p = γ/R − h Y`,
  `Z̄ = γ + J L/p`): `coefH_eq` (`H = p h`), `coefL_eq` (`L = p · L/p`), `coefL_eq'`, `coefZ_eq` (`Z = p Z̄`),
  `compC_eq` (`C = αE + γ L σ²/Z̄`), `compB_eq` (`B = αE + p[(q(D − 1) + p − γρ)/Y − h² J/Z̄]`), `coefE_eq`,
  `coefJ_eq` (`J = s σ T`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.Reserve.Cert

open Real Erdos993Lean.Analytic Erdos993Lean.Analytic.Reserve

/-! ## `φ(t) = (1 − e^{−t})/t` -/

/-- `φ(t) = (1 − e^{−t})/t`. -/
noncomputable def phiF (t : ℝ) : ℝ := (1 - exp (-t)) / t

/-- **`φ` decreases** on `(0, ∞)`: `e^{−t} ≤ (t/t') e^{−t'} + (1 − t/t')` (convexity of `exp`). -/
theorem phiF_anti {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') : phiF t' ≤ phiF t := by
  have ht' : 0 < t' := ht.trans_le htt
  have hconv := convexOn_exp.2 (Set.mem_univ (-t')) (Set.mem_univ 0)
    (show (0:ℝ) ≤ t / t' from div_nonneg ht.le ht'.le)
    (show (0:ℝ) ≤ 1 - t / t' by rw [sub_nonneg, div_le_one ht']; exact htt)
    (by ring : t / t' + (1 - t / t') = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hconv
  have harg : t / t' * -t' = -t := by field_simp
  rw [harg] at hconv
  have h2 : t' * exp (-t) ≤ t * exp (-t') + (t' - t) := by
    have := mul_le_mul_of_nonneg_left hconv ht'.le
    have e1 : t' * (t / t' * exp (-t') + (1 - t / t')) = t * exp (-t') + (t' - t) := by
      field_simp
    linarith
  unfold phiF
  rw [div_le_div_iff₀ ht' ht]
  nlinarith

/-! ## `Y = y + (4 − y) r` -/

/-- `Y = y + (4 − y) r`. -/
def yF (y r : ℝ) : ℝ := y + (4 - y) * r

/-- `Y(y, r) ≤ Y(y', r')` for `y ≤ y'`, `r ≤ r'`, `y ≤ 4`, `r' ≤ 1`:
`Y(y', r') − Y(y, r) = (y' − y)(1 − r') + (4 − y)(r' − r)`. -/
theorem yF_mono {y y' r r' : ℝ} (hy : y ≤ y') (hy4 : y ≤ 4) (hr : r ≤ r') (hr1 : r' ≤ 1) :
    yF y r ≤ yF y' r' := by
  unfold yF
  nlinarith [mul_nonneg (sub_nonneg.2 hy) (show (0:ℝ) ≤ 1 - r' by linarith),
    mul_nonneg (show (0:ℝ) ≤ 4 - y by linarith) (sub_nonneg.2 hr)]

/-- `Y − y = (4 − y) r`. -/
theorem yF_sub (y r : ℝ) : yF y r - y = (4 - y) * r := by unfold yF; ring

/-! ## The messages -/

theorem one_add_pos {lam X : ℝ} (hlam : 0 ≤ lam) : 0 < 1 + lam * exp (-X) := by
  have := exp_pos (-X); nlinarith

theorem msg_eq {lam X : ℝ} (hlam : 0 ≤ lam) : msg lam X = 1 - 1 / (1 + lam * exp (-X)) := by
  have h := one_add_pos (X := X) hlam
  unfold msg
  field_simp
  ring

theorem one_sub_msg {lam X : ℝ} (hlam : 0 ≤ lam) : 1 - msg lam X = 1 / (1 + lam * exp (-X)) := by
  rw [msg_eq hlam]; ring

theorem exp_neg_lmass {lam X : ℝ} (hlam : 0 ≤ lam) :
    exp (-lmass lam X) = 1 / (1 + lam * exp (-X)) := by
  unfold lmass
  rw [exp_neg, exp_log (one_add_pos hlam), one_div]

/-- `1 − e^{−lmass λ X} = msg λ X`, so `msg λ X / lmass λ X = φ(lmass λ X)`. -/
theorem one_sub_exp_neg_lmass {lam X : ℝ} (hlam : 0 ≤ lam) : 1 - exp (-lmass lam X) = msg lam X := by
  rw [exp_neg_lmass hlam, msg_eq hlam]

theorem msg_div_lmass {lam X : ℝ} (hlam : 0 ≤ lam) : msg lam X / lmass lam X = phiF (lmass lam X) := by
  unfold phiF; rw [one_sub_exp_neg_lmass hlam]

theorem lmass_pos {lam X : ℝ} (hlam : 0 < lam) : 0 < lmass lam X := by
  unfold lmass
  apply log_pos
  have := exp_pos (-X)
  nlinarith [mul_pos hlam this]

theorem lmass_le {lam X : ℝ} (hlam : 0 ≤ lam) (hX : 0 ≤ X) : lmass lam X ≤ lam := by
  unfold lmass
  have h1 := log_le_sub_one_of_pos (one_add_pos (X := X) hlam)
  have h2 : exp (-X) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  nlinarith

theorem lmass_anti {lam X X' : ℝ} (hlam : 0 ≤ lam) (hX : X ≤ X') : lmass lam X' ≤ lmass lam X := by
  unfold lmass
  apply log_le_log (one_add_pos hlam)
  have : exp (-X') ≤ exp (-X) := exp_le_exp.mpr (by linarith)
  nlinarith

theorem msg_pos {lam X : ℝ} (hlam : 0 < lam) : 0 < msg lam X := by
  unfold msg
  have := exp_pos (-X)
  positivity

theorem actQ_eq {lam : ℝ} (hlam : 0 ≤ lam) : actQ lam = 1 - 1 / (1 + lam) := by
  unfold actQ
  field_simp
  ring

/-! ## `R = λ e^{−Y}` -/

/-- `R(λ, T, r) = λ e^{−Y}`, `Y = y + (4 − y) r`, `y = lmass λ T`. -/
noncomputable def Rf (lam T r : ℝ) : ℝ := lam * exp (-yF (lmass lam T) r)

/-- `R` decreases in `r` (for `y ≤ 4`). -/
theorem Rf_anti_r {lam T r r' : ℝ} (hlam : 0 ≤ lam) (hy : lmass lam T ≤ 4) (hr : r ≤ r') :
    Rf lam T r' ≤ Rf lam T r := by
  unfold Rf yF
  apply mul_le_mul_of_nonneg_left _ hlam
  apply exp_le_exp.mpr
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 4 - lmass lam T by linarith) (sub_nonneg.2 hr)]

/-- `R` increases in `T` (for `r ≤ 1`). -/
theorem Rf_mono_T {lam T T' r : ℝ} (hlam : 0 < lam) (hr1 : r ≤ 1) (hT : T ≤ T') :
    Rf lam T r ≤ Rf lam T' r := by
  unfold Rf yF
  apply mul_le_mul_of_nonneg_left _ hlam.le
  apply exp_le_exp.mpr
  have := lmass_anti (lam := lam) hlam.le hT
  nlinarith [mul_nonneg (sub_nonneg.2 this) (show (0:ℝ) ≤ 1 - r by linarith)]

/-- `R` increases in `λ` (for `r ≥ 0`): with `y = log(1 + λu)`, `y' = log(1 + λ'u)`,
`(y' − y)(1 − r) ≤ y' − y ≤ log λ' − log λ`. -/
theorem Rf_mono_lam {lam lam' T r : ℝ} (hlam : 0 < lam) (hll : lam ≤ lam') (hr0 : 0 ≤ r) :
    Rf lam T r ≤ Rf lam' T r := by
  have hlam' : 0 < lam' := hlam.trans_le hll
  set u := exp (-T) with hu
  have hu0 : 0 < u := exp_pos _
  set y := lmass lam T with hy
  set y' := lmass lam' T with hy'
  have h1p : 0 < 1 + lam * u := by nlinarith
  have h1p' : 0 < 1 + lam' * u := by nlinarith
  have hyy : y ≤ y' := by
    rw [hy, hy']; unfold lmass
    exact log_le_log h1p (by nlinarith)
  have hkey : y' - y ≤ log lam' - log lam := by
    have h := log_le_log (mul_pos hlam h1p')
      (show lam * (1 + lam' * u) ≤ lam' * (1 + lam * u) by nlinarith)
    rw [log_mul hlam.ne' h1p'.ne', log_mul hlam'.ne' h1p.ne'] at h
    rw [hy, hy']; unfold lmass
    linarith
  unfold Rf
  rw [← hy, ← hy']
  rw [show lam * exp (-yF y r) = exp (log lam + -yF y r) by rw [exp_add, exp_log hlam],
    show lam' * exp (-yF y' r) = exp (log lam' + -yF y' r) by rw [exp_add, exp_log hlam']]
  apply exp_le_exp.mpr
  unfold yF
  have := mul_le_mul_of_nonneg_left (show 1 - r ≤ 1 by linarith) (sub_nonneg.2 hyy)
  nlinarith

/-- `R(λ_lo, T_lo, r_hi) ≤ R(λ, T, r)` on a cell. -/
theorem Rf_corner_lo {a0 t0 r1 lam T r : ℝ} (ha0 : 0 < a0) (hal : a0 ≤ lam) (ht0 : 0 ≤ t0)
    (htT : t0 ≤ T) (hr0 : 0 ≤ r) (hrr : r ≤ r1) (hr1 : r ≤ 1) (ha4 : a0 ≤ 4) :
    Rf a0 t0 r1 ≤ Rf lam T r :=
  (Rf_anti_r ha0.le ((lmass_le ha0.le ht0).trans ha4) hrr).trans
    ((Rf_mono_T ha0 hr1 htT).trans (Rf_mono_lam ha0 hal hr0))

/-- `R(λ, T, r) ≤ R(λ_hi, T_hi, r_lo)` on a cell. -/
theorem Rf_corner_hi {a1 t1 r0 lam T r : ℝ} (hlam : 0 < lam) (hla : lam ≤ a1) (hT0 : 0 ≤ T)
    (hTt : T ≤ t1) (hr0 : 0 ≤ r) (hrr : r0 ≤ r) (hr1 : r ≤ 1) (ha4 : a1 ≤ 4) :
    Rf lam T r ≤ Rf a1 t1 r0 := by
  have ha1 : 0 < a1 := hlam.trans_le hla
  exact (Rf_mono_lam hlam hla hr0).trans ((Rf_mono_T ha1 hr1 hTt).trans
    (Rf_anti_r ha1.le ((lmass_le ha1.le (hT0.trans hTt)).trans ha4) hrr))

/-! ## The normalized forms -/

section Forms

variable (c : Band)

/-- `h = 1 − p + γ ρ`, `ρ = p/y₀` (`H = p h`). -/
noncomputable def hF (lam Y : ℝ) : ℝ := (1 - msg lam Y) + gamma c lam * (msg lam Y / lmass lam Y)

/-- `L/p = γ/R − h Y`, `R = λ e^{−Y}`. -/
noncomputable def LpF (lam Y : ℝ) : ℝ := gamma c lam / (lam * exp (-Y)) - hF c lam Y * Y

/-- `Z̄ = Z/p = γ + J L/p`. -/
noncomputable def ZbF (lam T Y : ℝ) : ℝ := gamma c lam + coefJ lam T * LpF c lam Y

theorem coefH_eq (lam Y : ℝ) : coefH c lam Y = msg lam Y * hF c lam Y := by
  unfold coefH hF; ring

theorem msg_div_R (lam Y : ℝ) (hlam : 0 < lam) : msg lam Y / (lam * exp (-Y)) = 1 - msg lam Y := by
  have hR : 0 < lam * exp (-Y) := mul_pos hlam (exp_pos _)
  unfold msg
  field_simp
  ring

theorem coefL_eq (lam Y : ℝ) (hlam : 0 < lam) : coefL c lam Y = msg lam Y * LpF c lam Y := by
  have h1 := msg_div_R lam Y hlam
  unfold coefL LpF
  rw [coefH_eq]
  linear_combination (-(gamma c lam)) * h1

theorem coefL_eq' (lam Y : ℝ) : coefL c lam Y =
    gamma c lam * (1 - msg lam Y) - msg lam Y * hF c lam Y * Y := by
  unfold coefL; rw [coefH_eq]

theorem coefZ_eq (lam T Y : ℝ) (hlam : 0 < lam) : coefZ c lam T Y = msg lam Y * ZbF c lam T Y := by
  unfold coefZ ZbF
  rw [coefL_eq c lam Y hlam]
  ring

theorem compC_eq (lam T Y : ℝ) (hlam : 0 < lam) : compC c lam T Y =
    alpha c lam * coefE lam T Y + gamma c lam * coefL c lam Y * (msg lam T / lmass lam T) ^ 2 /
      ZbF c lam T Y := by
  have hp : msg lam Y ≠ 0 := (msg_pos hlam).ne'
  unfold compC
  rw [coefZ_eq c lam T Y hlam]
  congr 1
  rw [show msg lam Y * gamma c lam * coefL c lam Y * (msg lam T / lmass lam T) ^ 2 =
    msg lam Y * (gamma c lam * coefL c lam Y * (msg lam T / lmass lam T) ^ 2) by ring,
    mul_div_mul_left _ _ hp]

theorem compB_eq (lam T Y : ℝ) (hlam : 0 < lam) : compB c lam T Y =
    alpha c lam * coefE lam T Y + msg lam Y * ((actQ lam * ((c.D : ℝ) - 1) + msg lam Y -
      gamma c lam * (msg lam Y / lmass lam Y)) / Y - hF c lam Y ^ 2 * coefJ lam T / ZbF c lam T Y) := by
  have hp : msg lam Y ≠ 0 := (msg_pos hlam).ne'
  unfold compB
  rw [coefZ_eq c lam T Y hlam, coefH_eq]
  have e1 : (msg lam Y * hF c lam Y) ^ 2 * coefJ lam T / (msg lam Y * ZbF c lam T Y) =
      msg lam Y * (hF c lam Y ^ 2 * coefJ lam T / ZbF c lam T Y) := by
    rw [show (msg lam Y * hF c lam Y) ^ 2 * coefJ lam T =
      msg lam Y * (msg lam Y * (hF c lam Y ^ 2 * coefJ lam T)) by ring, mul_div_mul_left _ _ hp]
    ring
  rw [e1]
  unfold capA hF
  ring

theorem coefE_eq (lam T Y : ℝ) : coefE lam T Y =
    (1 - msg lam Y) + msg lam Y * (T / lmass lam T) - lmass lam Y / Y := by
  unfold coefE; ring

theorem coefJ_eq (lam T : ℝ) : coefJ lam T = msg lam T * (msg lam T / lmass lam T) * T := by
  unfold coefJ; ring

end Forms

end Erdos993Lean.Analytic.Reserve.Cert
