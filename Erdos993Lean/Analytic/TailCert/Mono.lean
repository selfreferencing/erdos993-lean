import Mathlib
import Erdos993Lean.Analytic.Tail

/-!
# Monotonicity facts for the cell checker of the repaired T3 potential (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  Sources: `SOUL/O3/repaired_potential_proof.md`
§"Positive-domain interval checker" (the monotonicity directions), confirmed by
`LEAN/referee/REVIEW_SOUL_ROUND2.md` item 3.  The quantities are those of lane A3's
`Erdos993Lean/Analytic/Tail/` (`actQ`, `rK`, `pC`, `Lf`, `Tf`, `That`, `rFallback`, `hmin`).

* `actQ_mono`, `rK_mono`: `q(λ)` and `r(λ)` increase;
* `rFallback_anti`: `ρ(λ, z) = log((1 + λ)/(1 + λ z))/log(1 + λ)` decreases in `λ` (for
  `0 ≤ z ≤ 1`): with `a = log(1 + λ) ≤ b = log(1 + μ)`, `θ = a/b`, the concavity of `x ↦ x^θ`
  (`Real.concaveOn_rpow`) gives `1 + λ z = (1 − z) + z (e^b)^θ ≤ (1 + μ z)^θ`;
* `pC_le_of_le`: `p_c(λ, s) ≤ W/(1 + W)` for `W ≥ λ e^{−s}`;
* `gain_anti`: `−log(p + (1 − p) E)` decreases in `p` (`E ≤ 1`) and in `E` (`p ≤ 1`);
* `Lf_mono`, `That_mono` (`That_λ(Y)` increases in `λ`, decreases in `Y`), `Tf_mono`
  (`T_λ(x)` increases in `λ`, decreases in `x`);
* `hmin_pC_ge`: `h(λ, p_c(λ, s)) = λ e^{−s}/(1 + λ + λ e^{−s}) ≥ l0 u/(1 + l0 + l0 u)` for `l0 ≤ λ`,
  `0 ≤ u ≤ e^{−s}`; `hmin_pC_nonneg`, `hmin_pC_le_one`;
* `That_Tf_eq`, `That_Tf_ge`: `That(T_λ(x)) = log(λ x/(λ(1 − x) − x))`, increasing in `x`,
  decreasing in `λ`;
* `div_Lf_anti`: `x/L(x)` decreases on `(0, 1)` (concavity of `log`);
* `That_le_Tf`, `Lf_le_of_le`: for `x ≤ 1 − e^{−Y}`, `T_λ(x) ≥ That_λ(Y)` and `L(x) ≤ Y`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.TailCert

open Tail

/-! ## Monotonicity of the activity-dependent quantities -/

theorem actQ_mono {l l' : ℝ} (hl : 0 ≤ l) (hll : l ≤ l') : actQ l ≤ actQ l' := by
  unfold actQ
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem rK_mono {l l' : ℝ} (hll : l ≤ l') : rK l ≤ rK l' := by
  unfold rK
  have h1 : Real.sqrt (1 + 4 * l) ≤ Real.sqrt (1 + 4 * l') := Real.sqrt_le_sqrt (by linarith)
  have h0 : 0 ≤ Real.sqrt (1 + 4 * l) := Real.sqrt_nonneg _
  have : 2 / (1 + Real.sqrt (1 + 4 * l')) ≤ 2 / (1 + Real.sqrt (1 + 4 * l)) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith

/-- **`ρ` decreases with the activity** (the convexity of `s ↦ log(1 − z + z e^s)`, through the
concavity of `x ↦ x^θ`): `rFallback μ z ≤ rFallback λ z` for `0 < λ ≤ μ`, `0 ≤ z ≤ 1`. -/
theorem rFallback_anti {l m z : ℝ} (hl : 0 < l) (hlm : l ≤ m) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    rFallback m z ≤ rFallback l z := by
  have hm : 0 < m := hl.trans_le hlm
  set a := Real.log (1 + l) with ha
  set b := Real.log (1 + m) with hb
  have ha0 : 0 < a := log_one_add_pos hl
  have hb0 : 0 < b := log_one_add_pos hm
  have hab : a ≤ b := Real.log_le_log (by linarith) (by linarith)
  set θ := a / b with hθ
  have hθ0 : 0 ≤ θ := div_nonneg ha0.le hb0.le
  have hθ1 : θ ≤ 1 := (div_le_one hb0).mpr hab
  -- `1 + l z ≤ (1 + m z)^θ`
  have hkey : 1 + l * z ≤ (1 + m * z) ^ θ := by
    have hconc := (Real.concaveOn_rpow hθ0 hθ1).2 (show (1 : ℝ) ∈ Set.Ici 0 by simp)
      (show (1 + m : ℝ) ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith)
      (show (0 : ℝ) ≤ 1 - z by linarith) hz0 (by ring : 1 - z + z = 1)
    simp only [smul_eq_mul, Real.one_rpow, mul_one] at hconc
    have hpow : (1 + m) ^ θ = 1 + l := by
      rw [hθ, show (1 + m) = Real.exp b by rw [hb, Real.exp_log (by linarith)], ← Real.exp_mul,
        show b * (a / b) = a by field_simp, ha, Real.exp_log (by linarith)]
    rw [hpow] at hconc
    calc 1 + l * z = 1 - z + z * (1 + l) := by ring
      _ ≤ (1 - z + z * (1 + m)) ^ θ := hconc
      _ = (1 + m * z) ^ θ := by ring_nf
  have hlog : Real.log (1 + l * z) ≤ θ * Real.log (1 + m * z) := by
    have h1 : 0 < 1 + l * z := by nlinarith
    have := Real.log_le_log h1 hkey
    rwa [Real.log_rpow (by nlinarith)] at this
  -- `rFallback t z = 1 − log(1 + t z)/log(1 + t)`
  have hr : ∀ t : ℝ, 0 < t → rFallback t z = 1 - Real.log (1 + t * z) / Real.log (1 + t) := by
    intro t ht
    unfold rFallback
    have h1 : 0 < 1 + t * z := by nlinarith
    rw [Real.log_div (by linarith) h1.ne']
    have := log_one_add_pos ht
    field_simp
  rw [hr m hm, hr l hl, ← ha, ← hb]
  have : Real.log (1 + l * z) / a ≤ Real.log (1 + m * z) / b := by
    rw [div_le_div_iff₀ ha0 hb0]
    have := mul_le_mul_of_nonneg_left hlog hb0.le
    calc Real.log (1 + l * z) * b ≤ b * (θ * Real.log (1 + m * z)) := by linarith
      _ = Real.log (1 + m * z) * a := by rw [hθ]; field_simp
  linarith

/-- `pC λ s ≤ W/(1 + W)` for `λ e^{−s} ≤ W`. -/
theorem pC_le_of_le {lam s W : ℝ} (hlam : 0 < lam) (hW : lam * Real.exp (-s) ≤ W) :
    pC lam s ≤ W / (1 + W) := by
  have hw0 : 0 < lam * Real.exp (-s) := mul_pos hlam (Real.exp_pos _)
  unfold pC
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `−log(p + (1 − p) E)` decreases in `p` (for `E ≤ 1`) and in `E` (for `p ≤ 1`). -/
theorem gain_anti {p p' E E' : ℝ} (hp0 : 0 ≤ p) (hpp : p ≤ p') (hp1 : p' ≤ 1) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hEE : E ≤ E') :
    -Real.log (p' + (1 - p') * E') ≤ -Real.log (p + (1 - p) * E) := by
  have h1 : 0 < p + (1 - p) * E := by nlinarith
  have h2 : p + (1 - p) * E ≤ p' + (1 - p') * E' := by nlinarith
  have := Real.log_le_log h1 h2
  linarith

theorem Lf_mono {p p' : ℝ} (hpp : p ≤ p') (hp1 : p' < 1) : Lf p ≤ Lf p' := by
  unfold Lf
  have := Real.log_le_log (by linarith) (show 1 - p' ≤ 1 - p by linarith)
  linarith

theorem That_mono {l l' Y Y' : ℝ} (hl : 0 < l) (hll : l ≤ l') (hY' : 0 < Y') (hYY : Y' ≤ Y) :
    That l Y ≤ That l' Y' := by
  have hY : 0 < Y := hY'.trans_le hYY
  have hl' : 0 < l' := hl.trans_le hll
  rw [That_eq hl hY, That_eq hl' hY']
  have h1 : 0 < Real.exp Y' - 1 := by linarith [Real.add_one_lt_exp hY'.ne']
  have h2 : Real.exp Y' ≤ Real.exp Y := Real.exp_le_exp.mpr hYY
  apply Real.log_le_log (div_pos hl (by linarith))
  exact div_le_div₀ hl'.le hll h1 (by linarith)

theorem That_le_ThatPlus (l Y : ℝ) : That l Y ≤ ThatPlus l Y := le_max_left _ _

theorem ThatPlus_nonneg (l Y : ℝ) : 0 ≤ ThatPlus l Y := le_max_right _ _

/-- `h(λ, p_c(λ, s)) = λ e^{−s}/(1 + λ + λ e^{−s}) ≥ l0 u/(1 + l0 + l0 u)` for `l0 ≤ λ`,
`0 ≤ u ≤ e^{−s}`. -/
theorem hmin_pC_ge {l0 lam s u : ℝ} (hl0 : 0 < l0) (hl : l0 ≤ lam) (hu0 : 0 ≤ u)
    (hu : u ≤ Real.exp (-s)) :
    l0 * u / (1 + l0 + l0 * u) ≤ hmin lam (pC lam s) := by
  have hlam : 0 < lam := hl0.trans_le hl
  set e := Real.exp (-s) with he
  have he0 : 0 < e := Real.exp_pos _
  have hform : hmin lam (pC lam s) = lam * e / (1 + lam + lam * e) := by
    have h1 : 0 < 1 + lam * e := by nlinarith [mul_pos hlam he0]
    have h3 : 1 + lam * (1 - pC lam s) = (1 + lam + lam * e) / (1 + lam * e) := by
      rw [one_sub_pC hlam, ← he]
      field_simp
      ring
    unfold hmin
    rw [h3]
    unfold pC
    rw [← he, div_div_div_cancel_right₀ h1.ne']
  have hd1 : 0 < 1 + l0 + l0 * u := by nlinarith [mul_nonneg hl0.le hu0]
  have hd2 : 0 < 1 + lam + lam * e := by nlinarith [mul_pos hlam he0]
  rw [hform, div_le_div_iff₀ hd1 hd2]
  have h1 : l0 * u ≤ lam * e := mul_le_mul hl hu hu0 hlam.le
  nlinarith [mul_nonneg hl0.le hu0, mul_nonneg (sub_nonneg.mpr hl) hu0, mul_pos hlam he0,
    mul_nonneg (sub_nonneg.mpr hl) (mul_nonneg hl0.le hu0), mul_nonneg (sub_nonneg.mpr hu) hl0.le]

theorem hmin_pC_nonneg {lam s : ℝ} (hlam : 0 < lam) : 0 ≤ hmin lam (pC lam s) := by
  have h := pC_pos hlam s
  have h1 := pC_lt_one hlam s
  unfold hmin
  apply div_nonneg h.le
  nlinarith

theorem hmin_pC_le_one {lam s : ℝ} (hlam : 0 < lam) : hmin lam (pC lam s) ≤ 1 := by
  have := one_sub_hmin_nonneg hlam.le (pC_lt_one hlam s).le
  linarith

/-- `T_λ(x) = log(λ(1 − x)/x)` increases in `λ` and decreases in `x`. -/
theorem Tf_mono {l l' x x' : ℝ} (hl : 0 < l) (hll : l ≤ l') (hx' : 0 < x') (hxx : x' ≤ x)
    (hx1 : x < 1) : Tf l x ≤ Tf l' x' := by
  unfold Tf
  have hx : 0 < x := hx'.trans_le hxx
  apply Real.log_le_log (by apply div_pos (mul_pos hl (by linarith)) hx)
  rw [div_le_div_iff₀ hx hx']
  have : l * (1 - x) * x' ≤ l' * (1 - x') * x := by
    have h1 : l * (1 - x) ≤ l' * (1 - x') := mul_le_mul hll (by linarith) (by linarith)
      (by linarith)
    calc l * (1 - x) * x' ≤ l' * (1 - x') * x' := mul_le_mul_of_nonneg_right h1 hx'.le
      _ ≤ l' * (1 - x') * x := mul_le_mul_of_nonneg_left hxx (by nlinarith)
  linarith

/-- The composed `That`: `That(T_λ(x)) = log(λ x/(λ(1 − x) − x))` for `0 < x < q`. -/
theorem That_Tf_eq {lam x : ℝ} (hlam : 0 < lam) (hx0 : 0 < x) (hxq : x < actQ lam) :
    That lam (Tf lam x) = Real.log (lam * x / (lam * (1 - x) - x)) := by
  have hq1 := actQ_lt_one hlam.le
  have hx1 : x < 1 := hxq.trans hq1
  have hden : 0 < lam * (1 - x) - x := by
    unfold actQ at hxq
    rw [lt_div_iff₀ (by linarith)] at hxq
    linarith
  have hT : 0 < Tf lam x := by
    unfold Tf
    apply Real.log_pos
    rw [one_lt_div hx0]
    linarith
  rw [That_eq hlam hT]
  unfold Tf
  rw [Real.exp_log (div_pos (mul_pos hlam (by linarith)) hx0)]
  congr 1
  rw [div_sub_one hx0.ne', div_div_eq_mul_div]

/-- `That(T_λ(x)) ≥ log(l1 x'/(l1(1 − x') − x'))` for `λ ≤ l1`, `x' ≤ x < q(λ)` (it increases in
`x` and decreases in `λ`). -/
theorem That_Tf_ge {l1 lam x x' : ℝ} (hlam : 0 < lam) (hl1 : lam ≤ l1) (hx' : 0 < x')
    (hxx : x' ≤ x) (hxq : x < actQ lam) (hden : 0 < l1 * (1 - x') - x') :
    Real.log (l1 * x' / (l1 * (1 - x') - x')) ≤ That lam (Tf lam x) := by
  have hx0 : 0 < x := hx'.trans_le hxx
  rw [That_Tf_eq hlam hx0 hxq]
  have hq1 := actQ_lt_one hlam.le
  have hdenx : 0 < lam * (1 - x) - x := by
    unfold actQ at hxq
    rw [lt_div_iff₀ (by linarith)] at hxq
    linarith
  have hl1pos : 0 < l1 := hlam.trans_le hl1
  apply Real.log_le_log (div_pos (mul_pos hl1pos hx') hden)
  rw [div_le_div_iff₀ hden hdenx]
  -- `l1 x' (λ(1 − x) − x) ≤ λ x (l1(1 − x') − x')`
  have h1 : l1 * x' * (lam * (1 - x) - x) = lam * l1 * x' - x' * x * (lam * l1 + l1) := by ring
  have h2 : lam * x * (l1 * (1 - x') - x') = lam * l1 * x - x * x' * (lam * l1 + lam) := by ring
  rw [h1, h2]
  have h3 : lam * l1 * x' ≤ lam * l1 * x := by
    apply mul_le_mul_of_nonneg_left hxx; positivity
  have h4 : x * x' * (lam * l1 + lam) ≤ x' * x * (lam * l1 + l1) := by
    have : lam * l1 + lam ≤ lam * l1 + l1 := by linarith
    have hxx0 : 0 ≤ x * x' := by positivity
    calc x * x' * (lam * l1 + lam) ≤ x * x' * (lam * l1 + l1) := mul_le_mul_of_nonneg_left this hxx0
      _ = x' * x * (lam * l1 + l1) := by ring
  linarith

/-- `x / L(x)` decreases on `(0, 1)` (`L` is convex with `L(0) = 0`). -/
theorem div_Lf_anti {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (hx1 : x' < 1) :
    x' / Lf x' ≤ x / Lf x := by
  have hx'0 : 0 < x' := hx.trans_le hxx
  have hL : 0 < Lf x := Tail.Lf_pos hx (hxx.trans_lt hx1)
  have hL' : 0 < Lf x' := Tail.Lf_pos hx'0 hx1
  -- concavity of `log`: `log(1 − x) ≥ (x/x') log(1 − x')`
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 : ℝ) ∈ Set.Ioi 0 by simp)
    (show (1 - x' : ℝ) ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith)
    (show (0 : ℝ) ≤ 1 - x / x' by rw [sub_nonneg, div_le_one hx'0]; exact hxx)
    (show (0 : ℝ) ≤ x / x' from div_nonneg hx.le hx'0.le) (by ring : 1 - x / x' + x / x' = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc
  have harg : 1 - x / x' + x / x' * (1 - x') = 1 - x := by field_simp; ring
  rw [harg] at hconc
  -- `L(x) ≤ (x/x') L(x')`
  have hLx : Lf x ≤ x / x' * Lf x' := by unfold Lf; linarith
  rw [div_le_div_iff₀ hL' hL]
  calc x' * Lf x ≤ x' * (x / x' * Lf x') := mul_le_mul_of_nonneg_left hLx hx'0.le
    _ = x * Lf x' := by field_simp

/-- `T_λ(x) ≥ That_λ(Y)` for `0 < x ≤ 1 − e^{−Y}`. -/
theorem That_le_Tf {lam Y x : ℝ} (hlam : 0 < lam) (hY : 0 < Y) (hx0 : 0 < x)
    (hxY : x ≤ 1 - Real.exp (-Y)) : That lam Y ≤ Tf lam x := by
  rw [That_eq hlam hY]
  unfold Tf
  have he : Real.exp (-Y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he0 : 0 < Real.exp (-Y) := Real.exp_pos _
  have hx1 : x < 1 := by linarith
  have h1 : 0 < Real.exp Y - 1 := by linarith [Real.add_one_lt_exp hY.ne']
  apply Real.log_le_log (div_pos hlam h1)
  rw [div_le_div_iff₀ h1 hx0]
  -- `λ x ≤ λ(1 − x)(e^Y − 1)` from `x ≤ 1 − e^{−Y}`
  have hexp : Real.exp Y * Real.exp (-Y) = 1 := by rw [← Real.exp_add]; simp
  have : x ≤ (1 - x) * (Real.exp Y - 1) := by nlinarith
  nlinarith

/-- `L(x) ≤ Y` for `x ≤ 1 − e^{−Y}`. -/
theorem Lf_le_of_le {Y x : ℝ} (hxY : x ≤ 1 - Real.exp (-Y)) : Lf x ≤ Y := by
  unfold Lf
  have he0 : 0 < Real.exp (-Y) := Real.exp_pos _
  have := Real.log_le_log he0 (show Real.exp (-Y) ≤ 1 - x by linarith)
  rw [Real.log_exp] at this
  linarith

end Erdos993Lean.Analytic.TailCert
