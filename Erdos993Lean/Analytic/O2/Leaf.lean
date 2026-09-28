import Erdos993Lean.Analytic.O2.Defs

/-!
# O2: the payment at the physical leaf endpoint

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A16; for lane A18).  Source: `PRO_R2_PROOF.md`
§8 ("At the physical endpoint `x = 1`, only `z = 1` is admitted.  Its payment is exactly `D₁`, in
which the three own Cauchy terms vanish").

At `p = q` (an empty child list): `T = log(λ(1−q)/q) = 0`, the packed slack `φ = 0`,
`G = log(1 + λ)`, `h(q) = q/log(1 + λ)`, and with `z = 1`

  `Φ(λ, q, r, t, 1) = c r g(q, r) − r(1 − q) − v(t) h(q) − (1 − r)(1 − q) s(t) + (1 − r) τ(t)
                      − ℓ log(1 + λ)/q`   (**`BandData.phi_leaf_eq`**),

which is the engines' `D₁` at `x = 1` (`N_v = r(1−p) + h v(t) + (1−r)(1−p) s(t)`, `w r φ = 0`).
-/

namespace Erdos993Lean.Analytic.O2

theorem logMass_actQ {lam : ℝ} (hl : 0 < lam) : logMass lam (actQ lam) = 0 := by
  unfold logMass actQ
  have h1 : (1 : ℝ) + lam ≠ 0 := by positivity
  have h : lam * (1 - lam / (1 + lam)) / (lam / (1 + lam)) = 1 := by
    field_simp
    ring
  rw [h, Real.log_one]

theorem packPhi_actQ {lam : ℝ} (hl : 0 < lam) : packPhi lam (actQ lam) = 0 := by
  unfold packPhi packRes packJ
  rw [logMass_actQ hl]
  simp

theorem logG_actQ {lam : ℝ} (hl : 0 < lam) : logG lam (actQ lam) = Real.log (1 + lam) := by
  have h1 : (1 : ℝ) + lam ≠ 0 := by positivity
  unfold logG actQ
  congr 1
  field_simp
  ring

theorem hFun_actQ {lam : ℝ} (hl : 0 < lam) :
    hFun (actQ lam) = actQ lam / Real.log (1 + lam) := by
  unfold hFun
  congr 1
  have h1 : (1 : ℝ) + lam ≠ 0 := by positivity
  have h : 1 - actQ lam = (1 + lam)⁻¹ := by
    unfold actQ
    field_simp
    ring
  rw [h, Real.log_inv, neg_neg]

/-- **The leaf payment** (`p = q`, `z = 1`) is the engines' `D₁` at `x = 1`. -/
theorem BandData.phi_leaf_eq (b : BandData) {lam : ℝ} (hl : 0 < lam) (r t : ℝ) :
    b.Phi lam (actQ lam) r t 1 =
      b.price lam * r * src lam (actQ lam) r - r * (1 - actQ lam) -
        b.vF lam t * (actQ lam / Real.log (1 + lam)) -
        (1 - r) * (1 - actQ lam) * b.sF lam t + (1 - r) * b.tauF lam t -
        b.ellF lam * Real.log (1 + lam) / actQ lam := by
  unfold BandData.Phi BandData.Ru BandData.Rv BandData.Rs BandData.Rtau Rw
  rw [packPhi_actQ hl, logG_actQ hl, hFun_actQ hl]
  have e1 : max ((1 : ℝ) - 1) 0 = 0 := by norm_num
  have e2 : max (-(1 : ℝ)) 0 = 0 := by norm_num
  have e3 : max (1 : ℝ) 0 = 1 := by norm_num
  rw [e1, e2, e3]
  ring

end Erdos993Lean.Analytic.O2
