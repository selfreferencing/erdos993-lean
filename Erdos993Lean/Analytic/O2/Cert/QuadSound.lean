import Mathlib
import Erdos993Lean.Analytic.O2.Cert.BernSound

/-!
# O2 certificate checker (lane A18): the payment as three response quadratics

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The local payment in the engines' variables (`payE`,
eq. (11) of `PRO_R2_PROOF.md`) is, on each of the three response ranges `z ≤ 0`, `0 ≤ z ≤ 1`, `z ≥ 1`, the quadratic
`A η² + B η + E` of `η = −z`, `1 − z`, `z − 1` (**`payE_quad`**; `(13)`), nondecreasing in the source when
`c r ≥ 0` (`payE_mono_g`).  On a piece, the Bernstein combinations of the real controls (`triplesR`) are exactly
these coefficients at the interpolated parent data (**`bernA`**, **`bernB`**, **`bernE`**).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

/-! ## The payment as three response quadratics (`PRO_R2_PROOF.md` (13)) -/

/-- The payment in the engines' variables: price `C`, `r`, source `g`, `p`, response `z`, own coefficients
`Au = u(p)/(pT)`, `Av = v(p)/(pT)`, `so = s(p)/H`, the parent fields `ut, vt, st, tt` at `t`, `tp = τ(p)`, `w`, `φ`, `ℓ`,
`G`, `h`. -/
noncomputable def payE (C r g p z Au Av so ut vt st tp tt w phi ell G h : ℝ) : ℝ :=
  C * r * g - r * (1 - p) * z ^ 2 + (Au * (max (z - 1) 0) ^ 2 - ut * h * (max (-z) 0) ^ 2) +
    (Av * (max (1 - z) 0) ^ 2 - vt * h * (max z 0) ^ 2) +
    (r * so * (1 - z) ^ 2 - (1 - r) * st * (1 - p) * z ^ 2) + (r * tp * (z - 1) + (1 - r) * tt * z) +
    w * (z - 1 + r * phi) - ell * G / p

/-- The three quadratics' coefficients (`part` 0: `z ≤ 0`, `η = −z`; 1: `0 ≤ z ≤ 1`, `η = 1 − z`; 2: `z ≥ 1`,
`η = z − 1`). -/
noncomputable def quadA (part : ℕ) (r p Au Av so ut vt st h : ℝ) : ℝ :=
  let ss := r * so
  let nu := r * (1 - p) + ut * h + (1 - r) * st * (1 - p)
  let nv := r * (1 - p) + vt * h + (1 - r) * st * (1 - p)
  if part = 0 then ss + Av - nu else if part = 1 then ss + Av - nv else ss + Au - nv

noncomputable def quadB (part : ℕ) (r p Av so vt st tp tt w h : ℝ) : ℝ :=
  let ss := r * so
  let nv := r * (1 - p) + vt * h + (1 - r) * st * (1 - p)
  let beta := r * tp + (1 - r) * tt + w
  if part = 0 then 2 * (ss + Av) - beta else if part = 1 then 2 * nv - beta else beta - 2 * nv

noncomputable def quadE (part : ℕ) (C r g p Av so vt st tp tt w phi ell G h : ℝ) : ℝ :=
  let ss := r * so
  let nv := r * (1 - p) + vt * h + (1 - r) * st * (1 - p)
  if part = 0 then C * r * g - r * tp - w + r * phi * w - ell * G / p + Av + ss
  else C * r * g - nv + (1 - r) * tt + r * phi * w - ell * G / p

/-- The response variable of each part. -/
noncomputable def etaOf (part : ℕ) (z : ℝ) : ℝ := if part = 0 then -z else if part = 1 then 1 - z else z - 1

theorem payE_quad (C r g p z Au Av so ut vt st tp tt w phi ell G h : ℝ) (part : ℕ)
    (hz : (part = 0 ∧ z ≤ 0) ∨ (part = 1 ∧ 0 ≤ z ∧ z ≤ 1) ∨ (part = 2 ∧ 1 ≤ z)) :
    payE C r g p z Au Av so ut vt st tp tt w phi ell G h =
      quadA part r p Au Av so ut vt st h * etaOf part z ^ 2 + quadB part r p Av so vt st tp tt w h * etaOf part z +
        quadE part C r g p Av so vt st tp tt w phi ell G h := by
  unfold payE quadA quadB quadE etaOf
  rcases hz with ⟨rfl, hz⟩ | ⟨rfl, hz0, hz1⟩ | ⟨rfl, hz⟩
  · simp only [if_true]
    rw [max_eq_right (by linarith : z - 1 ≤ 0), max_eq_left (by linarith : 0 ≤ -z),
      max_eq_left (by linarith : 0 ≤ 1 - z), max_eq_right hz]
    ring
  · simp only [one_ne_zero, if_false, if_true]
    rw [max_eq_right (by linarith : z - 1 ≤ 0), max_eq_right (by linarith : -z ≤ 0),
      max_eq_left (by linarith : 0 ≤ 1 - z), max_eq_left hz0]
    ring
  · simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false]
    rw [max_eq_left (by linarith : 0 ≤ z - 1), max_eq_right (by linarith : -z ≤ 0),
      max_eq_right (by linarith : 1 - z ≤ 0), max_eq_left (by linarith : 0 ≤ z)]
    ring

/-- The payment is nondecreasing in the source when `C r ≥ 0`. -/
theorem payE_mono_g {C r g g' p z Au Av so ut vt st tp tt w phi ell G h : ℝ} (hCr : 0 ≤ C * r) (hg : g' ≤ g) :
    payE C r g' p z Au Av so ut vt st tp tt w phi ell G h ≤ payE C r g p z Au Av so ut vt st tp tt w phi ell G h := by
  unfold payE
  have : C * r * g' ≤ C * r * g := mul_le_mul_of_nonneg_left hg hCr
  linarith

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The degree-2 Bernstein combination. -/
noncomputable def bev3 (a b c η : ℝ) : ℝ := a * (1 - η) ^ 2 + 2 * b * η * (1 - η) + c * η ^ 2

/-- The affine interpolation of two values. -/
noncomputable def lin2 (a b η : ℝ) : ℝ := a * (1 - η) + b * η

/-- The parent field of a label at `η` (degree 0 for knot and `P` labels, degree 1 for `t/q = Y`). -/
noncomputable def parAt (cr : CR) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (f : ℕ → RF) (l x η : ℝ) : ℝ :=
  if lab.1 = 1 then f lab.2 l x
  else if lab.1 = 2 then segR f (clampR cr.upper lab.2) lab.2 l x
  else lin2 (segR f (clampR ya s) s l x) (segR f (clampR yb s) s l x) η

/-- The controls of a piece, evaluated at a point. -/
noncomputable def ctrlAt (cr : CR) (low : Bool) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (part j : ℕ) (l x : ℝ) : ℝ × ℝ × ℝ :=
  let t := ((triplesR cr low lab s ya yb).getD part []).getD j ⟨0, 0, 0⟩
  (t.A l x, t.B l x, t.E l x)

theorem kind_cases (lab : ℕ × ℕ) : lab.1 = 1 ∨ lab.1 = 2 ∨ (lab.1 ≠ 1 ∧ lab.1 ≠ 2) := by omega

set_option maxHeartbeats 4000000 in
theorem bernA (cr : CR) (low : Bool) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (l x η : ℝ) (part : ℕ) (hp : part < 3) :
    bev3 (ctrlAt cr low lab s ya yb part 0 l x).1 (ctrlAt cr low lab s ya yb part 1 l x).1
      (ctrlAt cr low lab s ya yb part 2 l x).1 η =
    quadA part (lin2 (1 - cr.q l x * ya l x) (1 - cr.q l x * yb l x) η) (cr.p l x) (cr.au l x) (cr.av l x) (cr.so l x)
      (parAt cr lab s ya yb cr.u l x η) (parAt cr lab s ya yb cr.v l x η) (parAt cr lab s ya yb cr.s l x η)
      (cr.hp l x) := by
  rcases kind_cases lab with hk | hk | ⟨hk1, hk2⟩ <;> interval_cases part
  all_goals first
    | simp [ctrlAt, triplesR, parR, parAt, hk, rcontrols, radd, rsub, rneg, rmul, relev, bev3, lin2, quadA, rhalf_eq]
    | simp [ctrlAt, triplesR, parR, parAt, hk1, hk2, rcontrols, radd, rsub, rneg, rmul, relev, bev3, lin2, quadA,
        rhalf_eq]
  all_goals ring

set_option maxHeartbeats 4000000 in
theorem bernB (cr : CR) (low : Bool) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (l x η : ℝ) (part : ℕ) (hp : part < 3) :
    bev3 (ctrlAt cr low lab s ya yb part 0 l x).2.1 (ctrlAt cr low lab s ya yb part 1 l x).2.1
      (ctrlAt cr low lab s ya yb part 2 l x).2.1 η =
    quadB part (lin2 (1 - cr.q l x * ya l x) (1 - cr.q l x * yb l x) η) (cr.p l x) (cr.av l x) (cr.so l x)
      (parAt cr lab s ya yb cr.v l x η) (parAt cr lab s ya yb cr.s l x η) (cr.tau l x)
      (parAt cr lab s ya yb cr.t l x η) (cr.w l x) (cr.hp l x) := by
  rcases kind_cases lab with hk | hk | ⟨hk1, hk2⟩ <;> interval_cases part
  all_goals first
    | simp [ctrlAt, triplesR, parR, parAt, hk, rcontrols, radd, rsub, rneg, rmul, relev, bev3, lin2, quadB, rhalf_eq]
    | simp [ctrlAt, triplesR, parR, parAt, hk1, hk2, rcontrols, radd, rsub, rneg, rmul, relev, bev3, lin2, quadB,
        rhalf_eq]
  all_goals ring

set_option maxHeartbeats 4000000 in
theorem bernE (cr : CR) (low : Bool) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (l x η : ℝ) (part : ℕ) (hp : part < 3) :
    bev3 (ctrlAt cr low lab s ya yb part 0 l x).2.2 (ctrlAt cr low lab s ya yb part 1 l x).2.2
      (ctrlAt cr low lab s ya yb part 2 l x).2.2 η =
    quadE part (cr.C l x) (lin2 (1 - cr.q l x * ya l x) (1 - cr.q l x * yb l x) η)
      (lin2 (srcR cr low ya l x) (srcR cr low yb l x) η) (cr.p l x) (cr.av l x) (cr.so l x)
      (parAt cr lab s ya yb cr.v l x η) (parAt cr lab s ya yb cr.s l x η) (cr.tau l x)
      (parAt cr lab s ya yb cr.t l x η) (cr.w l x) (cr.phi l x) (cr.ell l x) (cr.G l x) (cr.hp l x) := by
  rcases kind_cases lab with hk | hk | ⟨hk1, hk2⟩ <;> interval_cases part
  all_goals first
    | simp [ctrlAt, triplesR, parR, parAt, hk, rcontrols, radd, rsub, rneg, rmul, relev, bev3, lin2, quadE, rhalf_eq]
    | simp [ctrlAt, triplesR, parR, parAt, hk1, hk2, rcontrols, radd, rsub, rneg, rmul, relev, bev3, lin2, quadE,
        rhalf_eq]
  all_goals ring

end Erdos993Lean.Analytic.O2.Cert
