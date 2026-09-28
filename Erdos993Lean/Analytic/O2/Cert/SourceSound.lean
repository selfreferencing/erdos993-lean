import Mathlib
import Erdos993Lean.Analytic.O2.Cert.QuadSound

/-!
# O2 certificate checker (lane A18): the retained source on a piece

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The checker bounds A16's source
`g = max(f_q(pr), (1 + f_q(pr) − f_q(M_up))/2)` (`O2/Defs.lean`, `src`; `PRO_R2_PROOF.md` Lemma 2) from below by
`srcV`: `αxr` in low mode, else `(f(xr) + 1 − f(M))/2` with `f(a) = f_q(qa)` (`fq_q_mul`) and `M = M_up/q`
(`mUp_eq`, `cavH_eq`), so `srcV ≤ src` (**`srcV_le_src`**).  On a piece `[ya, yb]` that the first source cut
`Y_f` (the kink of `Y ↦ f(x(1 − qY))`) does not cross, `srcV` lies above its chord (**`srcV_chord`**): the part
`f(xr)` is affine there (`fnR_affine_piece`) and `−f(M)` is concave (`f` convex nondecreasing, `M` convex).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The retained source on a piece (`PRO_R2_PROOF.md` Lemma 2, (4)–(5)) -/

/-- The retained-source lower bound at a real `Y` (the value of `srcR` of the real context). -/
noncomputable def srcV (low : Bool) (l x Y : ℝ) : ℝ :=
  if low then x * (1 - qR l * Y) * (1 - 1 / ((l + 1) * 2))
  else (fnR l (x * (1 - qR l * Y)) + 1 - fnR l (max Y ((1 - pR l x * (1 - qR l * Y)) * hnR l x))) / 2

theorem srcR_eq (sd : SegData) (fl : Flags) (low : Bool) (FY : RF) (l x : ℝ) :
    srcR (ctxR sd fl) low FY l x = srcV low l x (FY l x) := rfl

theorem qR_eq_actQ (l : ℝ) : qR l = actQ l := by unfold qR actQ; rw [add_comm]

theorem qR_pos {l : ℝ} (hl : 0 < l) : 0 < qR l := by unfold qR; positivity

theorem qR_lt_one {l : ℝ} (hl : 0 < l) : qR l < 1 := by
  unfold qR; rw [div_lt_one (by linarith)]; linarith

theorem kapR_eq {l : ℝ} (hl : 0 < l) : kapR l = (l + 1) / (2 * l + 1) := by
  unfold kapR qR
  have h1 : l + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem fnR_alpha_pos {l : ℝ} (hl : 0 < l) : 0 < 1 - 1 / ((l + 1) * 2) := by
  have : 1 / ((l + 1) * 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
  linarith

theorem fnR_mono {l : ℝ} (hl : 0 < l) {a b : ℝ} (h : a ≤ b) : fnR l a ≤ fnR l b := by
  unfold fnR
  have hα := fnR_alpha_pos hl
  have hβ : 0 < 1 / (l * 2) := by positivity
  apply max_le_max
  · exact mul_le_mul_of_nonneg_left h hα.le
  · nlinarith

theorem le_fnR (l a : ℝ) : (1 - 1 / ((l + 1) * 2)) * a ≤ fnR l a := by unfold fnR; exact le_max_left _ _

theorem lin2_le_lin2 {a b a' b' η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (ha : a ≤ a') (hb : b ≤ b') :
    lin2 a b η ≤ lin2 a' b' η := by
  unfold lin2
  exact add_le_add (mul_le_mul_of_nonneg_right ha (by linarith)) (mul_le_mul_of_nonneg_right hb h0)

theorem max_lin2_le (a1 b1 a2 b2 η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    max (lin2 a1 b1 η) (lin2 a2 b2 η) ≤ lin2 (max a1 a2) (max b1 b2) η :=
  max_le (lin2_le_lin2 h0 h1 (le_max_left _ _) (le_max_left _ _))
    (lin2_le_lin2 h0 h1 (le_max_right _ _) (le_max_right _ _))

theorem fnR_convex (l a b η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    fnR l (lin2 a b η) ≤ lin2 (fnR l a) (fnR l b) η := by
  have e1 : (1 - 1 / ((l + 1) * 2)) * lin2 a b η =
      lin2 ((1 - 1 / ((l + 1) * 2)) * a) ((1 - 1 / ((l + 1) * 2)) * b) η := by unfold lin2; ring
  have e2 : lin2 a b η - 1 / (l * 2) * (1 - lin2 a b η) =
      lin2 (a - 1 / (l * 2) * (1 - a)) (b - 1 / (l * 2) * (1 - b)) η := by unfold lin2; ring
  unfold fnR
  rw [e1, e2]
  exact max_lin2_le _ _ _ _ η h0 h1

theorem fnR_eq_hi {l a : ℝ} (hl : 0 < l) (ha : kapR l ≤ a) : fnR l a = a - 1 / (l * 2) * (1 - a) := by
  unfold fnR
  rw [max_eq_right]
  rw [kapR_eq hl, div_le_iff₀ (by linarith)] at ha
  have e : a - 1 / (l * 2) * (1 - a) - (1 - 1 / ((l + 1) * 2)) * a = (a * (2 * l + 1) - (l + 1)) / (2 * l * (l + 1)) := by
    field_simp
    ring
  have : 0 ≤ (a * (2 * l + 1) - (l + 1)) / (2 * l * (l + 1)) := div_nonneg (by linarith) (by positivity)
  linarith

theorem fnR_eq_lo {l a : ℝ} (hl : 0 < l) (ha : a ≤ kapR l) : fnR l a = (1 - 1 / ((l + 1) * 2)) * a := by
  unfold fnR
  rw [max_eq_left]
  rw [kapR_eq hl, le_div_iff₀ (by linarith)] at ha
  have e : a - 1 / (l * 2) * (1 - a) - (1 - 1 / ((l + 1) * 2)) * a = (a * (2 * l + 1) - (l + 1)) / (2 * l * (l + 1)) := by
    field_simp
    ring
  have : (a * (2 * l + 1) - (l + 1)) / (2 * l * (l + 1)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- On a piece without the kink `Y_f` of `f(xr)` strictly inside, `Y ↦ f(x(1 − qY))` is affine. -/
theorem fnR_affine_piece {l x ya yb η : ℝ} (hl : 0 < l) (hx : 0 < x) (hya : 0 ≤ ya) (hab : ya ≤ yb)
    (h0 : 0 ≤ η) (h1 : η ≤ 1) (hcut : ¬ (ya < nnR l x / pR l x ∧ nnR l x / pR l x < yb)) :
    fnR l (x * (1 - qR l * lin2 ya yb η)) =
      lin2 (fnR l (x * (1 - qR l * ya))) (fnR l (x * (1 - qR l * yb))) η := by
  have hq := qR_pos hl
  have hlin1 : ya ≤ lin2 ya yb η := by unfold lin2; nlinarith
  have hlin2 : lin2 ya yb η ≤ yb := by unfold lin2; nlinarith
  -- all three points on one branch
  have hbr : (∀ Y, ya ≤ Y → Y ≤ yb → x * (1 - qR l * Y) ≤ kapR l) ∨
      (∀ Y, ya ≤ Y → Y ≤ yb → kapR l ≤ x * (1 - qR l * Y)) := by
    by_cases hxk : x ≤ kapR l
    · left
      intro Y hY _
      have : 0 ≤ x * (qR l * Y) := mul_nonneg hx.le (mul_nonneg hq.le (hya.trans hY))
      nlinarith
    · push_neg at hxk
      have hnn : nnR l x = x - kapR l := by unfold nnR; rw [max_eq_right (by linarith)]
      have hp : pR l x = qR l * x := rfl
      have hzf : x * qR l * (nnR l x / pR l x) = x - kapR l := by
        rw [hnn, hp]; field_simp
      rcases not_and_or.mp hcut with h | h
      · left
        intro Y hY _
        have hY' : nnR l x / pR l x ≤ Y := (not_lt.mp h).trans hY
        have : x * qR l * (nnR l x / pR l x) ≤ x * qR l * Y := mul_le_mul_of_nonneg_left hY' (by positivity)
        nlinarith
      · right
        intro Y _ hY
        have hY' : Y ≤ nnR l x / pR l x := hY.trans (not_lt.mp h)
        have : x * qR l * Y ≤ x * qR l * (nnR l x / pR l x) := mul_le_mul_of_nonneg_left hY' (by positivity)
        nlinarith
  rcases hbr with h | h
  · rw [fnR_eq_lo hl (h _ hlin1 hlin2), fnR_eq_lo hl (h _ le_rfl hab), fnR_eq_lo hl (h _ hab le_rfl)]
    unfold lin2; ring
  · rw [fnR_eq_hi hl (h _ hlin1 hlin2), fnR_eq_hi hl (h _ le_rfl hab), fnR_eq_hi hl (h _ hab le_rfl)]
    unfold lin2; ring

/-- **The chord property of the retained source**: on a piece with no kink of `f(xr)` strictly inside, the
source lower bound lies above its chord (it is affine plus concave there). -/
theorem srcV_chord (low : Bool) {l x ya yb η : ℝ} (hl : 0 < l) (hx : 0 < x) (hya : 0 ≤ ya) (hab : ya ≤ yb)
    (h0 : 0 ≤ η) (h1 : η ≤ 1) (hcut : low = false → ¬ (ya < nnR l x / pR l x ∧ nnR l x / pR l x < yb)) :
    lin2 (srcV low l x ya) (srcV low l x yb) η ≤ srcV low l x (lin2 ya yb η) := by
  cases low
  · simp only [srcV, Bool.false_eq_true, if_false]
    have hA := fnR_affine_piece hl hx hya hab h0 h1 (hcut rfl)
    -- the convex part
    set M : ℝ → ℝ := fun Y => max Y ((1 - pR l x * (1 - qR l * Y)) * hnR l x) with hM
    have hMc : M (lin2 ya yb η) ≤ lin2 (M ya) (M yb) η := by
      have e : (1 - pR l x * (1 - qR l * lin2 ya yb η)) * hnR l x =
          lin2 ((1 - pR l x * (1 - qR l * ya)) * hnR l x) ((1 - pR l x * (1 - qR l * yb)) * hnR l x) η := by
        unfold lin2; ring
      simp only [hM]
      rw [e]
      exact max_lin2_le _ _ _ _ η h0 h1
    have hfM : fnR l (M (lin2 ya yb η)) ≤ lin2 (fnR l (M ya)) (fnR l (M yb)) η :=
      (fnR_mono hl hMc).trans (fnR_convex l _ _ η h0 h1)
    simp only [hM] at hfM
    rw [hA]
    unfold lin2 at hfM ⊢
    linarith
  · simp only [srcV, if_true]
    apply le_of_eq
    unfold lin2; ring

theorem fq_q_mul {l : ℝ} (hl : 0 < l) (a : ℝ) : fq (actQ l) (actQ l * a) = fnR l a := by
  unfold fq fnR actQ
  have h1 : (1 : ℝ) + l ≠ 0 := by positivity
  have h2 : l + 1 ≠ 0 := by positivity
  have h3 : l ≠ 0 := hl.ne'
  congr 1
  · field_simp; ring
  · field_simp; ring

theorem cavH_eq {l x : ℝ} (hl : 0 < l) (hx : 0 < x) (hx1 : x ≤ 1) :
    cavH l (pR l x) = actQ l * hnR l x := by
  have hq := qR_pos hl
  have hq1 := qR_lt_one hl
  have hle : 0 < le1R l x := by unfold le1R; nlinarith
  have hp1 : pR l x < 1 := by unfold pR; nlinarith
  have hq' : 0 ≤ actQ l := by rw [← qR_eq_actQ]; exact hq.le
  unfold cavH hnR
  rw [mul_min_of_nonneg _ _ hq', mul_one]
  congr 1
  unfold pR le1R qR at *
  unfold actQ
  have h1 : (1 : ℝ) + l ≠ 0 := by positivity
  have h2 : l + 1 ≠ 0 := by positivity
  have h4 : 1 - l / (l + 1) * x ≠ 0 := by linarith
  have h5 : l * (1 - x) + 1 ≠ 0 := by linarith
  have h6 : 1 - x * l + l ≠ 0 := by linarith
  have h7 : l + 1 - l * x ≠ 0 := by linarith
  field_simp
  ring

theorem mUp_eq {l x Y : ℝ} (hl : 0 < l) (hx : 0 < x) (hx1 : x ≤ 1) :
    mUp l (pR l x) (1 - qR l * Y) = actQ l * max Y ((1 - pR l x * (1 - qR l * Y)) * hnR l x) := by
  have hq' : 0 ≤ actQ l := by rw [← qR_eq_actQ]; exact (qR_pos hl).le
  unfold mUp
  rw [cavH_eq hl hx hx1, mul_max_of_nonneg _ _ hq', qR_eq_actQ]
  congr 1
  · ring
  · ring

/-- The retained-source lower bound is at most A16's source `g` (`src`). -/
theorem srcV_le_src (low : Bool) {l x Y : ℝ} (hl : 0 < l) (hx : 0 < x) (hx1 : x ≤ 1) :
    srcV low l x Y ≤ src l (pR l x) (1 - qR l * Y) := by
  have hpr : pR l x * (1 - qR l * Y) = actQ l * (x * (1 - qR l * Y)) := by
    unfold pR; rw [qR_eq_actQ]; ring
  unfold src
  rw [hpr, fq_q_mul hl, mUp_eq hl hx hx1, fq_q_mul hl]
  cases low
  · simp only [srcV, Bool.false_eq_true, if_false]
    apply le_max_of_le_right
    apply le_of_eq
    ring
  · simp only [srcV, if_true]
    apply le_max_of_le_left
    have := le_fnR l (x * (1 - qR l * Y))
    linarith

end Erdos993Lean.Analytic.O2.Cert
