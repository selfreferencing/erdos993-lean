import Mathlib
import Erdos993Lean.Analytic.O2.Cert.BernSound

/-!
# O2 certificate checker (lane A18): the centered lower bound and the quadratic tests

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The derived quantities of a control (`derive`: `A`,
`B`, `E`, `A+B+E`, `2A+B`, `E+B/2`, `4AE−B²`, and `E − B²/(4A)` with slopes by the envelope rule `sl_minimum`)
enclose their real counterparts (`de_derive`); the centered (mean-value) lower bound `lowerB` over a box, with the
anchor re-evaluated at a corner or the midpoint of each coordinate, is a lower bound at every point of the box
(**`lowerB_sound`**, via `coord_step`); and a passing quadratic test (`quad`, `PRO_R2_PROOF.md` §6) makes the control
a nonnegative quadratic on its response range (**`quad_sound`**: the half-line and unit-interval tests
`quad_half`, `quad_unit`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The derived quantities of a control -/

/-- The real derived quantity `k` of a real control (mirror of `derive`). -/
noncomputable def dR (t : TriR) (k : ℕ) : RF := fun l x =>
  match k with
  | 0 => t.A l x
  | 1 => t.B l x
  | 2 => t.E l x
  | 3 => t.A l x + t.B l x + t.E l x
  | 4 => t.A l x * 2 + t.B l x
  | 5 => t.E l x + t.B l x / 2
  | 6 => t.A l x * 4 * t.E l x - t.B l x ^ 2
  | _ => t.E l x - t.B l x ^ 2 / (4 * t.A l x)

/-- The envelope rule for the slopes of `m = E − B²/(4A)` (`A > 0`). -/
theorem sl_minimum {IA IB IE VB V2 L : Ival} {fA fB fE : ℝ → ℝ} (hA : Sl IA L fA) (hB : Sl IB L fB)
    (hE : Sl IE L fE) (hpos : ∀ t, L.Mem t → 0 < fA t)
    (heta : ∀ t, L.Mem t → VB.Mem (-fB t / (2 * fA t))) (heta2 : ∀ t, L.Mem t → V2.Mem ((-fB t / (2 * fA t)) ^ 2)) :
    Sl (add (add IE (mul VB IB)) (mul V2 IA)) L (fun t => fE t - fB t ^ 2 / (4 * fA t)) := by
  intro a b ha hb hab
  obtain ⟨sA, hsA, eA⟩ := hA a b ha hb hab
  obtain ⟨sB, hsB, eB⟩ := hB a b ha hb hab
  obtain ⟨sE, hsE, eE⟩ := hE a b ha hb hab
  have hAa := hpos a ha
  have hAb := hpos b hb
  set ηa := -fB a / (2 * fA a)
  set ηb := -fB b / (2 * fA b)
  -- m_t = Q_t(η_t) ≤ Q_t(η) for all η
  have hQ : ∀ t, 0 < fA t → ∀ η : ℝ, fE t - fB t ^ 2 / (4 * fA t) ≤ fA t * η ^ 2 + fB t * η + fE t := by
    intro t ht η
    have : fA t * η ^ 2 + fB t * η + fE t - (fE t - fB t ^ 2 / (4 * fA t)) = fA t * (η + fB t / (2 * fA t)) ^ 2 := by
      field_simp; ring
    nlinarith [this, sq_nonneg (η + fB t / (2 * fA t))]
  have hQe : ∀ t, 0 < fA t → fA t * (-fB t / (2 * fA t)) ^ 2 + fB t * (-fB t / (2 * fA t)) + fE t =
      fE t - fB t ^ 2 / (4 * fA t) := by
    intro t ht; field_simp; ring
  set F : ℝ → ℝ := fun η => sE + η * sB + η ^ 2 * sA
  have hmem : ∀ η, VB.Mem η → V2.Mem (η ^ 2) → (add (add IE (mul VB IB)) (mul V2 IA)).Mem (F η) :=
    fun η h1 h2 => mem_add (mem_add hsE (mem_mul h1 hsB)) (mem_mul h2 hsA)
  -- the difference lies between F(ηa)Δ and F(ηb)Δ
  have hup : (fE b - fB b ^ 2 / (4 * fA b)) - (fE a - fB a ^ 2 / (4 * fA a)) ≤ F ηa * (b - a) := by
    have h1 := hQ b hAb ηa
    have h2 := hQe a hAa
    have : F ηa * (b - a) = (fA b * ηa ^ 2 + fB b * ηa + fE b) - (fA a * ηa ^ 2 + fB a * ηa + fE a) := by
      simp only [F]; linear_combination (-ηa ^ 2) * eA - ηa * eB - eE
    rw [this]; linarith
  have hlo : F ηb * (b - a) ≤ (fE b - fB b ^ 2 / (4 * fA b)) - (fE a - fB a ^ 2 / (4 * fA a)) := by
    have h1 := hQ a hAa ηb
    have h2 := hQe b hAb
    have : F ηb * (b - a) = (fA b * ηb ^ 2 + fB b * ηb + fE b) - (fA a * ηb ^ 2 + fB a * ηb + fE a) := by
      simp only [F]; linear_combination (-ηb ^ 2) * eA - ηb * eB - eE
    rw [this]; linarith
  have hΔ : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set D := (fE b - fB b ^ 2 / (4 * fA b)) - (fE a - fB a ^ 2 / (4 * fA a))
  obtain ⟨g1, g2⟩ := slope_between hΔ (d1 := F ηa * (b - a)) (d2 := F ηb * (b - a)) rfl rfl
    (by rw [min_le_iff]; right; exact hlo) (by rw [le_max_iff]; left; exact hup)
  refine ⟨D / (b - a), Compute.Ival.Mem.between (hmem ηa (heta a ha) (heta2 a ha)) (hmem ηb (heta b hb) (heta2 b hb))
    g1 g2, by field_simp⟩

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

section Derive

variable {L X : Ival}

/-- `(c · A).lo = c · A.lo` for an integer point `c > 0` and `A.lo ≤ A.hi`. -/
theorem mul_pt_lo {A : Ival} {c : ℤ} (hc : 0 < c) (hA : A.lo ≤ A.hi) : (mul (pt (c * one)) A).lo = c * A.lo := by
  unfold mul pt fdivP
  simp only
  have h1 : c * one * A.lo ≤ c * one * A.hi := mul_le_mul_of_nonneg_left hA (by rw [one_eq]; positivity)
  simp only [min_eq_left h1, min_self]
  rw [Int.shiftRight_eq_div_pow, one_eq]
  unfold prec
  push_cast
  rw [show c * 18446744073709551616 * A.lo = c * A.lo * 18446744073709551616 by ring]
  exact Int.mul_ediv_cancel (c * A.lo) (by norm_num)

/-- The derived quantity dual numbers enclose the real derived quantities. -/
theorem de_derive (hL : L.lo ≤ L.hi) (hX : X.lo ≤ X.hi) {t : TriR} {d : Tri} (h : TE L X t d) (k : ℕ) :
    DE L X (dR t k) (derive d k) := by
  obtain ⟨hA, hB, hE⟩ := h
  match k with
  | 0 => exact hA
  | 1 => exact hB
  | 2 => exact hE
  | 3 => exact de_add (de_add hA hB) hE
  | 4 => exact de_add (de_mulI hA mem_twoI) hB
  | 5 => exact de_add hE (de_divI hB mem_twoI)
  | 6 => exact de_sub (de_mul (de_mulI hA mem_fourI) hE) (de_sq hB)
  | k + 7 =>
    intro hok
    simp only [derive, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hokA, hokB⟩, hokE⟩, hpos⟩ := hok
    have hA' := hA hokA; have hB' := hB hokB; have hE' := hE hokE
    have hl0 : L.Mem (toR L.lo) := ⟨le_rfl, toR_le_toR.mpr hL⟩
    have hx0 : X.Mem (toR X.lo) := ⟨le_rfl, toR_le_toR.mpr hX⟩
    have hne : d.A.v.lo ≤ d.A.v.hi := (hA'.val _ _ hl0 hx0).lo_le_hi
    have h4 : 0 < (mul fourI d.A.v).lo := by
      unfold fourI; rw [mul_pt_lo (by norm_num) hne]; omega
    have h2 : 0 < (mul twoI d.A.v).lo := by
      unfold twoI; rw [mul_pt_lo (by norm_num) hne]; omega
    have hApos : ∀ l x, L.Mem l → X.Mem x → 0 < t.A l x :=
      fun l x hl hx => (toR_pos.mpr hpos).trans_le (hA'.val l x hl hx).1
    have heta : ∀ l x, L.Mem l → X.Mem x → (div (neg d.B.v) (mul twoI d.A.v)).Mem (-t.B l x / (2 * t.A l x)) :=
      fun l x hl hx => mem_div (mem_neg (hB'.val l x hl hx)) (mem_mul mem_twoI (hA'.val l x hl hx)) h2
    refine ⟨fun l x hl hx => ?_, fun x hx => ?_, fun l hl => ?_⟩
    · exact mem_sub (hE'.val l x hl hx) (mem_div (mem_sqI (hB'.val l x hl hx)) (mem_mul mem_fourI (hA'.val l x hl hx)) h4)
    · exact sl_minimum (hA'.sl0 x hx) (hB'.sl0 x hx) (hE'.sl0 x hx) (fun l hl => hApos l x hl hx)
        (fun l hl => heta l x hl hx) (fun l hl => mem_sqI (heta l x hl hx))
    · exact sl_minimum (hA'.sl1 l hl) (hB'.sl1 l hl) (hE'.sl1 l hl) (fun x hx => hApos l x hl hx)
        (fun x hx => heta l x hl hx) (fun x hx => mem_sqI (heta l x hl hx))

end Derive

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The possibly negated derived quantity. -/
noncomputable def dRn (t : TriR) (k : ℕ) (neg : Bool) : RF := fun l x => if neg then -dR t k l x else dR t k l x

theorem de_dRn {L X : Ival} (hL : L.lo ≤ L.hi) (hX : X.lo ≤ X.hi) {t : TriR} {d : Tri} (h : TE L X t d) (k : ℕ)
    (neg : Bool) : DE L X (dRn t k neg) (if neg then dneg (derive d k) else derive d k) := by
  cases neg
  · simpa [dRn] using de_derive hL hX h k
  · simpa [dRn] using de_neg (de_derive hL hX h k)

theorem toR_natAbs (x : ℤ) : toR ((x.natAbs : ℕ) : ℤ) = |toR x| := by
  unfold toR; rw [Int.natCast_natAbs]; push_cast; rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ prec)]

theorem abs_le_of_mem {I : Ival} {s : ℝ} (h : I.Mem s) :
    |s| ≤ toR (((max I.lo.natAbs I.hi.natAbs : ℕ) : ℤ)) := by
  rw [Nat.cast_max, toR_max', toR_natAbs, toR_natAbs]
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]; exact le_max_of_le_right (h.2.trans (le_abs_self _))
  · rw [abs_of_nonpos hs]; exact le_max_of_le_left (by have := neg_abs_le (toR I.lo); linarith [h.1])

/-- One coordinate of the centered bound: moving from `a` to the anchor changes the value by at least `−err`. -/
theorem coord_step {I A : Ival} {φ : ℝ → ℝ} (hA : A.lo ≤ A.hi) (hsl : Sl I A φ) (rad : ℤ)
    (hrad : rad = (A.hi - A.lo + 1) / 2) {a : ℝ} (ha : A.Mem a) :
    -toR (codeOf I rad).2 ≤ φ a - φ (toR (anchorPt A ((codeOf I rad).1 + 1).toNat)) := by
  unfold codeOf
  split_ifs with h0 h1 h2
  · -- rad = 0: the coordinate is fixed
    have hlo : A.hi ≤ A.lo := by omega
    have heq : A.lo = A.hi := le_antisymm hA hlo
    have ha' : a = toR A.lo := le_antisymm (ha.2.trans (toR_le_toR.mpr hlo)) ha.1
    simp only [Int.reduceAdd, Int.toNat_one, anchorPt, one_ne_zero, if_false, OfNat.one_ne_ofNat]
    rw [← heq, show (A.lo + A.lo) / 2 = A.lo by omega, ha', toR_zero]; simp
  · -- slope ≥ 0: anchor at the lower end
    simp only [show ((-1 : ℤ) + 1).toNat = 0 by rfl, anchorPt, if_true, toR_zero, neg_zero, sub_nonneg]
    rcases eq_or_ne a (toR A.lo) with he | he
    · rw [he]
    · obtain ⟨s, hs, e⟩ := hsl (toR A.lo) a ⟨le_rfl, toR_le_toR.mpr hA⟩ ha (Ne.symm he)
      have : 0 ≤ s * (a - toR A.lo) := mul_nonneg ((toR_nonneg.mpr h1).trans hs.1) (by linarith [ha.1])
      linarith
  · -- slope ≤ 0: anchor at the upper end
    simp only [show ((1 : ℤ) + 1).toNat = 2 by rfl, anchorPt, OfNat.ofNat_ne_zero, if_false, if_true, toR_zero,
      neg_zero, sub_nonneg]
    rcases eq_or_ne a (toR A.hi) with he | he
    · rw [he]
    · obtain ⟨s, hs, e⟩ := hsl (toR A.hi) a ⟨toR_le_toR.mpr hA, le_rfl⟩ ha (Ne.symm he)
      have hs0 : s ≤ 0 := hs.2.trans (by rw [← toR_zero]; exact toR_le_toR.mpr h2)
      have : 0 ≤ s * (a - toR A.hi) := mul_nonneg_of_nonpos_of_nonpos hs0 (by linarith [ha.2])
      linarith
  · -- mixed: anchor at the midpoint, remainder
    simp only [show ((0 : ℤ) + 1).toNat = 1 by rfl, anchorPt, one_ne_zero, if_false, OfNat.one_ne_ofNat]
    set mid := (A.lo + A.hi) / 2
    have hm1 : A.lo ≤ mid := by omega
    have hm2 : mid ≤ A.hi := by omega
    have hr1 : A.hi - mid ≤ rad := by omega
    have hr2 : mid - A.lo ≤ rad := by omega
    have hrad0 : 0 ≤ rad := by omega
    have hdist : |a - toR mid| ≤ toR rad := by
      rw [abs_le]; constructor
      · have := toR_le_toR.mpr hr2; rw [toR_sub] at this; linarith [ha.1]
      · have := toR_le_toR.mpr hr1; rw [toR_sub] at this; linarith [ha.2]
    set M := (((max I.lo.natAbs I.hi.natAbs : ℕ) : ℤ))
    have herr : toR M * toR rad ≤ toR (cdivP (M * rad)) := by
      rw [toR_mul_toR]; exact le_toR_cdivP _
    rcases eq_or_ne a (toR mid) with he | he
    · rw [he, sub_self]
      have : 0 ≤ toR M * toR rad := mul_nonneg (by rw [toR_nonneg]; positivity) (toR_nonneg.mpr hrad0)
      linarith
    · obtain ⟨s, hs, e⟩ := hsl (toR mid) a ⟨toR_le_toR.mpr hm1, toR_le_toR.mpr hm2⟩ ha (Ne.symm he)
      rw [e]
      have h3 : |s * (a - toR mid)| ≤ toR M * toR rad := by
        rw [abs_mul]; exact mul_le_mul (abs_le_of_mem hs) hdist (abs_nonneg _) (by rw [toR_nonneg]; positivity)
      have := neg_abs_le (s * (a - toR mid))
      linarith

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem codeOf_range (I : Ival) (rad : ℤ) : (codeOf I rad).1 = -1 ∨ (codeOf I rad).1 = 0 ∨ (codeOf I rad).1 = 1 := by
  unfold codeOf; split_ifs <;> simp

theorem code_div_mod {a b : ℤ} (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    ((a + 1) * 3 + (b + 1)).toNat / 3 = (a + 1).toNat ∧ ((a + 1) * 3 + (b + 1)).toNat % 3 = (b + 1).toNat := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide

theorem pt_mem (a : ℤ) : (pt a).Mem (toR a) := mem_pt a

theorem pt_nonempty (a : ℤ) : (pt a).lo ≤ (pt a).hi := le_refl a

/-- The body of `lowerB` for an abstract expression and anchor family. -/
def lowerCore (bx : BoxCtx) (expr : DN) (ecOf : ℕ → DN) : Int :=
  if !expr.ok then -1
  else if 0 ≤ expr.v.lo then expr.v.lo
  else
    if !(ecOf ((((codeOf expr.d0 bx.radL).1 + 1) * 3 + ((codeOf expr.d1 bx.radX).1 + 1)).toNat)).ok then expr.v.lo
    else max expr.v.lo ((ecOf ((((codeOf expr.d0 bx.radL).1 + 1) * 3 +
      ((codeOf expr.d1 bx.radX).1 + 1)).toNat)).v.lo - ((codeOf expr.d0 bx.radL).2 + (codeOf expr.d1 bx.radX).2))

theorem lowerB_eq (bx : BoxCtx) (anchor : ℕ → Tri) (t : Tri) (k : ℕ) (neg : Bool) :
    lowerB bx anchor t k neg = lowerCore bx (if neg then dneg (derive t k) else derive t k)
      (fun code => if neg then dneg (derive (anchor code) k) else derive (anchor code) k) := rfl

theorem lowerCore_sound (bx : BoxCtx) (hL : bx.lamI.lo ≤ bx.lamI.hi) (hX : bx.xI.lo ≤ bx.xI.hi)
    (hrL : bx.radL = (bx.lamI.hi - bx.lamI.lo + 1) / 2) (hrX : bx.radX = (bx.xI.hi - bx.xI.lo + 1) / 2)
    {F : RF} {expr : DN} (hE : DE bx.lamI bx.xI F expr) (ecOf : ℕ → DN)
    (hanc : ∀ code, DE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))) F (ecOf code))
    {l x : ℝ} (hl : bx.lamI.Mem l) (hx : bx.xI.Mem x) (h0 : 0 ≤ lowerCore bx expr ecOf) :
    toR (lowerCore bx expr ecOf) ≤ F l x := by
  unfold lowerCore at h0 ⊢
  split_ifs at h0 ⊢ with hok hlo hok2
  · exact absurd h0 (by decide)
  · exact ((hE (by simpa using hok)).val l x hl hx).1
  · exact ((hE (by simpa using hok)).val l x hl hx).1
  · have hE' := hE (by simpa using hok)
    obtain ⟨hq, hr⟩ := code_div_mod (codeOf_range expr.d0 bx.radL) (codeOf_range expr.d1 bx.radX)
    set code := (((codeOf expr.d0 bx.radL).1 + 1) * 3 + ((codeOf expr.d1 bx.radX).1 + 1)).toNat with hcode
    have hA' := hanc code (by simpa using hok2)
    set a0 := anchorPt bx.lamI ((codeOf expr.d0 bx.radL).1 + 1).toNat
    set a1 := anchorPt bx.xI ((codeOf expr.d1 bx.radX).1 + 1).toNat
    have ha0L : bx.lamI.Mem (toR a0) := by
      simp only [a0, anchorPt]; split_ifs
      · exact ⟨le_rfl, toR_le_toR.mpr hL⟩
      · exact ⟨toR_le_toR.mpr hL, le_rfl⟩
      · exact ⟨toR_le_toR.mpr (by omega), toR_le_toR.mpr (by omega)⟩
    have hv := (hA'.val (toR a0) (toR a1) (by rw [hq]; exact pt_mem _) (by rw [hr]; exact pt_mem _)).1
    have s0 := coord_step hL (hE'.sl0 x hx) bx.radL hrL hl
    have s1 := coord_step hX (hE'.sl1 (toR a0) ha0L) bx.radX hrX hx
    rw [toR_max', toR_sub, toR_add]
    refine max_le (hE'.val l x hl hx).1 ?_
    linarith

/-- **Soundness of the centered lower bound**: a nonnegative result of `lowerB` is a lower bound of the (possibly
negated) derived quantity at every point of the box. -/
theorem lowerB_sound (bx : BoxCtx) (hL : bx.lamI.lo ≤ bx.lamI.hi) (hX : bx.xI.lo ≤ bx.xI.hi)
    (hrL : bx.radL = (bx.lamI.hi - bx.lamI.lo + 1) / 2) (hrX : bx.radX = (bx.xI.hi - bx.xI.lo + 1) / 2)
    {t : TriR} {d : Tri} (hT : TE bx.lamI bx.xI t d) (anchor : ℕ → Tri)
    (hanc : ∀ code, TE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))) t (anchor code))
    (k : ℕ) (neg : Bool) {l x : ℝ} (hl : bx.lamI.Mem l) (hx : bx.xI.Mem x) (h0 : 0 ≤ lowerB bx anchor d k neg) :
    toR (lowerB bx anchor d k neg) ≤ dRn t k neg l x := by
  rw [lowerB_eq] at h0 ⊢
  exact lowerCore_sound bx hL hX hrL hrX (de_dRn hL hX hT k neg) _
    (fun code => de_dRn (pt_nonempty _) (pt_nonempty _) (hanc code) k neg) hl hx h0

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The quadratic tests (`PRO_R2_PROOF.md` §6) -/

theorem quad_min_nonneg {A B E : ℝ} (hA : 0 < A) (hm : 0 ≤ E - B ^ 2 / (4 * A)) (η : ℝ) :
    0 ≤ A * η ^ 2 + B * η + E := by
  have e : A * η ^ 2 + B * η + E = A * (η + B / (2 * A)) ^ 2 + (E - B ^ 2 / (4 * A)) := by field_simp; ring
  rw [e]; have := sq_nonneg (η + B / (2 * A)); positivity

theorem quad_det_nonneg {A B E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) (hd : 0 ≤ A * 4 * E - B ^ 2) (η : ℝ) :
    0 ≤ A * η ^ 2 + B * η + E := by
  rcases hA.eq_or_lt with h0 | hpos
  · subst h0
    have hB : B = 0 := by nlinarith [sq_nonneg B]
    subst hB; simpa using hE
  · have h4 : 0 ≤ 4 * A * (A * η ^ 2 + B * η + E) := by nlinarith [sq_nonneg (2 * A * η + B)]
    nlinarith

/-- **The half-line test** (`η ≥ 0`). -/
theorem quad_half {A B E : ℝ} (hE : 0 ≤ E) (hA : 0 ≤ A)
    (h : 0 ≤ B ∨ (0 < A ∧ 0 ≤ E - B ^ 2 / (4 * A)) ∨ 0 ≤ A * 4 * E - B ^ 2) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ A * η ^ 2 + B * η + E := by
  rcases h with h | ⟨h1, h2⟩ | h
  · positivity
  · exact quad_min_nonneg h1 h2 η
  · exact quad_det_nonneg hA hE h η

/-- **The unit-interval test** (`0 ≤ η ≤ 1`). -/
theorem quad_unit {A B E : ℝ} (hE : 0 ≤ E) (hend : 0 ≤ A + B + E)
    (h : A ≤ 0 ∨ 0 ≤ E + B / 2 ∨ (0 ≤ B ∧ 0 ≤ A * 2 + B) ∨ (B ≤ 0 ∧ A * 2 + B ≤ 0) ∨
      (0 < A ∧ (0 ≤ E - B ^ 2 / (4 * A) ∨ 0 ≤ A * 4 * E - B ^ 2)))
    {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) : 0 ≤ A * η ^ 2 + B * η + E := by
  rcases h with h | h | ⟨hB, hD⟩ | ⟨hB, hD⟩ | ⟨hA, h | h⟩
  · -- concave: above the chord
    have : A * η ^ 2 + B * η + E ≥ (1 - η) * E + η * (A + B + E) := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hE, mul_nonneg h0 hend]
  · -- Bernstein form
    have e : A * η ^ 2 + B * η + E = E * (1 - η) ^ 2 + (E + B / 2) * (2 * η * (1 - η)) + (A + B + E) * η ^ 2 := by ring
    rw [e]
    have : 0 ≤ 2 * η * (1 - η) := by nlinarith
    positivity
  · -- increasing
    have : 0 ≤ A * η + B := by nlinarith
    nlinarith
  · -- decreasing: at least the value at 1
    have : A * (η + 1) + B ≤ 0 := by nlinarith
    nlinarith
  · exact quad_min_nonneg hA h η
  · exact quad_det_nonneg hA.le hE h η

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem lowerCore_ok {bx : BoxCtx} {expr : DN} {ecOf : ℕ → DN} (h : 0 ≤ lowerCore bx expr ecOf) : expr.ok = true := by
  unfold lowerCore at h
  by_contra hc
  rw [if_pos (by simpa using hc)] at h
  exact absurd h (by decide)

theorem derive7_ok {d : Tri} (h : (derive d 7).ok = true) : d.A.ok = true ∧ 0 < d.A.v.lo := by
  simp only [derive, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.2⟩

/-- **Soundness of the quadratic test**: a passing control is a nonnegative response quadratic on the range of
its part, at every point of the box. -/
theorem quad_sound (bx : BoxCtx) (hL : bx.lamI.lo ≤ bx.lamI.hi) (hX : bx.xI.lo ≤ bx.xI.hi)
    (hrL : bx.radL = (bx.lamI.hi - bx.lamI.lo + 1) / 2) (hrX : bx.radX = (bx.xI.hi - bx.xI.lo + 1) / 2)
    {t : TriR} {d : Tri} (hT : TE bx.lamI bx.xI t d) (anchor : ℕ → Tri)
    (hanc : ∀ code, TE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))) t (anchor code))
    (part : ℕ) (hq : quad bx anchor d part = true) {l x : ℝ} (hl : bx.lamI.Mem l) (hx : bx.xI.Mem x) {η : ℝ}
    (hη : if part = 1 then 0 ≤ η ∧ η ≤ 1 else 0 ≤ η) : 0 ≤ t.A l x * η ^ 2 + t.B l x * η + t.E l x := by
  -- lower and upper bounds from the centered bound
  have lbF : ∀ k, 0 ≤ lowerB bx anchor d k false → 0 ≤ dR t k l x := fun k h =>
    (toR_nonneg.mpr h).trans (by simpa [dRn] using lowerB_sound bx hL hX hrL hrX hT anchor hanc k false hl hx h)
  have lbP : ∀ k, 0 < lowerB bx anchor d k false → 0 < dR t k l x := fun k h =>
    (toR_pos.mpr h).trans_le (by simpa [dRn] using lowerB_sound bx hL hX hrL hrX hT anchor hanc k false hl hx h.le)
  have ubF : ∀ k, -lowerB bx anchor d k true ≤ 0 → dR t k l x ≤ 0 := fun k h => by
    have h' : 0 ≤ lowerB bx anchor d k true := by omega
    have := (toR_nonneg.mpr h').trans (lowerB_sound bx hL hX hrL hrX hT anchor hanc k true hl hx h')
    simp only [dRn, if_true] at this; linarith
  have hApos : 0 ≤ lowerB bx anchor d 7 false → 0 < t.A l x := fun h => by
    have hok := derive7_ok (by rw [lowerB_eq] at h; simpa using lowerCore_ok h)
    exact (toR_pos.mpr hok.2).trans_le ((hT.1 hok.1).val l x hl hx).1
  unfold quad at hq
  simp only at hq
  split_ifs at hq with h2 hp h0 h1 h3 hub hbern hinc hdec
  all_goals simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true] at hq
  all_goals first
    | (exact absurd hq (by decide))
    | skip
  · -- half-line, B ≥ 0
    rw [if_neg hp] at hη
    exact quad_half (lbF 2 (not_lt.mp h2)) (lbF 0 (not_lt.mp h0)) (Or.inl (lbF 1 h1)) hη
  · rw [if_neg hp] at hη
    rcases hq with ⟨-, h7⟩ | h6
    · exact quad_half (lbF 2 (not_lt.mp h2)) (lbF 0 (not_lt.mp h0)) (Or.inr (Or.inl ⟨hApos h7, lbF 7 h7⟩)) hη
    · exact quad_half (lbF 2 (not_lt.mp h2)) (lbF 0 (not_lt.mp h0)) (Or.inr (Or.inr (lbF 6 h6))) hη
  · have hp1 : part = 1 := by simpa using hp
    rw [if_pos hp1] at hη
    exact quad_unit (lbF 2 (not_lt.mp h2)) (lbF 3 (not_lt.mp h3)) (Or.inl (ubF 0 hub)) hη.1 hη.2
  · have hp1 : part = 1 := by simpa using hp
    rw [if_pos hp1] at hη
    exact quad_unit (lbF 2 (not_lt.mp h2)) (lbF 3 (not_lt.mp h3)) (Or.inr (Or.inl (lbF 5 hbern))) hη.1 hη.2
  · have hp1 : part = 1 := by simpa using hp
    rw [if_pos hp1] at hη
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hinc
    exact quad_unit (lbF 2 (not_lt.mp h2)) (lbF 3 (not_lt.mp h3))
      (Or.inr (Or.inr (Or.inl ⟨lbF 1 hinc.1, lbF 4 hinc.2⟩))) hη.1 hη.2
  · have hp1 : part = 1 := by simpa using hp
    rw [if_pos hp1] at hη
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
    exact quad_unit (lbF 2 (not_lt.mp h2)) (lbF 3 (not_lt.mp h3))
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨ubF 1 hdec.1, ubF 4 hdec.2⟩)))) hη.1 hη.2
  · have hp1 : part = 1 := by simpa using hp
    rw [if_pos hp1] at hη
    obtain ⟨hA0, h7 | h6⟩ := hq
    · exact quad_unit (lbF 2 (not_lt.mp h2)) (lbF 3 (not_lt.mp h3))
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨lbP 0 hA0, Or.inl (lbF 7 h7.2)⟩)))) hη.1 hη.2
    · exact quad_unit (lbF 2 (not_lt.mp h2)) (lbF 3 (not_lt.mp h3))
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨lbP 0 hA0, Or.inr (lbF 6 h6)⟩)))) hη.1 hη.2

end Erdos993Lean.Analytic.O2.Cert
