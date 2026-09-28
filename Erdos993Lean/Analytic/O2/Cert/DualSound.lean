import Mathlib
import Erdos993Lean.Analytic.TailCert.ExpLog
import Erdos993Lean.Analytic.O2.Cert.Compute.Arith

/-!
# O2 certificate checker (lane A18): soundness of the dual numbers

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The computational dual numbers are in
`Erdos993Lean/Analytic/O2/Cert/Compute/Arith.lean`.  A dual number `D` *encloses* a function `f(λ, x)` on the box
`L × X` (`DEnc`) when its value interval contains every value, its `λ`-slope interval contains a divided difference
of `f` along every horizontal pair of points and its `x`-slope interval one along every vertical pair; `DE` asks this
whenever the side-condition flag `D.ok` is set.  Divided differences (slopes) replace derivatives: every rule is an
exact algebraic identity (product, quotient), a mean value inequality proved from `1 − 1/y ≤ log y ≤ y − 1`
(`log_sub_eq`), or the fact that a maximum/minimum moves between its arguments (`Sl.between`).

* interval helpers: `mem_zI`, `mem_oneI`, `mem_twoI`, `mem_fourI`, `mem_eightI`, `mem_knotI`, `mem_sqI`, `mem_imax`,
  `mem_imin`, `mem_hull_between`;
* one-variable slopes `Sl` and their rules `sl_add`, `sl_mul`, `sl_div`, `sl_sq`, `sl_log`, `sl_max`, `sl_min`, …;
* **`DE` rules for every dual-number operation**: `de_add`, `de_addI`, `de_neg`, `de_sub`, `de_mul`, `de_mulI`, `de_div`,
  `de_divI`, `de_sq`, `de_log`, `de_dmax`, `de_mx`, `de_dmin`, `de_mn`, `de_dhull_min`, `de_dhull_max`, `de_cst`,
  `de_lam`, `de_x`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## Interval helpers -/

theorem toR_int_mul_one (k : ℤ) : toR (k * one) = k := by
  unfold toR; rw [one_eq]; push_cast; field_simp

theorem mem_zI : zI.Mem 0 := by
  have := mem_pt 0; rwa [toR_zero] at this

theorem mem_oneI : oneI.Mem 1 := by
  have := mem_pt one; rwa [toR_one] at this

theorem mem_twoI : twoI.Mem 2 := by
  have := mem_pt (2 * one); rw [toR_int_mul_one] at this; exact_mod_cast this

theorem mem_fourI : fourI.Mem 4 := by
  have := mem_pt (4 * one); rw [toR_int_mul_one] at this; exact_mod_cast this

theorem mem_eightI : eightI.Mem 8 := by
  have := mem_pt (8 * one); rw [toR_int_mul_one] at this; exact_mod_cast this

theorem toR_eighth_mul (j : ℤ) : toR (j * eighth) = j / 8 := by
  have h : (j * eighth : ℤ) = j * one / 8 := by
    rw [one_eq]; unfold eighth prec; norm_num; omega
  unfold toR; rw [one_eq] at *; unfold eighth prec; push_cast; ring

theorem mem_knotI (j : ℕ) : (knotI j).Mem ((j : ℝ) / 8) := by
  have := mem_pt ((j : ℤ) * eighth)
  rw [toR_eighth_mul] at this
  unfold knotI; convert this using 2

theorem mem_ptOne (j : ℕ) : (pt ((j : ℤ) * one)).Mem (j : ℝ) := by
  have := mem_pt ((j : ℤ) * one); rw [toR_int_mul_one] at this; exact_mod_cast this

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

theorem toR_max' (a b : ℤ) : toR (max a b) = max (toR a) (toR b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (toR_le_toR.mpr h)]
  · rw [max_eq_left h, max_eq_left (toR_le_toR.mpr h)]

theorem toR_min' (a b : ℤ) : toR (min a b) = min (toR a) (toR b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (toR_le_toR.mpr h)]
  · rw [min_eq_right h, min_eq_right (toR_le_toR.mpr h)]

theorem mem_imax {A B : Ival} {x y : ℝ} (hA : A.Mem x) (hB : B.Mem y) : (imax A B).Mem (max x y) := by
  unfold imax Ival.Mem; simp only [toR_max']
  exact ⟨max_le_max hA.1 hB.1, max_le_max hA.2 hB.2⟩

theorem mem_imin {A B : Ival} {x y : ℝ} (hA : A.Mem x) (hB : B.Mem y) : (imin A B).Mem (min x y) := by
  unfold imin Ival.Mem; simp only [toR_min']
  exact ⟨min_le_min hA.1 hB.1, min_le_min hA.2 hB.2⟩

/-- A number between two members of `A` and `B` lies in their hull. -/
theorem mem_hull_between {A B : Ival} {s t θ : ℝ} (hA : A.Mem s) (hB : B.Mem t) (h1 : min s t ≤ θ)
    (h2 : θ ≤ max s t) : (hull A B).Mem θ := by
  unfold hull Ival.Mem; simp only [toR_min', toR_max']
  exact ⟨(min_le_min hA.1 hB.1).trans h1, h2.trans (max_le_max hA.2 hB.2)⟩

theorem mem_hull_left {A B : Ival} {s : ℝ} (hA : A.Mem s) (hB : ∃ t, B.Mem t) : (hull A B).Mem s := by
  obtain ⟨t, ht⟩ := hB
  exact mem_hull_between hA ht (min_le_left _ _) (le_max_left _ _)

theorem mem_hull_right {A B : Ival} {t : ℝ} (hA : ∃ s, A.Mem s) (hB : B.Mem t) : (hull A B).Mem t := by
  obtain ⟨s, hs⟩ := hA
  exact mem_hull_between hs hB (min_le_right _ _) (le_max_right _ _)

/-- A number between two members of one interval lies in it. -/
theorem Compute.Ival.Mem.between {A : Ival} {s t θ : ℝ} (hs : A.Mem s) (ht : A.Mem t) (h1 : min s t ≤ θ)
    (h2 : θ ≤ max s t) : A.Mem θ :=
  ⟨(le_min hs.1 ht.1).trans h1, h2.trans (max_le hs.2 ht.2)⟩

/-! ## Slopes -/

/-- `I` contains a slope (divided difference) of `φ` between any two distinct points of the interval `L`. -/
def Sl (I L : Ival) (φ : ℝ → ℝ) : Prop :=
  ∀ a b, L.Mem a → L.Mem b → a ≠ b → ∃ s, I.Mem s ∧ φ b - φ a = s * (b - a)

section Slopes

variable {I J C V W L : Ival} {φ ψ : ℝ → ℝ}

theorem sl_congr (h : Sl I L φ) (e : ∀ t, L.Mem t → φ t = ψ t) : Sl I L ψ := by
  intro a b ha hb hab
  obtain ⟨s, hs, hs'⟩ := h a b ha hb hab
  exact ⟨s, hs, by rw [← e a ha, ← e b hb, hs']⟩

theorem sl_const (c : ℝ) : Sl zI L (fun _ => c) := fun _ _ _ _ _ => ⟨0, mem_zI, by ring⟩

theorem sl_id : Sl oneI L (fun t => t) := fun _ _ _ _ _ => ⟨1, mem_oneI, by ring⟩

theorem sl_add (h1 : Sl I L φ) (h2 : Sl J L ψ) : Sl (add I J) L (fun t => φ t + ψ t) := by
  intro a b ha hb hab
  obtain ⟨s1, hs1, e1⟩ := h1 a b ha hb hab
  obtain ⟨s2, hs2, e2⟩ := h2 a b ha hb hab
  exact ⟨s1 + s2, mem_add hs1 hs2, by linear_combination e1 + e2⟩

theorem sl_neg (h : Sl I L φ) : Sl (neg I) L (fun t => -φ t) := by
  intro a b ha hb hab
  obtain ⟨s, hs, e⟩ := h a b ha hb hab
  exact ⟨-s, mem_neg hs, by linear_combination -e⟩

theorem sl_mul (hV : ∀ t, L.Mem t → V.Mem (φ t)) (hW : ∀ t, L.Mem t → W.Mem (ψ t)) (h1 : Sl I L φ)
    (h2 : Sl J L ψ) : Sl (add (mul I W) (mul V J)) L (fun t => φ t * ψ t) := by
  intro a b ha hb hab
  obtain ⟨s1, hs1, e1⟩ := h1 a b ha hb hab
  obtain ⟨s2, hs2, e2⟩ := h2 a b ha hb hab
  refine ⟨s1 * ψ a + φ b * s2, mem_add (mem_mul hs1 (hW a ha)) (mem_mul (hV b hb) hs2), ?_⟩
  linear_combination φ b * e2 + ψ a * e1

theorem sl_mulC {c : ℝ} (hc : C.Mem c) (h : Sl I L φ) : Sl (mul I C) L (fun t => φ t * c) := by
  intro a b ha hb hab
  obtain ⟨s, hs, e⟩ := h a b ha hb hab
  exact ⟨s * c, mem_mul hs hc, by linear_combination c * e⟩

theorem sl_div (hV : ∀ t, L.Mem t → V.Mem (φ t / ψ t)) (hW : ∀ t, L.Mem t → W.Mem (ψ t)) (hpos : 0 < W.lo)
    (h1 : Sl I L φ) (h2 : Sl J L ψ) : Sl (div (sub I (mul V J)) W) L (fun t => φ t / ψ t) := by
  intro a b ha hb hab
  obtain ⟨s1, hs1, e1⟩ := h1 a b ha hb hab
  obtain ⟨s2, hs2, e2⟩ := h2 a b ha hb hab
  have hψb : 0 < ψ b := (toR_pos.mpr hpos).trans_le (hW b hb).1
  have hψa : 0 < ψ a := (toR_pos.mpr hpos).trans_le (hW a ha).1
  refine ⟨(s1 - φ a / ψ a * s2) / ψ b, mem_div (mem_sub hs1 (mem_mul (hV a ha) hs2)) (hW b hb) hpos, ?_⟩
  field_simp
  linear_combination ψ a * e1 - φ a * e2

theorem sl_divC {c : ℝ} (hc : C.Mem c) (hpos : 0 < C.lo) (h : Sl I L φ) : Sl (div I C) L (fun t => φ t / c) := by
  intro a b ha hb hab
  obtain ⟨s, hs, e⟩ := h a b ha hb hab
  have hc0 : 0 < c := (toR_pos.mpr hpos).trans_le hc.1
  refine ⟨s / c, mem_div hs hc hpos, ?_⟩
  field_simp
  linear_combination e

theorem sl_sq (hV : ∀ t, L.Mem t → V.Mem (φ t)) (h : Sl I L φ) :
    Sl (mul (mul twoI V) I) L (fun t => φ t ^ 2) := by
  intro a b ha hb hab
  obtain ⟨s, hs, e⟩ := h a b ha hb hab
  have hm : V.Mem ((φ a + φ b) / 2) :=
    Compute.Ival.Mem.between (hV a ha) (hV b hb) (by rcases le_total (φ a) (φ b) with h | h <;> simp [h] <;> linarith)
      (by rcases le_total (φ a) (φ b) with h | h <;> simp [h] <;> linarith)
  refine ⟨2 * ((φ a + φ b) / 2) * s, mem_mul (mem_mul mem_twoI hm) hs, ?_⟩
  linear_combination (φ a + φ b) * e

/-- The mean value form of the logarithm. -/
theorem log_sub_eq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∃ ξ, min u v ≤ ξ ∧ ξ ≤ max u v ∧ Real.log v - Real.log u = (v - u) / ξ := by
  rcases lt_trichotomy u v with h | h | h
  · have h1 : Real.log v - Real.log u ≤ (v - u) / u := by
      have := Real.log_le_sub_one_of_pos (div_pos hv hu)
      rw [Real.log_div hv.ne' hu.ne'] at this
      rw [sub_div, div_self hu.ne']; linarith
    have h2 : (v - u) / v ≤ Real.log v - Real.log u := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hv hu)
      rw [Real.log_div hv.ne' hu.ne', inv_div] at this
      rw [sub_div, div_self hv.ne']; linarith
    have hpos : 0 < Real.log v - Real.log u := by
      have := Real.log_lt_log hu h; linarith
    refine ⟨(v - u) / (Real.log v - Real.log u), ?_, ?_, ?_⟩
    · rw [min_eq_left h.le, le_div_iff₀ hpos]
      rw [le_div_iff₀ hu] at h1; linarith
    · rw [max_eq_right h.le, div_le_iff₀ hpos]
      rw [div_le_iff₀ hv] at h2; linarith
    · have hvu : v - u ≠ 0 := by linarith
      field_simp
  · subst h; exact ⟨u, by simp, by simp, by simp⟩
  · have h1 : Real.log u - Real.log v ≤ (u - v) / v := by
      have := Real.log_le_sub_one_of_pos (div_pos hu hv)
      rw [Real.log_div hu.ne' hv.ne'] at this
      rw [sub_div, div_self hv.ne']; linarith
    have h2 : (u - v) / u ≤ Real.log u - Real.log v := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
      rw [Real.log_div hu.ne' hv.ne', inv_div] at this
      rw [sub_div, div_self hu.ne']; linarith
    have hpos : 0 < Real.log u - Real.log v := by
      have := Real.log_lt_log hv h; linarith
    refine ⟨(u - v) / (Real.log u - Real.log v), ?_, ?_, ?_⟩
    · rw [min_eq_right h.le, le_div_iff₀ hpos]
      rw [le_div_iff₀ hv] at h1; linarith
    · rw [max_eq_left h.le, div_le_iff₀ hpos]
      rw [div_le_iff₀ hu] at h2; linarith
    · have hne : Real.log u - Real.log v ≠ 0 := hpos.ne'
      have huv : u - v ≠ 0 := by linarith
      rw [div_div_eq_mul_div]
      field_simp
      ring

theorem sl_log (hV : ∀ t, L.Mem t → V.Mem (φ t)) (hpos : 0 < V.lo) (h : Sl I L φ) :
    Sl (div I V) L (fun t => Real.log (φ t)) := by
  intro a b ha hb hab
  obtain ⟨s, hs, e⟩ := h a b ha hb hab
  have hVa : 0 < φ a := (toR_pos.mpr hpos).trans_le (hV a ha).1
  have hVb : 0 < φ b := (toR_pos.mpr hpos).trans_le (hV b hb).1
  obtain ⟨ξ, h1, h2, hξ⟩ := log_sub_eq hVa hVb
  have hξV : V.Mem ξ := Compute.Ival.Mem.between (hV a ha) (hV b hb) h1 h2
  have hξ0 : 0 < ξ := (toR_pos.mpr hpos).trans_le hξV.1
  refine ⟨s / ξ, mem_div hs hξV hpos, ?_⟩
  rw [hξ, e]; field_simp

/-- A difference between two slope-bounded differences has a slope in the hull. -/
theorem slope_between {Δ d1 d2 D s1 s2 : ℝ} (hΔ : Δ ≠ 0) (e1 : d1 = s1 * Δ) (e2 : d2 = s2 * Δ)
    (hlo : min d1 d2 ≤ D) (hhi : D ≤ max d1 d2) :
    min s1 s2 ≤ D / Δ ∧ D / Δ ≤ max s1 s2 := by
  subst e1 e2
  rcases lt_or_gt_of_ne hΔ with hn | hp
  · constructor
    · rw [le_div_iff_of_neg hn]
      rcases le_total s1 s2 with h | h
      · rw [min_eq_left h]; rw [max_eq_left (by nlinarith)] at hhi; exact hhi
      · rw [min_eq_right h]; rw [max_eq_right (by nlinarith)] at hhi; exact hhi
    · rw [div_le_iff_of_neg hn]
      rcases le_total s1 s2 with h | h
      · rw [max_eq_right h]; rw [min_eq_right (by nlinarith)] at hlo; exact hlo
      · rw [max_eq_left h]; rw [min_eq_left (by nlinarith)] at hlo; exact hlo
  · constructor
    · rw [le_div_iff₀ hp]
      rcases le_total s1 s2 with h | h
      · rw [min_eq_left h]; rw [min_eq_left (by nlinarith)] at hlo; exact hlo
      · rw [min_eq_right h]; rw [min_eq_right (by nlinarith)] at hlo; exact hlo
    · rw [div_le_iff₀ hp]
      rcases le_total s1 s2 with h | h
      · rw [max_eq_right h]; rw [max_eq_right (by nlinarith)] at hhi; exact hhi
      · rw [max_eq_left h]; rw [max_eq_left (by nlinarith)] at hhi; exact hhi

/-- A function whose differences lie between those of two slope-bounded functions has slopes in the hull. -/
theorem sl_between {f : ℝ → ℝ} (h1 : Sl I L φ) (h2 : Sl J L ψ)
    (hb : ∀ a b, L.Mem a → L.Mem b →
      min (φ b - φ a) (ψ b - ψ a) ≤ f b - f a ∧ f b - f a ≤ max (φ b - φ a) (ψ b - ψ a)) :
    Sl (hull I J) L f := by
  intro a b ha hb' hab
  obtain ⟨s1, hs1, e1⟩ := h1 a b ha hb' hab
  obtain ⟨s2, hs2, e2⟩ := h2 a b ha hb' hab
  have hΔ : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  obtain ⟨hl, hh⟩ := hb a b ha hb'
  obtain ⟨g1, g2⟩ := slope_between hΔ e1 e2 hl hh
  exact ⟨(f b - f a) / (b - a), mem_hull_between hs1 hs2 g1 g2, by field_simp⟩

theorem max_sub_max_between (p q r s : ℝ) :
    min (r - p) (s - q) ≤ max r s - max p q ∧ max r s - max p q ≤ max (r - p) (s - q) := by
  constructor
  · rcases le_total p q with h | h
    · rw [max_eq_right h]
      exact (min_le_right _ _).trans (by linarith [le_max_right r s])
    · rw [max_eq_left h]
      exact (min_le_left _ _).trans (by linarith [le_max_left r s])
  · rcases le_total r s with h | h
    · rw [max_eq_right h]
      exact (by linarith [le_max_right p q] : s - max p q ≤ s - q).trans (le_max_right _ _)
    · rw [max_eq_left h]
      exact (by linarith [le_max_left p q] : r - max p q ≤ r - p).trans (le_max_left _ _)

theorem min_sub_min_between (p q r s : ℝ) :
    min (r - p) (s - q) ≤ min r s - min p q ∧ min r s - min p q ≤ max (r - p) (s - q) := by
  constructor
  · rcases le_total r s with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith [min_le_left p q])
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith [min_le_right p q])
  · rcases le_total p q with h | h
    · rw [min_eq_left h]
      exact (by linarith [min_le_left r s] : min r s - p ≤ r - p).trans (le_max_left _ _)
    · rw [min_eq_right h]
      exact (by linarith [min_le_right r s] : min r s - q ≤ s - q).trans (le_max_right _ _)

theorem sl_max (h1 : Sl I L φ) (h2 : Sl J L ψ) : Sl (hull I J) L (fun t => max (φ t) (ψ t)) :=
  sl_between h1 h2 (fun a b _ _ => max_sub_max_between _ _ _ _)

theorem sl_min (h1 : Sl I L φ) (h2 : Sl J L ψ) : Sl (hull I J) L (fun t => min (φ t) (ψ t)) :=
  sl_between h1 h2 (fun a b _ _ => min_sub_min_between _ _ _ _)

/-- The hull of two slope intervals for a function that equals one of two slope-bounded functions at every
point and is below/above both (the minimum/maximum of a family). -/
theorem sl_hull_of_min {f : ℝ → ℝ} (h1 : Sl I L φ) (h2 : Sl J L ψ)
    (hmin : ∀ t, L.Mem t → f t = min (φ t) (ψ t)) : Sl (hull I J) L f :=
  sl_congr (sl_min h1 h2) (fun t ht => (hmin t ht).symm)

theorem sl_hull_of_max {f : ℝ → ℝ} (h1 : Sl I L φ) (h2 : Sl J L ψ)
    (hmax : ∀ t, L.Mem t → f t = max (φ t) (ψ t)) : Sl (hull I J) L f :=
  sl_congr (sl_max h1 h2) (fun t ht => (hmax t ht).symm)

end Slopes

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem sl_addC {I L : Ival} {φ : ℝ → ℝ} (c : ℝ) (h : Sl I L φ) : Sl I L (fun t => φ t + c) := by
  intro a b ha hb hab
  obtain ⟨s, hs, e⟩ := h a b ha hb hab
  exact ⟨s, hs, by linear_combination e⟩

/-! ## Dual numbers enclose functions on a box -/

/-- `D` encloses `f` on the box `L × X`: the values, the slopes in `λ` (at fixed `x`) and in `x` (at fixed `λ`). -/
structure DEnc (L X : Ival) (f : ℝ → ℝ → ℝ) (D : DN) : Prop where
  val : ∀ l x, L.Mem l → X.Mem x → D.v.Mem (f l x)
  sl0 : ∀ x, X.Mem x → Sl D.d0 L (fun l => f l x)
  sl1 : ∀ l, L.Mem l → Sl D.d1 X (fun x => f l x)

/-- `D` encloses `f` on the box whenever its side conditions hold. -/
def DE (L X : Ival) (f : ℝ → ℝ → ℝ) (D : DN) : Prop := D.ok = true → DEnc L X f D

section DE

variable {L X : Ival} {f g : ℝ → ℝ → ℝ} {a b : DN}

theorem de_congr (h : DE L X f a) (e : ∀ l x, L.Mem l → X.Mem x → f l x = g l x) : DE L X g a := by
  intro hok
  have h := h hok
  exact ⟨fun l x hl hx => (e l x hl hx) ▸ h.val l x hl hx,
    fun x hx => sl_congr (h.sl0 x hx) (fun l hl => e l x hl hx),
    fun l hl => sl_congr (h.sl1 l hl) (fun x hx => e l x hl hx)⟩

theorem de_ok_imp {a' : DN} (h : DE L X f a) (hv : a'.v = a.v) (h0 : a'.d0 = a.d0) (h1 : a'.d1 = a.d1)
    (hok : a'.ok = true → a.ok = true) : DE L X f a' := by
  intro hk
  have h := h (hok hk)
  exact ⟨fun l x hl hx => hv ▸ h.val l x hl hx, fun x hx => h0 ▸ h.sl0 x hx, fun l hl => h1 ▸ h.sl1 l hl⟩

theorem de_cst {C : Ival} {c : ℝ} (hc : C.Mem c) : DE L X (fun _ _ => c) (DN.cst C) :=
  fun _ => ⟨fun _ _ _ _ => hc, fun _ _ => sl_const c, fun _ _ => sl_const c⟩

theorem de_lam : DE L X (fun l _ => l) (lamDN L) :=
  fun _ => ⟨fun _ _ hl _ => hl, fun _ _ => sl_id, fun _ _ => sl_const _⟩

theorem de_x : DE L X (fun _ x => x) (xDN X) :=
  fun _ => ⟨fun _ _ _ hx => hx, fun _ _ => sl_const _, fun _ _ => sl_id⟩

theorem de_add (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => f l x + g l x) (dadd a b) := by
  intro hok
  simp only [dadd, Bool.and_eq_true] at hok
  have ha := ha hok.1; have hb := hb hok.2
  exact ⟨fun l x hl hx => mem_add (ha.val l x hl hx) (hb.val l x hl hx),
    fun x hx => sl_add (ha.sl0 x hx) (hb.sl0 x hx), fun l hl => sl_add (ha.sl1 l hl) (hb.sl1 l hl)⟩

theorem de_addI {C : Ival} {c : ℝ} (ha : DE L X f a) (hc : C.Mem c) :
    DE L X (fun l x => f l x + c) (daddI a C) := by
  intro hok
  have ha := ha hok
  exact ⟨fun l x hl hx => mem_add (ha.val l x hl hx) hc, fun x hx => sl_addC c (ha.sl0 x hx),
    fun l hl => sl_addC c (ha.sl1 l hl)⟩

theorem de_neg (ha : DE L X f a) : DE L X (fun l x => -f l x) (dneg a) := by
  intro hok
  have ha := ha hok
  exact ⟨fun l x hl hx => mem_neg (ha.val l x hl hx), fun x hx => sl_neg (ha.sl0 x hx),
    fun l hl => sl_neg (ha.sl1 l hl)⟩

theorem de_sub (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => f l x - g l x) (dsub a b) :=
  (de_add ha (de_neg hb)) |> fun h => de_congr h (fun _ _ _ _ => by ring)

theorem de_subI {C : Ival} {c : ℝ} (ha : DE L X f a) (hc : C.Mem c) :
    DE L X (fun l x => f l x - c) (dsubI a C) :=
  (de_addI ha (mem_neg hc)) |> fun h => de_congr h (fun _ _ _ _ => by ring)

theorem de_rsubI {C : Ival} {c : ℝ} (hc : C.Mem c) (ha : DE L X f a) :
    DE L X (fun l x => c - f l x) (drsubI C a) :=
  (de_addI (de_neg ha) hc) |> fun h => de_congr h (fun _ _ _ _ => by ring)

theorem de_mul (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => f l x * g l x) (dmul a b) := by
  intro hok
  simp only [dmul, Bool.and_eq_true] at hok
  have ha := ha hok.1; have hb := hb hok.2
  exact ⟨fun l x hl hx => mem_mul (ha.val l x hl hx) (hb.val l x hl hx),
    fun x hx => sl_mul (fun l hl => ha.val l x hl hx) (fun l hl => hb.val l x hl hx) (ha.sl0 x hx) (hb.sl0 x hx),
    fun l hl => sl_mul (fun x hx => ha.val l x hl hx) (fun x hx => hb.val l x hl hx) (ha.sl1 l hl) (hb.sl1 l hl)⟩

theorem de_mulI {C : Ival} {c : ℝ} (ha : DE L X f a) (hc : C.Mem c) :
    DE L X (fun l x => f l x * c) (dmulI a C) := by
  intro hok
  have ha := ha hok
  exact ⟨fun l x hl hx => mem_mul (ha.val l x hl hx) hc, fun x hx => sl_mulC hc (ha.sl0 x hx),
    fun l hl => sl_mulC hc (ha.sl1 l hl)⟩

theorem de_div (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => f l x / g l x) (ddiv a b) := by
  intro hok
  simp only [ddiv, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hoka, hokb⟩, hpos⟩ := hok
  have ha := ha hoka; have hb := hb hokb
  have hv : ∀ l x, L.Mem l → X.Mem x → (div a.v b.v).Mem (f l x / g l x) :=
    fun l x hl hx => mem_div (ha.val l x hl hx) (hb.val l x hl hx) hpos
  exact ⟨hv,
    fun x hx => sl_div (fun l hl => hv l x hl hx) (fun l hl => hb.val l x hl hx) hpos (ha.sl0 x hx) (hb.sl0 x hx),
    fun l hl => sl_div (fun x hx => hv l x hl hx) (fun x hx => hb.val l x hl hx) hpos (ha.sl1 l hl) (hb.sl1 l hl)⟩

theorem de_divI {C : Ival} {c : ℝ} (ha : DE L X f a) (hc : C.Mem c) :
    DE L X (fun l x => f l x / c) (ddivI a C) := by
  intro hok
  simp only [ddivI, Bool.and_eq_true, decide_eq_true_eq] at hok
  have ha' := ha hok.1
  exact ⟨fun l x hl hx => mem_div (ha'.val l x hl hx) hc hok.2, fun x hx => sl_divC hc hok.2 (ha'.sl0 x hx),
    fun l hl => sl_divC hc hok.2 (ha'.sl1 l hl)⟩

theorem de_sq (ha : DE L X f a) : DE L X (fun l x => f l x ^ 2) (dsq a) := by
  intro hok
  have ha := ha hok
  exact ⟨fun l x hl hx => mem_sqI (ha.val l x hl hx),
    fun x hx => sl_sq (fun l hl => ha.val l x hl hx) (ha.sl0 x hx),
    fun l hl => sl_sq (fun x hx => ha.val l x hl hx) (ha.sl1 l hl)⟩

theorem de_log (ha : DE L X f a) : DE L X (fun l x => Real.log (f l x)) (dlog a) := by
  intro hok
  simp only [dlog, Bool.and_eq_true, decide_eq_true_eq] at hok
  have ha' := ha hok.1
  have hpos := hok.2
  refine ⟨fun l x hl hx => mem_logI (ha'.val l x hl hx) hpos,
    fun x hx => sl_log (fun l hl => ha'.val l x hl hx) hpos (ha'.sl0 x hx),
    fun l hl => sl_log (fun x hx => ha'.val l x hl hx) hpos (ha'.sl1 l hl)⟩

/-- The value of an enclosed function is at most the upper end. -/
theorem DEnc.le_hi {D : DN} (h : DEnc L X f D) {l x : ℝ} (hl : L.Mem l) (hx : X.Mem x) :
    f l x ≤ toR D.v.hi := (h.val l x hl hx).2

theorem DEnc.lo_le {D : DN} (h : DEnc L X f D) {l x : ℝ} (hl : L.Mem l) (hx : X.Mem x) :
    toR D.v.lo ≤ f l x := (h.val l x hl hx).1

/-- The maximum when the second is surely below the first. -/
theorem max_eq_of_box {ha : DEnc L X f a} {hb : DEnc L X g b} (h : b.v.hi < a.v.lo ∨ b.v.hi ≤ a.v.lo)
    {l x : ℝ} (hl : L.Mem l) (hx : X.Mem x) : max (f l x) (g l x) = f l x := by
  apply max_eq_left
  have h' : b.v.hi ≤ a.v.lo := by rcases h with h | h <;> omega
  exact (hb.le_hi hl hx).trans ((toR_le_toR.mpr h').trans (ha.lo_le hl hx))

theorem de_dhullMax (ha : DE L X f a) (hb : DE L X g b) :
    DE L X (fun l x => max (f l x) (g l x)) ⟨imax a.v b.v, hull a.d0 b.d0, hull a.d1 b.d1, a.ok && b.ok⟩ := by
  intro hok
  simp only [Bool.and_eq_true] at hok
  have ha := ha hok.1; have hb := hb hok.2
  exact ⟨fun l x hl hx => mem_imax (ha.val l x hl hx) (hb.val l x hl hx),
    fun x hx => sl_max (ha.sl0 x hx) (hb.sl0 x hx), fun l hl => sl_max (ha.sl1 l hl) (hb.sl1 l hl)⟩

theorem de_dhullMin (ha : DE L X f a) (hb : DE L X g b) :
    DE L X (fun l x => min (f l x) (g l x)) ⟨imin a.v b.v, hull a.d0 b.d0, hull a.d1 b.d1, a.ok && b.ok⟩ := by
  intro hok
  simp only [Bool.and_eq_true] at hok
  have ha := ha hok.1; have hb := hb hok.2
  exact ⟨fun l x hl hx => mem_imin (ha.val l x hl hx) (hb.val l x hl hx),
    fun x hx => sl_min (ha.sl0 x hx) (hb.sl0 x hx), fun l hl => sl_min (ha.sl1 l hl) (hb.sl1 l hl)⟩

/-- A shortcut branch of a maximum/minimum: the kept operand encloses the extremum. -/
theorem de_keep {o : Bool} (ho : o = true → a.ok = true ∧ b.ok = true) (ha : DE L X f a) (hb : DE L X g b)
    {F : ℝ → ℝ → ℝ} (hF : DEnc L X f a → DEnc L X g b → ∀ l x, L.Mem l → X.Mem x → f l x = F l x) :
    DE L X F { a with ok := o } := by
  intro hok
  have ha' := ha (ho hok).1; have hb' := hb (ho hok).2
  have h := de_congr (fun _ => ha') (hF ha' hb') (ho hok).1
  exact ⟨h.val, h.sl0, h.sl1⟩

theorem ok_and_self {p q : Bool} : (p && q) = true → p = true ∧ q = true := by simp
theorem ok_and_swap {p q : Bool} : (p && q) = true → q = true ∧ p = true := by simp; tauto

theorem de_dmax (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => max (f l x) (g l x)) (dmax a b) := by
  unfold dmax
  split_ifs with h1 h2
  · exact de_keep ok_and_self ha hb (fun ha' hb' l x hl hx => (max_eq_of_box (ha := ha') (hb := hb') (Or.inl h1) hl hx).symm)
  · refine de_keep ok_and_swap hb ha (fun hb' ha' l x hl hx => ?_)
    rw [max_comm]; exact (max_eq_of_box (ha := hb') (hb := ha') (Or.inl h2) hl hx).symm
  · exact de_dhullMax ha hb

theorem de_mx (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => max (f l x) (g l x)) (mx a b) := by
  unfold mx
  split_ifs with h1 h2
  · exact de_keep ok_and_self ha hb (fun ha' hb' l x hl hx => (max_eq_of_box (ha := ha') (hb := hb') (Or.inr h1) hl hx).symm)
  · refine de_keep ok_and_swap hb ha (fun hb' ha' l x hl hx => ?_)
    rw [max_comm]; exact (max_eq_of_box (ha := hb') (hb := ha') (Or.inr h2) hl hx).symm
  · exact de_dhullMax ha hb

theorem min_eq_of_box {ha : DEnc L X f a} {hb : DEnc L X g b} (h : a.v.hi < b.v.lo ∨ a.v.hi ≤ b.v.lo)
    {l x : ℝ} (hl : L.Mem l) (hx : X.Mem x) : min (f l x) (g l x) = f l x := by
  apply min_eq_left
  have h' : a.v.hi ≤ b.v.lo := by rcases h with h | h <;> omega
  exact (ha.le_hi hl hx).trans ((toR_le_toR.mpr h').trans (hb.lo_le hl hx))

theorem de_dmin (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => min (f l x) (g l x)) (dmin a b) := by
  unfold dmin
  split_ifs with h1 h2
  · exact de_keep ok_and_self ha hb (fun ha' hb' l x hl hx => (min_eq_of_box (ha := ha') (hb := hb') (Or.inl h1) hl hx).symm)
  · refine de_keep ok_and_swap hb ha (fun hb' ha' l x hl hx => ?_)
    rw [min_comm]; exact (min_eq_of_box (ha := hb') (hb := ha') (Or.inl h2) hl hx).symm
  · exact de_dhullMin ha hb

theorem de_mn (ha : DE L X f a) (hb : DE L X g b) : DE L X (fun l x => min (f l x) (g l x)) (mn a b) := by
  unfold mn
  split_ifs with h1 h2
  · exact de_keep ok_and_self ha hb (fun ha' hb' l x hl hx => (min_eq_of_box (ha := ha') (hb := hb') (Or.inr h1) hl hx).symm)
  · refine de_keep ok_and_swap hb ha (fun hb' ha' l x hl hx => ?_)
    rw [min_comm]; exact (min_eq_of_box (ha := hb') (hb := ha') (Or.inr h2) hl hx).symm
  · exact de_dhullMin ha hb

/-- The hull of two dual numbers encloses a function that is the minimum of the two enclosed ones. -/
theorem de_dhull_min {F : ℝ → ℝ → ℝ} (ha : DE L X f a) (hb : DE L X g b)
    (hF : ∀ l x, L.Mem l → X.Mem x → F l x = min (f l x) (g l x)) : DE L X F (dhull a b) := by
  intro hok
  simp only [dhull, Bool.and_eq_true] at hok
  have ha := ha hok.1; have hb := hb hok.2
  refine ⟨fun l x hl hx => ?_, fun x hx => sl_hull_of_min (ha.sl0 x hx) (hb.sl0 x hx) (fun l hl => hF l x hl hx),
    fun l hl => sl_hull_of_min (ha.sl1 l hl) (hb.sl1 l hl) (fun x hx => hF l x hl hx)⟩
  rw [hF l x hl hx]
  rcases min_choice (f l x) (g l x) with h | h <;> rw [h]
  · exact mem_hull_left (ha.val l x hl hx) ⟨_, hb.val l x hl hx⟩
  · exact mem_hull_right ⟨_, ha.val l x hl hx⟩ (hb.val l x hl hx)

theorem de_dhull_max {F : ℝ → ℝ → ℝ} (ha : DE L X f a) (hb : DE L X g b)
    (hF : ∀ l x, L.Mem l → X.Mem x → F l x = max (f l x) (g l x)) : DE L X F (dhull a b) := by
  intro hok
  simp only [dhull, Bool.and_eq_true] at hok
  have ha := ha hok.1; have hb := hb hok.2
  refine ⟨fun l x hl hx => ?_, fun x hx => sl_hull_of_max (ha.sl0 x hx) (hb.sl0 x hx) (fun l hl => hF l x hl hx),
    fun l hl => sl_hull_of_max (ha.sl1 l hl) (hb.sl1 l hl) (fun x hx => hF l x hl hx)⟩
  rw [hF l x hl hx]
  rcases max_choice (f l x) (g l x) with h | h <;> rw [h]
  · exact mem_hull_left (ha.val l x hl hx) ⟨_, hb.val l x hl hx⟩
  · exact mem_hull_right ⟨_, ha.val l x hl hx⟩ (hb.val l x hl hx)

end DE

end Erdos993Lean.Analytic.O2.Cert
