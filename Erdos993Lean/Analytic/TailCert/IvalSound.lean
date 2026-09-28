import Mathlib
import Erdos993Lean.Analytic.TailCert.Compute.Ival

/-!
# Fixed-point interval arithmetic: soundness (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  The real semantics of the computational
core `Erdos993Lean/Analytic/TailCert/Compute/Ival.lean`: a fixed-point number `n : ℤ` stands for
`toR n = n / 2 ^ prec`, an interval `A` contains `x` when `toR A.lo ≤ x ≤ toR A.hi` (`Ival.Mem`).

* the rounded divisions: `fdiv_le`, `le_cdiv`, `toR_fdivP_le`, `le_toR_cdivP`;
* each interval operation contains the exact result: `mem_pt`, `mem_add`, `mem_sub`, `mem_neg`,
  `mem_mul` (through `corner_mul`), `mem_div` (divisor interval with `0 < lo`, through
  `corner_div`), `mem_divNat`, `mem_mulNat`, `mem_mulInt`, `mem_sqr` (`0 ≤ lo`), `mem_ofRat`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.TailCert

open Compute

/-! ## Real semantics of fixed-point numbers -/

/-- The real number `n / 2 ^ prec` of a fixed-point number. -/
noncomputable def toR (n : ℤ) : ℝ := n / 2 ^ prec

theorem prec_eq : prec = 64 := rfl

theorem one_eq : one = 2 ^ prec := by decide

theorem two_pow_prec_pos : (0 : ℝ) < 2 ^ prec := by positivity

theorem toR_one : toR one = 1 := by
  unfold toR
  rw [one_eq]
  push_cast
  exact div_self two_pow_prec_pos.ne'

theorem toR_zero : toR 0 = 0 := by simp [toR]

theorem toR_add (a b : ℤ) : toR (a + b) = toR a + toR b := by
  unfold toR; push_cast; ring

theorem toR_sub (a b : ℤ) : toR (a - b) = toR a - toR b := by
  unfold toR; push_cast; ring

theorem toR_neg (a : ℤ) : toR (-a) = -toR a := by
  unfold toR; push_cast; ring

theorem toR_le_toR {a b : ℤ} : toR a ≤ toR b ↔ a ≤ b := by
  unfold toR
  rw [div_le_div_iff_of_pos_right two_pow_prec_pos]
  exact Int.cast_le

theorem toR_lt_toR {a b : ℤ} : toR a < toR b ↔ a < b := by
  unfold toR
  rw [div_lt_div_iff_of_pos_right two_pow_prec_pos]
  exact Int.cast_lt

theorem toR_nonneg {a : ℤ} : 0 ≤ toR a ↔ 0 ≤ a := by
  rw [← toR_zero, toR_le_toR]

theorem toR_pos {a : ℤ} : 0 < toR a ↔ 0 < a := by
  rw [← toR_zero, toR_lt_toR]

theorem toR_min (a b : ℤ) : toR (min a b) = min (toR a) (toR b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (toR_le_toR.mpr h)]
  · rw [min_eq_right h, min_eq_right (toR_le_toR.mpr h)]

theorem toR_max (a b : ℤ) : toR (max a b) = max (toR a) (toR b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (toR_le_toR.mpr h)]
  · rw [max_eq_left h, max_eq_left (toR_le_toR.mpr h)]

/-! ## Rounded divisions -/

theorem fdiv_le (a : ℤ) {b : ℤ} (hb : 0 < b) : (fdiv a b : ℝ) ≤ a / b := by
  unfold fdiv
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

theorem le_cdiv (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  unfold cdiv
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h := Int.ediv_mul_le (-a) hb.ne'
  have h' : a ≤ -(-a / b) * b := by linarith [neg_mul (-a / b) b]
  exact_mod_cast h'

theorem fdivP_eq (a : ℤ) : fdivP a = fdiv a (2 ^ prec) := by
  unfold fdivP fdiv
  rw [Int.shiftRight_eq_div_pow]
  norm_num

theorem cdivP_eq (a : ℤ) : cdivP a = cdiv a (2 ^ prec) := by
  unfold cdivP cdiv
  rw [Int.shiftRight_eq_div_pow]
  norm_num

theorem two_pow_prec_pos_int : (0 : ℤ) < 2 ^ prec := by positivity

/-- `toR ⌊p / 2^prec⌋ ≤ p / 2^(2 prec)`, the rounded product. -/
theorem toR_fdivP_le (p : ℤ) : toR (fdivP p) ≤ (p : ℝ) / 2 ^ prec / 2 ^ prec := by
  unfold toR
  rw [div_le_div_iff_of_pos_right two_pow_prec_pos, fdivP_eq]
  have := fdiv_le p two_pow_prec_pos_int
  simpa using this

theorem le_toR_cdivP (p : ℤ) : (p : ℝ) / 2 ^ prec / 2 ^ prec ≤ toR (cdivP p) := by
  unfold toR
  rw [div_le_div_iff_of_pos_right two_pow_prec_pos, cdivP_eq]
  have := le_cdiv p two_pow_prec_pos_int
  simpa using this

theorem toR_mul_toR (a b : ℤ) : toR a * toR b = ((a * b : ℤ) : ℝ) / 2 ^ prec / 2 ^ prec := by
  unfold toR
  push_cast
  field_simp

/-! ## Intervals -/

/-- `x` lies in the interval `A`. -/
def Compute.Ival.Mem (A : Ival) (x : ℝ) : Prop := toR A.lo ≤ x ∧ x ≤ toR A.hi

theorem mem_pt (n : ℤ) : (pt n).Mem (toR n) := ⟨le_rfl, le_rfl⟩

theorem Compute.Ival.Mem.lo_le_hi {A : Ival} {x : ℝ} (h : A.Mem x) : A.lo ≤ A.hi :=
  toR_le_toR.mp (h.1.trans h.2)

theorem mem_add {A B : Ival} {x y : ℝ} (hA : A.Mem x) (hB : B.Mem y) : (add A B).Mem (x + y) := by
  unfold add Ival.Mem
  simp only [toR_add]
  exact ⟨add_le_add hA.1 hB.1, add_le_add hA.2 hB.2⟩

theorem mem_sub {A B : Ival} {x y : ℝ} (hA : A.Mem x) (hB : B.Mem y) : (sub A B).Mem (x - y) := by
  unfold sub Ival.Mem
  simp only [toR_sub]
  exact ⟨sub_le_sub hA.1 hB.2, sub_le_sub hA.2 hB.1⟩

theorem mem_neg {A : Ival} {x : ℝ} (hA : A.Mem x) : (neg A).Mem (-x) := by
  unfold neg Ival.Mem
  simp only [toR_neg]
  exact ⟨neg_le_neg hA.2, neg_le_neg hA.1⟩

/-- The product of `x ∈ [a, b]` and `y ∈ [c, d]` lies between the least and the greatest of the
four corner products. -/
theorem corner_mul {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hay : min (a * c) (a * d) ≤ a * y ∧ a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with ha | ha
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy1 ha),
        (mul_le_mul_of_nonneg_left hy2 ha).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy2 ha),
        (mul_le_mul_of_nonpos_left hy1 ha).trans (le_max_left _ _)⟩
  have hby : min (b * c) (b * d) ≤ b * y ∧ b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with hb | hb
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy1 hb),
        (mul_le_mul_of_nonneg_left hy2 hb).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy2 hb),
        (mul_le_mul_of_nonpos_left hy1 hb).trans (le_max_left _ _)⟩
  have hxy : min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx1 hy),
        (mul_le_mul_of_nonneg_right hx2 hy).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx2 hy),
        (mul_le_mul_of_nonpos_right hx1 hy).trans (le_max_left _ _)⟩
  constructor
  · refine le_trans ?_ hxy.1
    apply le_min
    · exact (min_le_left _ _).trans hay.1
    · exact (min_le_right _ _).trans hby.1
  · refine hxy.2.trans ?_
    apply max_le
    · exact hay.2.trans (le_max_left _ _)
    · exact hby.2.trans (le_max_right _ _)

theorem mem_mul {A B : Ival} {x y : ℝ} (hA : A.Mem x) (hB : B.Mem y) : (mul A B).Mem (x * y) := by
  obtain ⟨h1, h2⟩ := corner_mul hA.1 hA.2 hB.1 hB.2
  unfold mul Ival.Mem
  simp only
  constructor
  · refine (toR_fdivP_le _).trans (le_trans ?_ h1)
    simp only [toR_mul_toR, Int.cast_min]
    apply le_of_eq
    simp only [min_div_div_right (by positivity : (0 : ℝ) ≤ 2 ^ prec)]
  · refine h2.trans (le_trans ?_ (le_toR_cdivP _))
    simp only [toR_mul_toR, Int.cast_max]
    apply le_of_eq
    simp only [max_div_div_right (by positivity : (0 : ℝ) ≤ 2 ^ prec)]

theorem toR_div_eq (a b : ℤ) (hb : 0 < b) :
    ((a * one : ℤ) : ℝ) / (b : ℝ) / 2 ^ prec = toR a / toR b := by
  unfold toR
  rw [one_eq]
  push_cast
  have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

theorem toR_fdiv_le (a b : ℤ) (hb : 0 < b) : toR (fdiv (a * one) b) ≤ toR a / toR b := by
  rw [← toR_div_eq a b hb]
  unfold toR
  exact div_le_div_of_nonneg_right (fdiv_le _ hb) two_pow_prec_pos.le

theorem le_toR_cdiv (a b : ℤ) (hb : 0 < b) : toR a / toR b ≤ toR (cdiv (a * one) b) := by
  rw [← toR_div_eq a b hb]
  unfold toR
  exact div_le_div_of_nonneg_right (le_cdiv _ hb) two_pow_prec_pos.le

/-- `x / y` for `x ∈ [a, b]`, `y ∈ [c, d]`, `0 < c`, lies between `min(a/c, a/d)` and
`max(b/c, b/d)`. -/
theorem corner_div {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hc : 0 < c) (hy1 : c ≤ y)
    (hy2 : y ≤ d) : min (a / c) (a / d) ≤ x / y ∧ x / y ≤ max (b / c) (b / d) := by
  have hy : 0 < y := hc.trans_le hy1
  have hd : 0 < d := hy.trans_le hy2
  constructor
  · have h1 : a / y ≤ x / y := div_le_div_of_nonneg_right hx1 hy.le
    refine le_trans ?_ h1
    rcases le_total 0 a with ha | ha
    · exact (min_le_right _ _).trans (div_le_div_of_nonneg_left ha hy hy2)
    · refine (min_le_left _ _).trans ?_
      rw [div_le_div_iff₀ hc hy]
      nlinarith
  · have h1 : x / y ≤ b / y := div_le_div_of_nonneg_right hx2 hy.le
    refine h1.trans ?_
    rcases le_total 0 b with hb | hb
    · exact (div_le_div_of_nonneg_left hb hc hy1).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [div_le_div_iff₀ hy hd]
      nlinarith

theorem mem_div {A B : Ival} {x y : ℝ} (hA : A.Mem x) (hB : B.Mem y) (hpos : 0 < B.lo) :
    (div A B).Mem (x / y) := by
  have hBhi : 0 < B.hi := lt_of_lt_of_le hpos hB.lo_le_hi
  have hc : 0 < toR B.lo := toR_pos.mpr hpos
  obtain ⟨h1, h2⟩ := corner_div hA.1 hA.2 hc hB.1 hB.2
  unfold div Ival.Mem
  simp only [toR_min, toR_max]
  constructor
  · refine le_trans ?_ h1
    exact min_le_min (toR_fdiv_le _ _ hpos) (toR_fdiv_le _ _ hBhi)
  · refine h2.trans ?_
    exact max_le_max (le_toR_cdiv _ _ hpos) (le_toR_cdiv _ _ hBhi)

theorem mem_divNat {A : Ival} {x : ℝ} (hA : A.Mem x) {k : ℕ} (hk : 0 < k) :
    (divNat A k).Mem (x / k) := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold divNat Ival.Mem
  constructor
  · unfold toR
    have := fdiv_le A.lo hk'
    have h1 : toR A.lo / k ≤ x / k := div_le_div_of_nonneg_right hA.1 hkR.le
    refine le_trans ?_ h1
    unfold toR
    rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) two_pow_prec_pos.le
  · unfold toR
    have := le_cdiv A.hi hk'
    have h1 : x / k ≤ toR A.hi / k := div_le_div_of_nonneg_right hA.2 hkR.le
    refine h1.trans ?_
    unfold toR
    rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) two_pow_prec_pos.le

theorem mem_mulNat {A : Ival} {x : ℝ} (hA : A.Mem x) (k : ℕ) : (mulNat A k).Mem (x * k) := by
  unfold mulNat Ival.Mem
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · have : toR (A.lo * (k : ℤ)) = toR A.lo * k := by unfold toR; push_cast; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hA.1 hk
  · have : toR (A.hi * (k : ℤ)) = toR A.hi * k := by unfold toR; push_cast; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hA.2 hk

theorem mem_mulInt {A : Ival} {x : ℝ} (hA : A.Mem x) (e : ℤ) : (mulInt A e).Mem (x * e) := by
  have hlo : toR (A.lo * e) = toR A.lo * e := by unfold toR; push_cast; ring
  have hhi : toR (A.hi * e) = toR A.hi * e := by unfold toR; push_cast; ring
  unfold mulInt
  split_ifs with he
  · have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
    refine ⟨?_, ?_⟩
    · show toR (A.lo * e) ≤ x * e
      rw [hlo]; exact mul_le_mul_of_nonneg_right hA.1 he'
    · show x * e ≤ toR (A.hi * e)
      rw [hhi]; exact mul_le_mul_of_nonneg_right hA.2 he'
  · have he' : (e : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp he))
    refine ⟨?_, ?_⟩
    · show toR (A.hi * e) ≤ x * e
      rw [hhi]; exact mul_le_mul_of_nonpos_right hA.2 he'
    · show x * e ≤ toR (A.lo * e)
      rw [hlo]; exact mul_le_mul_of_nonpos_right hA.1 he'

theorem mem_sqr {A : Ival} {x : ℝ} (hA : A.Mem x) (h0 : 0 ≤ A.lo) : (sqr A).Mem (x ^ 2) := by
  have ha : 0 ≤ toR A.lo := toR_nonneg.mpr h0
  unfold sqr Ival.Mem
  constructor
  · refine (toR_fdivP_le _).trans ?_
    rw [← toR_mul_toR, sq]
    exact mul_le_mul hA.1 hA.1 ha (ha.trans hA.1)
  · refine le_trans ?_ (le_toR_cdivP _)
    rw [← toR_mul_toR, sq]
    exact mul_le_mul hA.2 hA.2 (ha.trans hA.1) ((ha.trans hA.1).trans hA.2)

theorem mem_ofRat (q : ℚ) : (ofRat q).Mem (q : ℝ) := by
  have hd : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.pos
  have hq : (q : ℝ) = ((q.num * one : ℤ) : ℝ) / ((q.den : ℤ) : ℝ) / 2 ^ prec := by
    rw [one_eq]
    push_cast
    rw [Rat.cast_def]
    field_simp
  unfold ofRat Ival.Mem
  rw [hq]
  constructor
  · unfold toR
    exact div_le_div_of_nonneg_right (fdiv_le _ hd) two_pow_prec_pos.le
  · unfold toR
    exact div_le_div_of_nonneg_right (le_cdiv _ hd) two_pow_prec_pos.le

end Erdos993Lean.Analytic.TailCert
