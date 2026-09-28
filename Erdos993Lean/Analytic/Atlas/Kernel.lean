import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Binom
import Erdos993Lean.Analytic.NoValley.FiniteRange

/-!
# The O4 atlas (lane A9): the analytic bounds behind the checker

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  Sources: Soul's `SOUL/O4/ATLAS_PROOF.md`
(section "Uniform finite-atom bounds in q") and `SOUL/O4/PARAMETER_BOX_PROOF.md` (section "Pointwise
proof on a q interval"), adjudicated CORRECT in `LEAN/referee/REVIEW_SOUL_ROUND2.md`, item 2; the
kernel `κ` of `Erdos993Lean/Analytic/Defs.lean`.

For `0 ≤ j ≤ M` write `κ_x(M, j) = W(x) P(x)` with `W(x) = b_M(j; x)/(x(1 − x))`,
`P(x) = a(1 − x)² + b x²`, `a = (M + 1 − 2j)/(M − j + 1)`, `b = (2j + 1 − M)/(j + 1)`, and
`W' = W L`, `L(x) = (j − 1)/x − (M − j − 1)/(1 − x)`.

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* `kappa_neg_one`, `kappa_top`: `κ(M, −1) = −(1 − x)^M`, `κ(M, M + 1) = −x^M`.
* `binom_rel_left`, `binom_rel_right`, **`kappa_eq_WP`** (`κ = W P`), **`hasDerivAt_Wf`** (`W' = W L`).
* `Wf_mono`, `Wf_anti` and **`Wf_le_of_candidates`**: the maximum of `W` on `[ql, qh]` is at an
  endpoint or at the stationary point `(j − 1)/(M − 2)` (Soul's candidates).
* `abs_Lf_le` (reciprocal ranges), `abs_dPf_le` (`P'` affine), **`abs_Pf_le`** (endpoints and the
  vertex `a/(a + b)`).
* **`kappa_ge_firstOrder`**: Soul's first-order q-uniform bound
  `κ_q ≥ κ_{q0} − ((qh − ql)/2) W_max (|P'|_max + |L|_max |P|_max)` (mean value theorem for `W`,
  exact difference of the quadratic `P`); `kappa_neg_one_ge`, `kappa_top_ge` for `j = −1`, `M + 1`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.Atlas

/-- `κ(M, −1) = −(1 − q)^M`. -/
theorem kappa_neg_one {q : ℝ} (hq1 : q < 1) (M : ℕ) : kappa q M (-1) = -((1 - q) ^ M) := by
  have h1 : (1 - q) ≠ 0 := by linarith
  have e0 : binom M q (-1 + 1) = (1 - q) ^ M := by
    rw [show (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) by norm_num, binom_natCast_of_le q (Nat.zero_le M)]
    simp
  unfold kappa
  rw [binom_of_neg (by norm_num : (-1 : ℤ) < 0), binom_of_neg (by norm_num : (-1 : ℤ) - 1 < 0), e0]
  field_simp
  ring

/-- `κ(M, M + 1) = −q^M`. -/
theorem kappa_top {q : ℝ} (hq0 : 0 < q) (M : ℕ) : kappa q M ((M : ℤ) + 1) = -(q ^ M) := by
  have h0 : q ≠ 0 := hq0.ne'
  have e0 : binom M q ((M : ℤ) + 1 - 1) = q ^ M := by
    rw [show (M : ℤ) + 1 - 1 = ((M : ℕ) : ℤ) by ring, binom_natCast_of_le q le_rfl]
    simp
  unfold kappa
  rw [binom_of_gt (by omega : (M : ℤ) < (M : ℤ) + 1), binom_of_gt (by omega : (M : ℤ) < (M : ℤ) + 1 + 1),
    e0]
  field_simp
  ring

/-- Within one row: `x (M + 1 − j) b_M(j − 1) = j (1 − x) b_M(j)` for `j ≤ M`. -/
theorem binom_rel_left {M j : ℕ} (hj : j ≤ M) (x : ℝ) :
    x * ((M : ℝ) + 1 - j) * binom M x ((j : ℤ) - 1) = (j : ℝ) * (1 - x) * binom M x j := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    rw [binom_of_neg (by norm_num)]
    simp
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [show ((k + 1 : ℕ) : ℤ) - 1 = ((k : ℕ) : ℤ) by push_cast; ring,
    binom_natCast_of_le x (by omega : k ≤ M), binom_natCast_of_le x hj]
  have hc := Nat.choose_succ_right_eq M k
  have hc' : ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hc
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
    rw [this, Nat.cast_sub (by omega)]
  have hp : M - k = (M - (k + 1)) + 1 := by omega
  rw [hp, pow_succ, pow_succ]
  push_cast
  linear_combination (-(x ^ k * (1 - x) ^ (M - (k + 1)) * (1 - x) * x)) * hc'

/-- Within one row: `x (M − j) b_M(j) = (j + 1)(1 − x) b_M(j + 1)` for `j ≤ M`. -/
theorem binom_rel_right {M j : ℕ} (hj : j ≤ M) (x : ℝ) :
    x * ((M : ℝ) - j) * binom M x j = ((j : ℝ) + 1) * (1 - x) * binom M x ((j : ℤ) + 1) := by
  rcases Nat.lt_or_ge j M with hlt | hge
  · rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
      binom_natCast_of_le x hj, binom_natCast_of_le x (by omega : j + 1 ≤ M)]
    have hc := Nat.choose_succ_right_eq M j
    have hc' : ((M.choose (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) = ((M.choose j : ℕ) : ℝ) * ((M : ℝ) - j) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hc
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
      rw [this, Nat.cast_sub (by omega)]
    have hp : M - j = (M - (j + 1)) + 1 := by omega
    rw [hp, pow_succ, pow_succ]
    linear_combination (-(x ^ j * (1 - x) ^ (M - (j + 1)) * x * (1 - x))) * hc'
  · have hjM : j = M := le_antisymm hj hge
    subst hjM
    rw [binom_of_gt (by omega : ((j : ℕ) : ℤ) < (j : ℤ) + 1)]
    simp

/-- Soul's `a = (M + 1 − 2j)/(M − j + 1)`. -/
noncomputable def coefAR (M j : ℕ) : ℝ := ((M : ℝ) + 1 - 2 * (j : ℝ)) / ((M : ℝ) - (j : ℝ) + 1)

/-- Soul's `b = (2j + 1 − M)/(j + 1)`. -/
noncomputable def coefBR (M j : ℕ) : ℝ := (2 * (j : ℝ) + 1 - (M : ℝ)) / ((j : ℝ) + 1)

/-- `W(x) = b_M(j; x)/(x(1 − x))`. -/
noncomputable def Wf (M j : ℕ) (x : ℝ) : ℝ := binom M x j / (x * (1 - x))

/-- `P(x) = a(1 − x)² + b x²`. -/
def Pf (a b x : ℝ) : ℝ := a * ((1 - x) * (1 - x)) + b * (x * x)

/-- `P'(x) = −2a + 2(a + b)x`. -/
def dPf (a b x : ℝ) : ℝ := -2 * a + 2 * (a + b) * x

/-- `L(x) = W'(x)/W(x) = (j − 1)/x − (M − j − 1)/(1 − x)`. -/
noncomputable def Lf (M j : ℕ) (x : ℝ) : ℝ := ((j : ℝ) - 1) / x - ((M : ℝ) - (j : ℝ) - 1) / (1 - x)

/-- **`κ = W·P`** (T1's kernel factorised; Soul's `ATLAS_PROOF.md`, referee R2 item 2). -/
theorem kappa_eq_WP {M j : ℕ} (hj : j ≤ M) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    kappa x M j = Wf M j x * Pf (coefAR M j) (coefBR M j) x := by
  have hl := binom_rel_left hj x
  have hr := binom_rel_right hj x
  have h0 : x ≠ 0 := hx0.ne'
  have h1 : 1 - x ≠ 0 := by linarith
  have hA : (M : ℝ) - j + 1 ≠ 0 := by
    have : (j : ℝ) ≤ M := by exact_mod_cast hj
    linarith
  have hB : (j : ℝ) + 1 ≠ 0 := by positivity
  unfold kappa Wf Pf coefAR coefBR
  field_simp
  have hA' : (M : ℝ) + 1 - j = (M : ℝ) - j + 1 := by ring
  rw [hA'] at hl
  linear_combination (-(1 - x) * ((j : ℝ) + 1)) * hl + (x * ((M : ℝ) - j + 1)) * hr


/-- The closed form of `W`. -/
theorem Wf_eq {M j : ℕ} (hj : j ≤ M) (x : ℝ) :
    Wf M j x = (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) / (x * (1 - x)) := by
  unfold Wf
  rw [binom_natCast_of_le x hj]

theorem Wf_pos {M j : ℕ} (hj : j ≤ M) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < Wf M j x := by
  rw [Wf_eq hj]
  have : (0 : ℝ) < M.choose j := by exact_mod_cast Nat.choose_pos hj
  have h1 : 0 < 1 - x := by linarith
  positivity

theorem natCast_mul_pow_pred_mul (n : ℕ) (y : ℝ) : (n : ℝ) * y ^ (n - 1) * y = (n : ℝ) * y ^ n := by
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    ring

/-- `W' = W·L` on `(0, 1)`. -/
theorem hasDerivAt_Wf {M j : ℕ} (hj : j ≤ M) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (Wf M j) (Wf M j x * Lf M j x) x := by
  have hfun : Wf M j = fun y => (M.choose j : ℝ) * y ^ j * (1 - y) ^ (M - j) / (y * (1 - y)) := by
    funext y
    exact Wf_eq hj y
  have h1 : 0 < 1 - x := by linarith
  have hD : x * (1 - x) ≠ 0 := by positivity
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hN : HasDerivAt (fun y : ℝ => (M.choose j : ℝ) * y ^ j * (1 - y) ^ (M - j))
      ((M.choose j : ℝ) * ((j : ℝ) * x ^ (j - 1)) * (1 - x) ^ (M - j) +
        (M.choose j : ℝ) * x ^ j * (((M - j : ℕ) : ℝ) * (1 - x) ^ (M - j - 1) * (-1))) x := by
    have ha := (hasDerivAt_pow j x).const_mul (M.choose j : ℝ)
    have hb := hsub.pow (M - j)
    exact ha.mul hb
  have hDd : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 * (1 - x) + x * (-1)) x :=
    (hasDerivAt_id x).mul hsub
  have e1 := natCast_mul_pow_pred_mul j x
  have e2 := natCast_mul_pow_pred_mul (M - j) (1 - x)
  have hjM : ((M - j : ℕ) : ℝ) = (M : ℝ) - j := Nat.cast_sub hj
  have key : ((M.choose j : ℝ) * ((j : ℝ) * x ^ (j - 1)) * (1 - x) ^ (M - j) +
        (M.choose j : ℝ) * x ^ j * (((M - j : ℕ) : ℝ) * (1 - x) ^ (M - j - 1) * (-1))) * (x * (1 - x)) =
      (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) * ((j : ℝ) * (1 - x) - ((M : ℝ) - j) * x) := by
    have r : ((M.choose j : ℝ) * ((j : ℝ) * x ^ (j - 1)) * (1 - x) ^ (M - j) +
        (M.choose j : ℝ) * x ^ j * (((M - j : ℕ) : ℝ) * (1 - x) ^ (M - j - 1) * (-1))) * (x * (1 - x)) =
        (M.choose j : ℝ) * (1 - x) ^ (M - j) * (1 - x) * ((j : ℝ) * x ^ (j - 1) * x) -
          (M.choose j : ℝ) * x ^ j * x * (((M - j : ℕ) : ℝ) * (1 - x) ^ (M - j - 1) * (1 - x)) := by ring
    rw [r, e1, e2, hjM]
    ring
  rw [hfun]
  convert hN.div hDd hD using 1
  rw [key]
  unfold Lf
  field_simp
  ring

/-- `L(x) = ((j − 1) − (M − 2)x)/(x(1 − x))`: the sign of `W'` is that of the affine `(j − 1) − (M − 2)x`. -/
theorem Lf_eq (M j : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Lf M j x = (((j : ℝ) - 1) - ((M : ℝ) - 2) * x) / (x * (1 - x)) := by
  have h1 : 1 - x ≠ 0 := by linarith
  unfold Lf
  field_simp
  ring

/-- `W` is nondecreasing on `[a, b] ⊆ (0, 1)` where `(j − 1) − (M − 2)y ≥ 0`. -/
theorem Wf_mono {M j : ℕ} (hj : j ≤ M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hg : ∀ y, a ≤ y → y ≤ b → 0 ≤ ((j : ℝ) - 1) - ((M : ℝ) - 2) * y) : Wf M j a ≤ Wf M j b := by
  have hmon : MonotoneOn (Wf M j) (Set.Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => Wf M j y * Lf M j y)
      (convex_Icc a b) ?_ ?_ ?_
    · intro y hy
      exact (hasDerivAt_Wf hj (by linarith [hy.1]) (by linarith [hy.2])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hasDerivAt_Wf hj (by linarith [hy.1]) (by linarith [hy.2])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0 : 0 < y := by linarith [hy.1]
      have hy1 : y < 1 := by linarith [hy.2]
      show 0 ≤ Wf M j y * Lf M j y
      rw [Lf_eq M j hy0 hy1]
      have := Wf_pos hj hy0 hy1
      have h2 : 0 < y * (1 - y) := by nlinarith
      have := hg y hy.1.le hy.2.le
      positivity
  exact hmon ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- `W` is nonincreasing on `[a, b] ⊆ (0, 1)` where `(j − 1) − (M − 2)y ≤ 0`. -/
theorem Wf_anti {M j : ℕ} (hj : j ≤ M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hg : ∀ y, a ≤ y → y ≤ b → ((j : ℝ) - 1) - ((M : ℝ) - 2) * y ≤ 0) : Wf M j b ≤ Wf M j a := by
  have hmon : AntitoneOn (Wf M j) (Set.Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => Wf M j y * Lf M j y)
      (convex_Icc a b) ?_ ?_ ?_
    · intro y hy
      exact (hasDerivAt_Wf hj (by linarith [hy.1]) (by linarith [hy.2])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hasDerivAt_Wf hj (by linarith [hy.1]) (by linarith [hy.2])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0 : 0 < y := by linarith [hy.1]
      have hy1 : y < 1 := by linarith [hy.2]
      show Wf M j y * Lf M j y ≤ 0
      rw [Lf_eq M j hy0 hy1]
      have hW := Wf_pos hj hy0 hy1
      have h2 : 0 < y * (1 - y) := by nlinarith
      have hgy := hg y hy.1.le hy.2.le
      have : ((j : ℝ) - 1 - ((M : ℝ) - 2) * y) / (y * (1 - y)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hgy h2.le
      exact mul_nonpos_of_nonneg_of_nonpos hW.le this
  exact hmon ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- **`W_max` on `[ql, qh]`** (Soul's candidates): `W(x) ≤ w` for every `x ∈ [ql, qh] ⊆ (0, 1)` as soon
as `W(ql), W(qh) ≤ w` and `W(s) ≤ w` for the stationary point `s = (j − 1)/(M − 2)` when
`ql < s < qh`. -/
theorem Wf_le_of_candidates {M j : ℕ} (hj : j ≤ M) {ql qh x w : ℝ} (h0 : 0 < ql) (h1 : qh < 1)
    (hx : ql ≤ x) (hx' : x ≤ qh) (hwl : Wf M j ql ≤ w) (hwh : Wf M j qh ≤ w)
    (hws : ql < ((j : ℝ) - 1) / ((M : ℝ) - 2) → ((j : ℝ) - 1) / ((M : ℝ) - 2) < qh →
      Wf M j (((j : ℝ) - 1) / ((M : ℝ) - 2)) ≤ w) : Wf M j x ≤ w := by
  set a : ℝ := (j : ℝ) - 1 with ha
  set s : ℝ := (M : ℝ) - 2 with hs
  by_cases hgx : 0 ≤ a - s * x
  · by_cases hgh : 0 ≤ a - s * qh
    · refine le_trans (Wf_mono hj (by linarith) hx' h1 fun y hy1 hy2 => ?_) hwh
      show 0 ≤ a - s * y
      rcases le_or_gt 0 s with hs0 | hs0
      · nlinarith [mul_le_mul_of_nonneg_left hy2 hs0]
      · nlinarith [mul_le_mul_of_nonpos_left hy1 hs0.le]
    · push_neg at hgh
      have hspos : 0 < s := by nlinarith
      have hst1 : x ≤ a / s := by rw [le_div_iff₀ hspos]; linarith
      have hst2 : a / s < qh := by rw [div_lt_iff₀ hspos]; linarith
      have hWx : Wf M j x ≤ Wf M j (a / s) := by
        refine Wf_mono hj (by linarith) hst1 (by linarith) fun y hy1 hy2 => ?_
        have : s * y ≤ s * (a / s) := mul_le_mul_of_nonneg_left hy2 hspos.le
        rw [mul_div_cancel₀ _ hspos.ne'] at this
        linarith
      by_cases hlt : ql < a / s
      · exact hWx.trans (hws hlt hst2)
      · have hxq : x = ql := by push_neg at hlt; linarith
        rw [hxq]
        exact hwl
  · push_neg at hgx
    by_cases hgl : a - s * ql ≤ 0
    · refine le_trans (Wf_anti hj h0 hx (by linarith) fun y hy1 hy2 => ?_) hwl
      show a - s * y ≤ 0
      rcases le_or_gt 0 s with hs0 | hs0
      · nlinarith [mul_le_mul_of_nonneg_left hy1 hs0]
      · nlinarith [mul_le_mul_of_nonpos_left hy2 hs0.le]
    · push_neg at hgl
      have hspos : 0 < s := by nlinarith
      have hst1 : ql < a / s := by rw [lt_div_iff₀ hspos]; linarith
      have hst2 : a / s < x := by rw [div_lt_iff₀ hspos]; linarith
      have hWx : Wf M j x ≤ Wf M j (a / s) := by
        refine Wf_anti hj (by linarith) hst2.le (by linarith) fun y hy1 hy2 => ?_
        have : s * (a / s) ≤ s * y := mul_le_mul_of_nonneg_left hy1 hspos.le
        rw [mul_div_cancel₀ _ hspos.ne'] at this
        linarith
      exact hWx.trans (hws hst1 (by linarith))

/-! ### The factors `|L|`, `|P|`, `|P'|` on `[ql, qh]` -/

theorem abs_le_max_of_between {z u w : ℝ} (h1 : min u w ≤ z) (h2 : z ≤ max u w) :
    |z| ≤ max |u| |w| := by
  rw [abs_le]
  constructor
  · rcases le_total u w with h | h
    · rw [min_eq_left h] at h1
      linarith [neg_abs_le u, le_max_left |u| |w|]
    · rw [min_eq_right h] at h1
      linarith [neg_abs_le w, le_max_right |u| |w|]
  · rcases le_total u w with h | h
    · rw [max_eq_right h] at h2
      linarith [le_abs_self w, le_max_right |u| |w|]
    · rw [max_eq_left h] at h2
      linarith [le_abs_self u, le_max_left |u| |w|]

theorem div_between {c ql qh u : ℝ} (h0 : 0 < ql) (hu : ql ≤ u) (hu' : u ≤ qh) :
    min (c / ql) (c / qh) ≤ c / u ∧ c / u ≤ max (c / ql) (c / qh) := by
  have hu0 : 0 < u := by linarith
  rcases le_total 0 c with hc | hc
  · have e1 : c / qh ≤ c / u := div_le_div_of_nonneg_left hc hu0 hu'
    have e2 : c / u ≤ c / ql := div_le_div_of_nonneg_left hc h0 hu
    exact ⟨(min_le_right _ _).trans e1, e2.trans (le_max_left _ _)⟩
  · have e1 : c / ql ≤ c / u := by
      rw [div_le_div_iff₀ h0 hu0]; nlinarith
    have e2 : c / u ≤ c / qh := by
      rw [div_le_div_iff₀ hu0 (by linarith)]; nlinarith
    exact ⟨(min_le_left _ _).trans e1, e2.trans (le_max_right _ _)⟩

theorem abs_sub_le_of_between {a b a1 a2 b1 b2 : ℝ}
    (ha : min a1 a2 ≤ a ∧ a ≤ max a1 a2) (hb : min b1 b2 ≤ b ∧ b ≤ max b1 b2) :
    |a - b| ≤ max (max |a1 - b1| |a1 - b2|) (max |a2 - b1| |a2 - b2|) := by
  have m1 : |a1 - b1| ≤ max (max |a1 - b1| |a1 - b2|) (max |a2 - b1| |a2 - b2|) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have m2 : |a1 - b2| ≤ max (max |a1 - b1| |a1 - b2|) (max |a2 - b1| |a2 - b2|) :=
    (le_max_right _ _).trans (le_max_left _ _)
  have m3 : |a2 - b1| ≤ max (max |a1 - b1| |a1 - b2|) (max |a2 - b1| |a2 - b2|) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have m4 : |a2 - b2| ≤ max (max |a1 - b1| |a1 - b2|) (max |a2 - b1| |a2 - b2|) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have f1 := abs_le.mp (le_refl |a1 - b1|)
  have f2 := abs_le.mp (le_refl |a1 - b2|)
  have f3 := abs_le.mp (le_refl |a2 - b1|)
  have f4 := abs_le.mp (le_refl |a2 - b2|)
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  rw [abs_le]
  rcases le_total a1 a2 with h1 | h1 <;> rcases le_total b1 b2 with h2 | h2
  · rw [min_eq_left h1] at ha1; rw [max_eq_right h1] at ha2
    rw [min_eq_left h2] at hb1; rw [max_eq_right h2] at hb2
    constructor <;> linarith
  · rw [min_eq_left h1] at ha1; rw [max_eq_right h1] at ha2
    rw [min_eq_right h2] at hb1; rw [max_eq_left h2] at hb2
    constructor <;> linarith
  · rw [min_eq_right h1] at ha1; rw [max_eq_left h1] at ha2
    rw [min_eq_left h2] at hb1; rw [max_eq_right h2] at hb2
    constructor <;> linarith
  · rw [min_eq_right h1] at ha1; rw [max_eq_left h1] at ha2
    rw [min_eq_right h2] at hb1; rw [max_eq_left h2] at hb2
    constructor <;> linarith

/-- The combination `(j − 1)/u − (M − j − 1)/(1 − v)` of Soul's `|L|` bound. -/
noncomputable def lcombR (M j : ℕ) (u v : ℝ) : ℝ := ((j : ℝ) - 1) / u - ((M : ℝ) - (j : ℝ) - 1) / (1 - v)

/-- **`|L| ≤ max_{u, v ∈ {ql, qh}} |(j − 1)/u − (M − j − 1)/(1 − v)|`** on `[ql, qh] ⊆ (0, 1)`. -/
theorem abs_Lf_le {M j : ℕ} {ql qh x : ℝ} (h0 : 0 < ql) (h1 : qh < 1) (hx : ql ≤ x) (hx' : x ≤ qh) :
    |Lf M j x| ≤ max (max |lcombR M j ql ql| |lcombR M j ql qh|)
      (max |lcombR M j qh ql| |lcombR M j qh qh|) := by
  have hA := div_between (c := (j : ℝ) - 1) h0 hx hx'
  have hB := div_between (c := (M : ℝ) - (j : ℝ) - 1) (ql := 1 - qh) (qh := 1 - ql) (u := 1 - x)
    (by linarith) (by linarith) (by linarith)
  have hB' : min ((↑M - ↑j - 1) / (1 - ql)) ((↑M - ↑j - 1) / (1 - qh)) ≤ (↑M - ↑j - 1) / (1 - x) ∧
      (↑M - ↑j - 1) / (1 - x) ≤ max ((↑M - ↑j - 1) / (1 - ql)) ((↑M - ↑j - 1) / (1 - qh)) := by
    rw [min_comm, max_comm]; exact hB
  exact abs_sub_le_of_between hA hB'

/-- `P(y₂) − P(y₁) = (y₂ − y₁) P'((y₁ + y₂)/2)`. -/
theorem Pf_sub (a b y1 y2 : ℝ) : Pf a b y2 - Pf a b y1 = (y2 - y1) * dPf a b ((y1 + y2) / 2) := by
  unfold Pf dPf; ring

theorem dPf_between {a b c d x : ℝ} (hx : c ≤ x) (hx' : x ≤ d) :
    min (dPf a b c) (dPf a b d) ≤ dPf a b x ∧ dPf a b x ≤ max (dPf a b c) (dPf a b d) := by
  unfold dPf
  rcases le_total 0 (a + b) with hs | hs
  · have e1 : 2 * (a + b) * c ≤ 2 * (a + b) * x := by nlinarith
    have e2 : 2 * (a + b) * x ≤ 2 * (a + b) * d := by nlinarith
    exact ⟨(min_le_left _ _).trans (by linarith), le_trans (by linarith) (le_max_right _ _)⟩
  · have e1 : 2 * (a + b) * x ≤ 2 * (a + b) * c := by nlinarith
    have e2 : 2 * (a + b) * d ≤ 2 * (a + b) * x := by nlinarith
    exact ⟨(min_le_right _ _).trans (by linarith), le_trans (by linarith) (le_max_left _ _)⟩

/-- **`|P'| ≤ max(|P'(ql)|, |P'(qh)|)`** on `[ql, qh]` (`P'` is affine). -/
theorem abs_dPf_le {a b ql qh x : ℝ} (hx : ql ≤ x) (hx' : x ≤ qh) :
    |dPf a b x| ≤ max |dPf a b ql| |dPf a b qh| :=
  abs_le_max_of_between (dPf_between hx hx').1 (dPf_between hx hx').2

/-- If `P'` has one sign on `[c, d]` then `P(x)` lies between `P(c)` and `P(d)`. -/
theorem Pf_between {a b c d x : ℝ} (hx : c ≤ x) (hx' : x ≤ d)
    (hsign : (0 ≤ dPf a b c ∧ 0 ≤ dPf a b d) ∨ (dPf a b c ≤ 0 ∧ dPf a b d ≤ 0)) :
    |Pf a b x| ≤ max |Pf a b c| |Pf a b d| := by
  have e1 := Pf_sub a b c x
  have e2 := Pf_sub a b x d
  have m1 := dPf_between (a := a) (b := b) (c := c) (d := d) (x := (c + x) / 2) (by linarith) (by linarith)
  have m2 := dPf_between (a := a) (b := b) (c := c) (d := d) (x := (x + d) / 2) (by linarith) (by linarith)
  apply abs_le_max_of_between
  · rcases hsign with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · have : 0 ≤ dPf a b ((c + x) / 2) := le_trans (le_min hc hd) m1.1
      have : Pf a b c ≤ Pf a b x := by nlinarith
      exact (min_le_left _ _).trans this
    · have : dPf a b ((x + d) / 2) ≤ 0 := le_trans m2.2 (max_le hc hd)
      have : Pf a b d ≤ Pf a b x := by nlinarith
      exact (min_le_right _ _).trans this
  · rcases hsign with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · have : 0 ≤ dPf a b ((x + d) / 2) := le_trans (le_min hc hd) m2.1
      have : Pf a b x ≤ Pf a b d := by nlinarith
      exact this.trans (le_max_right _ _)
    · have : dPf a b ((c + x) / 2) ≤ 0 := le_trans m1.2 (max_le hc hd)
      have : Pf a b x ≤ Pf a b c := by nlinarith
      exact this.trans (le_max_left _ _)

/-- **`|P|_max` on `[ql, qh]`** (Soul's candidates: endpoints and the interior vertex `a/(a + b)`). -/
theorem abs_Pf_le {a b ql qh x p : ℝ} (hx : ql ≤ x) (hx' : x ≤ qh)
    (hl : |Pf a b ql| ≤ p) (hh : |Pf a b qh| ≤ p)
    (hv : a + b ≠ 0 → ql < a / (a + b) → a / (a + b) < qh → |Pf a b (a / (a + b))| ≤ p) :
    |Pf a b x| ≤ p := by
  by_cases hsign : (0 ≤ dPf a b ql ∧ 0 ≤ dPf a b qh) ∨ (dPf a b ql ≤ 0 ∧ dPf a b qh ≤ 0)
  · exact (Pf_between hx hx' hsign).trans (max_le hl hh)
  · -- a strict sign change: the vertex is interior
    have hs : a + b ≠ 0 := by
      intro h0
      apply hsign
      unfold dPf
      rw [h0]
      rcases le_total 0 a with ha | ha
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    have hdv : dPf a b (a / (a + b)) = 0 := by
      unfold dPf; field_simp; ring
    have hql : dPf a b ql = 2 * (a + b) * (ql - a / (a + b)) := by unfold dPf; field_simp; ring
    have hqh : dPf a b qh = 2 * (a + b) * (qh - a / (a + b)) := by unfold dPf; field_simp; ring
    have hin : ql < a / (a + b) ∧ a / (a + b) < qh := by
      constructor
      · by_contra hc
        push_neg at hc
        apply hsign
        rcases lt_or_gt_of_ne hs with hneg | hpos
        · right; constructor
          · rw [hql]; nlinarith
          · rw [hqh]; nlinarith
        · left; constructor
          · rw [hql]; nlinarith
          · rw [hqh]; nlinarith
      · by_contra hc
        push_neg at hc
        apply hsign
        rcases lt_or_gt_of_ne hs with hneg | hpos
        · left; constructor
          · rw [hql]; nlinarith
          · rw [hqh]; nlinarith
        · right; constructor
          · rw [hql]; nlinarith
          · rw [hqh]; nlinarith
    have hpv := hv hs hin.1 hin.2
    rcases le_total x (a / (a + b)) with hxv | hxv
    · refine (Pf_between hx hxv ?_).trans (max_le hl hpv)
      rw [hdv]
      rcases le_total 0 (dPf a b ql) with h | h
      · left; exact ⟨h, le_rfl⟩
      · right; exact ⟨h, le_rfl⟩
    · refine (Pf_between hxv hx' ?_).trans (max_le hpv hh)
      rw [hdv]
      rcases le_total 0 (dPf a b qh) with h | h
      · left; exact ⟨le_rfl, h⟩
      · right; exact ⟨le_rfl, h⟩

/-! ### Soul's first-order q-uniform bound -/

/-- **Soul's first-order q-uniform bound** for `0 ≤ j ≤ M` (`SOUL/O4/ATLAS_PROOF.md`,
`atlas_arb.py: uniform_slack`): with `q0 = (ql + qh)/2`, `W ≤ w`, `|P| ≤ p`, `|P'| ≤ d`, `|L| ≤ l` on
`[ql, qh] ⊆ (0, 1)`, for every `q ∈ [ql, qh]`: `κ_q(M, j) ≥ κ_{q0}(M, j) − ((qh − ql)/2) w (d + l p)`. -/
theorem kappa_ge_firstOrder {M j : ℕ} (hj : j ≤ M) {ql qh q w pa dp la : ℝ} (h0 : 0 < ql)
    (hlh : ql ≤ qh) (h1 : qh < 1) (hq : ql ≤ q) (hq' : q ≤ qh)
    (hW : ∀ x, ql ≤ x → x ≤ qh → Wf M j x ≤ w)
    (hP : ∀ x, ql ≤ x → x ≤ qh → |Pf (coefAR M j) (coefBR M j) x| ≤ pa)
    (hdP : ∀ x, ql ≤ x → x ≤ qh → |dPf (coefAR M j) (coefBR M j) x| ≤ dp)
    (hL : ∀ x, ql ≤ x → x ≤ qh → |Lf M j x| ≤ la) :
    kappa ((ql + qh) / 2) M j - (qh - ql) / 2 * (w * (dp + la * pa)) ≤ kappa q M j := by
  have hq0l : ql ≤ (ql + qh) / 2 := by linarith
  have hq0h : (ql + qh) / 2 ≤ qh := by linarith
  set q0 := (ql + qh) / 2 with hq0
  set a := coefAR M j
  set b := coefBR M j
  have hmvt : |Wf M j q - Wf M j q0| ≤ w * la * |q - q0| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Wf M j)
      (f' := fun x => Wf M j x * Lf M j x) (s := Set.Icc ql qh) (C := w * la)
      (fun x hx => (hasDerivAt_Wf hj (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        have hWx := Wf_pos hj (x := x) (by linarith [hx.1]) (by linarith [hx.2])
        rw [abs_of_pos hWx]
        exact mul_le_mul (hW x hx.1 hx.2) (hL x hx.1 hx.2) (abs_nonneg _)
          (hWx.le.trans (hW x hx.1 hx.2)))
      (convex_Icc ql qh) ⟨hq0l, hq0h⟩ ⟨hq, hq'⟩
    simpa [Real.norm_eq_abs] using this
  have hk := kappa_eq_WP hj (x := q) (by linarith) (by linarith)
  have hk0 := kappa_eq_WP hj (x := q0) (by linarith) (by linarith)
  have hPd : |Pf a b q - Pf a b q0| ≤ dp * |q - q0| := by
    rw [Pf_sub a b q0 q, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hdP _ (by linarith) (by linarith)) (abs_nonneg _)
  have hW0 := Wf_pos hj (x := q0) (by linarith) (by linarith)
  have hw0 : 0 ≤ w := hW0.le.trans (hW q0 hq0l hq0h)
  have hla : 0 ≤ la := (abs_nonneg _).trans (hL q hq hq')
  have hpa : 0 ≤ pa := (abs_nonneg _).trans (hP q hq hq')
  have hdp : 0 ≤ dp := (abs_nonneg _).trans (hdP q hq hq')
  have e : kappa q M j - kappa q0 M j =
      (Wf M j q - Wf M j q0) * Pf a b q + Wf M j q0 * (Pf a b q - Pf a b q0) := by
    rw [hk, hk0]; ring
  have hb : |kappa q M j - kappa q0 M j| ≤ w * (dp + la * pa) * |q - q0| := by
    rw [e]
    calc |(Wf M j q - Wf M j q0) * Pf a b q + Wf M j q0 * (Pf a b q - Pf a b q0)|
        ≤ |Wf M j q - Wf M j q0| * |Pf a b q| + |Wf M j q0| * |Pf a b q - Pf a b q0| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (w * la * |q - q0|) * pa + w * (dp * |q - q0|) := by
          rw [abs_of_pos hW0]
          gcongr
          · exact hP q hq hq'
          · exact hW q0 hq0l hq0h
      _ = w * (dp + la * pa) * |q - q0| := by ring
  have hrad : |q - q0| ≤ (qh - ql) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hK : 0 ≤ w * (dp + la * pa) := by positivity
  have := neg_abs_le (kappa q M j - kappa q0 M j)
  nlinarith [mul_le_mul_of_nonneg_left hrad hK]

/-- The atom `j = −1` (`κ = −(1 − q)^M`): `κ_q ≥ κ_{q0} − ((qh − ql)/2) M (1 − ql)^{M−1}`. -/
theorem kappa_neg_one_ge (M : ℕ) {ql qh q : ℝ} (h1 : qh < 1) (hq : ql ≤ q) (hq' : q ≤ qh) :
    kappa ((ql + qh) / 2) M (-1) - (qh - ql) / 2 * ((M : ℝ) * (1 - ql) ^ (M - 1)) ≤
      kappa q M (-1) := by
  rw [kappa_neg_one (by linarith), kappa_neg_one (by linarith)]
  have h := abs_pow_sub_pow_le (1 - q) (1 - (ql + qh) / 2) M
  have hmax : max |1 - q| |1 - (ql + qh) / 2| ≤ 1 - ql := by
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    exact max_le (by linarith) (by linarith)
  have hpow : max |1 - q| |1 - (ql + qh) / 2| ^ (M - 1) ≤ (1 - ql) ^ (M - 1) :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _
  have hd : |1 - q - (1 - (ql + qh) / 2)| ≤ (qh - ql) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h2 : |(1 - q) ^ M - (1 - (ql + qh) / 2) ^ M| ≤ (qh - ql) / 2 * ((M : ℝ) * (1 - ql) ^ (M - 1)) := by
    refine h.trans ?_
    rw [mul_assoc]
    gcongr
    linarith
  have := le_abs_self ((1 - q) ^ M - (1 - (ql + qh) / 2) ^ M)
  linarith

/-- The atom `j = M + 1` (`κ = −q^M`): `κ_q ≥ κ_{q0} − ((qh − ql)/2) M qh^{M−1}`. -/
theorem kappa_top_ge (M : ℕ) {ql qh q : ℝ} (h0 : 0 < ql) (hq : ql ≤ q) (hq' : q ≤ qh) :
    kappa ((ql + qh) / 2) M ((M : ℤ) + 1) - (qh - ql) / 2 * ((M : ℝ) * qh ^ (M - 1)) ≤
      kappa q M ((M : ℤ) + 1) := by
  rw [kappa_top (by linarith), kappa_top (by linarith)]
  have h := abs_pow_sub_pow_le q ((ql + qh) / 2) M
  have hmax : max |q| |(ql + qh) / 2| ≤ qh := by
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    exact max_le hq' (by linarith)
  have hpow : max |q| |(ql + qh) / 2| ^ (M - 1) ≤ qh ^ (M - 1) :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _
  have hd : |q - (ql + qh) / 2| ≤ (qh - ql) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h2 : |q ^ M - ((ql + qh) / 2) ^ M| ≤ (qh - ql) / 2 * ((M : ℝ) * qh ^ (M - 1)) := by
    refine h.trans ?_
    rw [mul_assoc]
    gcongr
    linarith
  have := le_abs_self (q ^ M - ((ql + qh) / 2) ^ M)
  linarith

end Erdos993Lean.Analytic.Atlas
