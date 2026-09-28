import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Binom

/-!
# Binomial log-concavity: increments, curvatures, chord and Taylor bounds (T1 Lemma 4.1; E4)

Source: T1 (`ProofRuns/2026-09-27_zhang_review/reports/T1.md`), §4, Lemma 4.1 (lines 175–182).

For `0 < q < 1`, `λ = q/(1 − q)` and the binomial masses `b_N(k) = binom N q k` (positive exactly
for `0 ≤ k ≤ N`), T1 uses the log-increments `Δ(k) = log(b_N(k + 1)/b_N(k))` (`logIncr`) and the
curvatures `c_N(k) = log(1 + (N + 1)/(k(N − k)))` (`curvN`).  Lattice points are natural numbers in
`[0, N]`; `logb q N k = log b_N(k)`.

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

Generic discrete calculus for sequences `F : ℕ → ℝ` with curvature
`scurv F m = (F m − F (m − 1)) − (F (m + 1) − F m)`: `seq_incr_ge/le`, `seq_taylor_ge/le` (and the
shifted and reflected forms `seq_taylor_from_ge/le`, `seq_taylor_left_ge/le`),
`seq_concave_nonneg`, `seq_chord_ge`.

**T1 Lemma 4.1.**
* `binom_pos`, `binom_ratio` (`(j + 1)(1 − q) b_N(j + 1) = (N − j) q b_N(j)` for all integers `j`);
* `logIncr_eq`: `Δ(k) = log(λ(N − k)/(k + 1))` for `0 ≤ k < N`;
* `logIncr_sub_logIncr`: `Δ(k − 1) − Δ(k) = c_N(k)` for `1 ≤ k ≤ N − 1`; `curvN_pos`: `c_N(k) > 0`;
  `curvN_symm`: symmetric about `N/2`; `curvN_anti`: decreasing on `[1, N/2]`;
* (i) chord (`logb_chord_ge`): on `[i₋, i₊]`,
  `log b_N(i) ≥ chord(i) + (c_in/2)(i − i₋)(i₊ − i)` for any `c_in ≤ c_N(k)` (`i₋ < k < i₊`), in
  particular `c_in = min_{i₋<k<i₊} c_N(k)`;
* (ii) Taylor (`logb_taylor_ge`, `logb_taylor_le`): for `i ≥ i₀`,
  `log b_N(i) ≥ log b_N(i₀) + (i − i₀)Δ(i₀) − (c̄/2)(i − i₀)(i − i₀ − 1)` for any `c̄ ≥ c_N(k)`
  (`i₀ < k < i`), and `≤` the same with any `c̲ ≤ c_N(k)`; mirror images for `i ≤ i₀`
  (`logb_taylor_left_ge`, `logb_taylor_left_le`, with `Δ(i₀ − 1)` in place of `Δ(i₀)`).
-/

namespace Erdos993Lean.Analytic.NoValley

open Finset

/-! ## Discrete calculus for sequences -/

/-- The curvature of a sequence at `m`: `(F m − F (m − 1)) − (F (m + 1) − F m)`, i.e.
`Δ(m − 1) − Δ(m)` for the increments `Δ(m) = F (m + 1) − F m`. -/
def scurv (F : ℕ → ℝ) (m : ℕ) : ℝ := (F m - F (m - 1)) - (F (m + 1) - F m)

theorem scurv_shift (F : ℕ → ℝ) (i0 : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    scurv (fun k => F (i0 + k)) m = scurv F (i0 + m) := by
  unfold scurv
  have e1 : i0 + (m - 1) = i0 + m - 1 := by omega
  have e2 : i0 + (m + 1) = i0 + m + 1 := by omega
  simp only [e1, e2]

theorem scurv_reflect (F : ℕ → ℝ) (i0 : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m + 1 ≤ i0) :
    scurv (fun k => F (i0 - k)) m = scurv F (i0 - m) := by
  unfold scurv
  have e1 : i0 - (m - 1) = i0 - m + 1 := by omega
  have e2 : i0 - (m + 1) = i0 - m - 1 := by omega
  simp only [e1, e2]
  ring

/-- Increments drop by at most `C` per step if the curvature is at most `C`. -/
theorem seq_incr_ge (F : ℕ → ℝ) (C : ℝ) (n : ℕ) (h : ∀ m, 1 ≤ m → m ≤ n → scurv F m ≤ C) :
    F 1 - F 0 - C * n ≤ F (n + 1) - F n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun m hm1 hm2 => h m hm1 (by omega)
    have hk := h (n + 1) (by omega) le_rfl
    unfold scurv at hk
    rw [Nat.add_sub_cancel] at hk
    push_cast
    linarith

/-- Increments drop by at least `c` per step if the curvature is at least `c`. -/
theorem seq_incr_le (F : ℕ → ℝ) (c : ℝ) (n : ℕ) (h : ∀ m, 1 ≤ m → m ≤ n → c ≤ scurv F m) :
    F (n + 1) - F n ≤ F 1 - F 0 - c * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun m hm1 hm2 => h m hm1 (by omega)
    have hk := h (n + 1) (by omega) le_rfl
    unfold scurv at hk
    rw [Nat.add_sub_cancel] at hk
    push_cast
    linarith

/-- **Discrete Taylor bound from below:** curvature `≤ C` on `[1, n)` gives
`F n ≥ F 0 + n (F 1 − F 0) − C n(n − 1)/2`. -/
theorem seq_taylor_ge (F : ℕ → ℝ) (C : ℝ) (n : ℕ) (h : ∀ m, 1 ≤ m → m < n → scurv F m ≤ C) :
    F 0 + n * (F 1 - F 0) - C * (n * (n - 1) / 2) ≤ F n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun m hm1 hm2 => h m hm1 (by omega)
    have hinc := seq_incr_ge F C n fun m hm1 hm2 => h m hm1 (by omega)
    push_cast
    nlinarith

/-- **Discrete Taylor bound from above:** curvature `≥ c` on `[1, n)` gives
`F n ≤ F 0 + n (F 1 − F 0) − c n(n − 1)/2`. -/
theorem seq_taylor_le (F : ℕ → ℝ) (c : ℝ) (n : ℕ) (h : ∀ m, 1 ≤ m → m < n → c ≤ scurv F m) :
    F n ≤ F 0 + n * (F 1 - F 0) - c * (n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun m hm1 hm2 => h m hm1 (by omega)
    have hinc := seq_incr_le F c n fun m hm1 hm2 => h m hm1 (by omega)
    push_cast
    nlinarith

/-- The Taylor bound from below, anchored at `i0` and going right. -/
theorem seq_taylor_from_ge (F : ℕ → ℝ) (C : ℝ) (i0 n : ℕ)
    (h : ∀ k, i0 < k → k < i0 + n → scurv F k ≤ C) :
    F i0 + n * (F (i0 + 1) - F i0) - C * (n * (n - 1) / 2) ≤ F (i0 + n) := by
  have := seq_taylor_ge (fun k => F (i0 + k)) C n fun m hm1 hm2 => by
    rw [scurv_shift F i0 hm1]
    exact h (i0 + m) (by omega) (by omega)
  simp only [add_zero] at this
  exact this

/-- The Taylor bound from above, anchored at `i0` and going right. -/
theorem seq_taylor_from_le (F : ℕ → ℝ) (c : ℝ) (i0 n : ℕ)
    (h : ∀ k, i0 < k → k < i0 + n → c ≤ scurv F k) :
    F (i0 + n) ≤ F i0 + n * (F (i0 + 1) - F i0) - c * (n * (n - 1) / 2) := by
  have := seq_taylor_le (fun k => F (i0 + k)) c n fun m hm1 hm2 => by
    rw [scurv_shift F i0 hm1]
    exact h (i0 + m) (by omega) (by omega)
  simp only [add_zero] at this
  exact this

/-- The Taylor bound from below, anchored at `i0` and going left (the mirror image). -/
theorem seq_taylor_left_ge (F : ℕ → ℝ) (C : ℝ) (i0 n : ℕ) (hn : n ≤ i0)
    (h : ∀ k, i0 - n < k → k < i0 → scurv F k ≤ C) :
    F i0 - n * (F i0 - F (i0 - 1)) - C * (n * (n - 1) / 2) ≤ F (i0 - n) := by
  have := seq_taylor_ge (fun k => F (i0 - k)) C n fun m hm1 hm2 => by
    rw [scurv_reflect F i0 hm1 (by omega)]
    exact h (i0 - m) (by omega) (by omega)
  simp only [Nat.sub_zero] at this
  linarith

/-- The Taylor bound from above, anchored at `i0` and going left (the mirror image). -/
theorem seq_taylor_left_le (F : ℕ → ℝ) (c : ℝ) (i0 n : ℕ) (hn : n ≤ i0)
    (h : ∀ k, i0 - n < k → k < i0 → c ≤ scurv F k) :
    F (i0 - n) ≤ F i0 - n * (F i0 - F (i0 - 1)) - c * (n * (n - 1) / 2) := by
  have := seq_taylor_le (fun k => F (i0 - k)) c n fun m hm1 hm2 => by
    rw [scurv_reflect F i0 hm1 (by omega)]
    exact h (i0 - m) (by omega) (by omega)
  simp only [Nat.sub_zero] at this
  linarith

/-- A sequence with nonnegative curvature on `(0, n)` that vanishes at `0` and `n` is
nonnegative on `[0, n]`. -/
theorem seq_concave_nonneg (g : ℕ → ℝ) (n : ℕ) (h : ∀ m, 1 ≤ m → m < n → 0 ≤ scurv g m)
    (h0 : g 0 = 0) (hn : g n = 0) (i : ℕ) (hi : i ≤ n) : 0 ≤ g i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [h0]
  rcases eq_or_lt_of_le hi with rfl | hin
  · rw [hn]
  -- forward from `i`: `g n ≤ g i + (n − i)(g (i + 1) − g i)`
  have hf := seq_taylor_from_le g 0 i (n - i) fun k hk1 hk2 => h k (by omega) (by omega)
  rw [Nat.add_sub_cancel' hi, hn, zero_mul, sub_zero, Nat.cast_sub hi] at hf
  -- backward from `i`: `g 0 ≤ g i − i (g i − g (i − 1))`
  have hb := seq_taylor_left_le g 0 i i le_rfl fun k hk1 hk2 => h k (by omega) (by omega)
  rw [Nat.sub_self, h0, zero_mul, sub_zero] at hb
  -- the increments decrease at `i`
  have hc := h i hi0 hin
  unfold scurv at hc
  have hni : (0 : ℝ) ≤ (n : ℝ) - i := by
    have : (i : ℝ) ≤ n := by exact_mod_cast hi
    linarith
  by_cases hG : 0 ≤ g i - g (i - 1)
  · have := mul_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i) hG
    linarith
  · have hG' : g (i + 1) - g i ≤ 0 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos hni hG'
    linarith

/-- **Discrete chord bound:** curvature `≥ c` on `(0, n)` gives
`F i ≥ F 0 + (i/n)(F n − F 0) + (c/2) i(n − i)` on `[0, n]`. -/
theorem seq_chord_ge (F : ℕ → ℝ) (c : ℝ) (n : ℕ) (hn : 0 < n)
    (h : ∀ m, 1 ≤ m → m < n → c ≤ scurv F m) (i : ℕ) (hi : i ≤ n) :
    F 0 + (i : ℝ) / n * (F n - F 0) + c / 2 * ((i : ℝ) * ((n : ℝ) - i)) ≤ F i := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set g : ℕ → ℝ := fun k =>
    F k - (F 0 + (k : ℝ) / n * (F n - F 0) + c / 2 * ((k : ℝ) * ((n : ℝ) - k))) with hg
  have hcurv : ∀ m, 1 ≤ m → m < n → 0 ≤ scurv g m := by
    intro m hm1 hm2
    have hFm := h m hm1 hm2
    have e : scurv g m = scurv F m - c := by
      simp only [scurv, hg]
      rw [Nat.cast_sub hm1]
      push_cast
      field_simp
      ring
    linarith
  have h0 : g 0 = 0 := by simp [hg]
  have hgn : g n = 0 := by
    simp only [hg]
    field_simp
    ring
  have := seq_concave_nonneg g n hcurv h0 hgn i hi
  simp only [hg] at this
  linarith

/-! ## Binomial increments and curvatures -/

/-- `log b_N(k)` on the lattice. -/
noncomputable def logb (q : ℝ) (N : ℕ) (k : ℕ) : ℝ := Real.log (binom N q (k : ℤ))

/-- T1's log-increment `Δ(k) = log(b_N(k + 1)/b_N(k))`. -/
noncomputable def logIncr (q : ℝ) (N k : ℕ) : ℝ :=
  Real.log (binom N q ((k : ℤ) + 1) / binom N q (k : ℤ))

/-- T1's curvature `c_N(k) = log(1 + (N + 1)/(k(N − k)))`. -/
noncomputable def curvN (N k : ℕ) : ℝ := Real.log (1 + ((N : ℝ) + 1) / ((k : ℝ) * ((N : ℝ) - k)))

theorem binom_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N k : ℕ} (hk : k ≤ N) :
    0 < binom N q (k : ℤ) := by
  rw [binom_natCast_of_le q hk]
  have hc : (0 : ℝ) < (N.choose k : ℕ) := by exact_mod_cast Nat.choose_pos hk
  exact mul_pos (mul_pos hc (pow_pos hq0 _)) (pow_pos (sub_pos.mpr hq1) _)

/-- The same-`N` ratio `(j + 1)(1 − q) b_N(j + 1) = (N − j) q b_N(j)`, for every integer `j`. -/
theorem binom_ratio (N : ℕ) (q : ℝ) (j : ℤ) :
    ((j : ℝ) + 1) * (1 - q) * binom N q (j + 1) = ((N : ℝ) - j) * q * binom N q j := by
  rcases N with _ | M
  · rcases lt_trichotomy j 0 with h | h | h
    · rw [binom_of_neg h]
      rcases lt_or_eq_of_le (show j + 1 ≤ 0 by omega) with h' | h'
      · rw [binom_of_neg h']
        ring
      · have : (j : ℝ) + 1 = 0 := by exact_mod_cast h'
        rw [this]
        ring
    · subst h
      rw [binom_of_gt (by norm_num : ((0 : ℕ) : ℤ) < 0 + 1)]
      push_cast
      ring
    · rw [binom_of_gt (by push_cast; omega : ((0 : ℕ) : ℤ) < j),
        binom_of_gt (by push_cast; omega : ((0 : ℕ) : ℤ) < j + 1)]
      ring
  · have h1 := binom_step_left M q (j + 1)
    have h2 := binom_step_right M q j
    rw [add_sub_cancel_right] at h1
    push_cast at h1 h2 ⊢
    linear_combination (q - 1) * h1 + q * h2

theorem logb_succ_sub {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N k : ℕ} (hk : k < N) :
    logb q N (k + 1) - logb q N k = logIncr q N k := by
  unfold logb logIncr
  have e : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hb1 := binom_pos hq0 hq1 (by omega : k + 1 ≤ N)
  rw [e] at hb1 ⊢
  rw [Real.log_div hb1.ne' (binom_pos hq0 hq1 hk.le).ne']

/-- **T1 Lemma 4.1, increments.** `Δ(k) = log(λ(N − k)/(k + 1))` for `0 ≤ k < N`, `λ = q/(1 − q)`. -/
theorem logIncr_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N k : ℕ} (hk : k < N) :
    logIncr q N k = Real.log (q / (1 - q) * ((N : ℝ) - k) / ((k : ℝ) + 1)) := by
  unfold logIncr
  congr 1
  have hb := binom_pos hq0 hq1 hk.le
  have hq1' : (1 - q) ≠ 0 := (sub_pos.mpr hq1).ne'
  have hr := binom_ratio N q k
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [div_eq_iff hb.ne']
  field_simp
  linear_combination hr

/-- **T1 Lemma 4.1, curvatures.** `Δ(k − 1) − Δ(k) = c_N(k)` for `1 ≤ k ≤ N − 1`. -/
theorem logIncr_sub_logIncr {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k + 1 ≤ N) : logIncr q N (k - 1) - logIncr q N k = curvN N k := by
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.mpr hq1
  rw [logIncr_eq hq0 hq1 (by omega), logIncr_eq hq0 hq1 (by omega)]
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk2
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hA : 0 < q / (1 - q) * ((N : ℝ) - ((k - 1 : ℕ) : ℝ)) / (((k - 1 : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_sub hk1]
    push_cast
    apply div_pos (mul_pos (div_pos hq0 hq1') (by linarith)) (by linarith)
  have hB : 0 < q / (1 - q) * ((N : ℝ) - k) / ((k : ℝ) + 1) :=
    div_pos (mul_pos (div_pos hq0 hq1') (by linarith)) (by linarith)
  rw [← Real.log_div hA.ne' hB.ne', curvN]
  congr 1
  rw [Nat.cast_sub hk1]
  push_cast
  rw [sub_add_cancel]
  have h1 : (k : ℝ) ≠ 0 := by linarith
  have h2 : (N : ℝ) - k ≠ 0 := by linarith
  have h3 : (1 - q) ≠ 0 := hq1'.ne'
  have h4 : q ≠ 0 := hq0.ne'
  have h5 : (k : ℝ) + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem curvN_pos {N k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ N) : 0 < curvN N k := by
  unfold curvN
  apply Real.log_pos
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk2
  have : 0 < ((N : ℝ) + 1) / ((k : ℝ) * ((N : ℝ) - k)) :=
    div_pos (by positivity) (mul_pos (by linarith) (by linarith))
  linarith

/-- `c_N` is symmetric about `N/2`. -/
theorem curvN_symm {N k : ℕ} (hk : k ≤ N) : curvN N (N - k) = curvN N k := by
  unfold curvN
  rw [Nat.cast_sub hk]
  ring_nf

/-- `c_N` is decreasing on `[1, N/2]`. -/
theorem curvN_anti {N k k' : ℕ} (hk1 : 1 ≤ k) (hkk' : k ≤ k') (hk' : 2 * k' ≤ N) :
    curvN N k' ≤ curvN N k := by
  unfold curvN
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkk'' : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
  have hk'' : 2 * (k' : ℝ) ≤ N := by exact_mod_cast hk'
  have hpos : 0 < (k : ℝ) * ((N : ℝ) - k) := mul_pos (by linarith) (by linarith)
  have hle : (k : ℝ) * ((N : ℝ) - k) ≤ (k' : ℝ) * ((N : ℝ) - k') := by nlinarith
  have hfrac : ((N : ℝ) + 1) / ((k' : ℝ) * ((N : ℝ) - k')) ≤
      ((N : ℝ) + 1) / ((k : ℝ) * ((N : ℝ) - k)) :=
    div_le_div_of_nonneg_left (by positivity) hpos hle
  have hpos' : 0 < 1 + ((N : ℝ) + 1) / ((k' : ℝ) * ((N : ℝ) - k')) := by
    have : 0 < ((N : ℝ) + 1) / ((k' : ℝ) * ((N : ℝ) - k')) :=
      div_pos (by positivity) (lt_of_lt_of_le hpos hle)
    linarith
  exact Real.log_le_log hpos' (by linarith)

/-- The curvature of `log b_N` at a lattice point `1 ≤ k ≤ N − 1` is `c_N(k)`. -/
theorem scurv_logb {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ N) :
    scurv (logb q N) k = curvN N k := by
  unfold scurv
  have e1 := logb_succ_sub hq0 hq1 (by omega : k - 1 < N)
  have e2 := logb_succ_sub hq0 hq1 (by omega : k < N)
  rw [Nat.sub_add_cancel hk1] at e1
  rw [e1, e2]
  exact logIncr_sub_logIncr hq0 hq1 hk1 hk2

/-! ## T1 Lemma 4.1 (i), (ii) -/

/-- **T1 Lemma 4.1 (i), the chord bound.**  For lattice points `i₋ < i₊ ≤ N` and any `c_in` with
`c_in ≤ c_N(k)` for `i₋ < k < i₊` (e.g. the minimum), every `i ∈ [i₋, i₊]` satisfies
`log b_N(i) ≥ chord(i) + (c_in/2)(i − i₋)(i₊ − i)`, where `chord` interpolates `log b_N` linearly
between `i₋` and `i₊`. -/
theorem logb_chord_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N im ip : ℕ} (hmp : im < ip)
    (hpN : ip ≤ N) (cin : ℝ) (hc : ∀ k, im < k → k < ip → cin ≤ curvN N k) (i : ℕ) (hi1 : im ≤ i)
    (hi2 : i ≤ ip) :
    logb q N im + ((i : ℝ) - im) / ((ip : ℝ) - im) * (logb q N ip - logb q N im) +
        cin / 2 * (((i : ℝ) - im) * ((ip : ℝ) - i)) ≤ logb q N i := by
  have := seq_chord_ge (fun k => logb q N (im + k)) cin (ip - im) (by omega) (fun m hm1 hm2 => by
      rw [scurv_shift _ im hm1, scurv_logb hq0 hq1 (by omega) (by omega)]
      exact hc (im + m) (by omega) (by omega)) (i - im) (by omega)
  simp only [add_zero, Nat.add_sub_cancel' hi1, Nat.add_sub_cancel' hmp.le] at this
  rw [Nat.cast_sub hi1, Nat.cast_sub hmp.le] at this
  have e : ((ip : ℝ) - im) - ((i : ℝ) - im) = (ip : ℝ) - i := by ring
  rw [e] at this
  exact this

/-- **T1 Lemma 4.1 (ii), Taylor from below, to the right.**  For lattice points `i₀ ≤ i ≤ N` and any
`c̄ ≥ c_N(k)` for `i₀ < k < i` (e.g. the maximum):
`log b_N(i) ≥ log b_N(i₀) + (i − i₀)Δ(i₀) − (c̄/2)(i − i₀)(i − i₀ − 1)`. -/
theorem logb_taylor_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N i0 i : ℕ} (hi : i0 ≤ i) (hiN : i ≤ N)
    (cbar : ℝ) (hc : ∀ k, i0 < k → k < i → curvN N k ≤ cbar) :
    logb q N i0 + ((i : ℝ) - i0) * logIncr q N i0 -
        cbar / 2 * (((i : ℝ) - i0) * ((i : ℝ) - i0 - 1)) ≤ logb q N i := by
  have := seq_taylor_from_ge (logb q N) cbar i0 (i - i0) fun k hk1 hk2 => by
    rw [scurv_logb hq0 hq1 (by omega) (by omega)]
    exact hc k hk1 (by omega)
  rw [Nat.add_sub_cancel' hi, Nat.cast_sub hi] at this
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    simp
  · rw [logb_succ_sub hq0 hq1 (by omega)] at this
    linarith

/-- **T1 Lemma 4.1 (ii), Taylor from above, to the right.**  For lattice points `i₀ ≤ i ≤ N` and any
`c̲ ≤ c_N(k)` for `i₀ < k < i` (e.g. the minimum):
`log b_N(i) ≤ log b_N(i₀) + (i − i₀)Δ(i₀) − (c̲/2)(i − i₀)(i − i₀ − 1)`. -/
theorem logb_taylor_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N i0 i : ℕ} (hi : i0 ≤ i) (hiN : i ≤ N)
    (cund : ℝ) (hc : ∀ k, i0 < k → k < i → cund ≤ curvN N k) :
    logb q N i ≤ logb q N i0 + ((i : ℝ) - i0) * logIncr q N i0 -
        cund / 2 * (((i : ℝ) - i0) * ((i : ℝ) - i0 - 1)) := by
  have := seq_taylor_from_le (logb q N) cund i0 (i - i0) fun k hk1 hk2 => by
    rw [scurv_logb hq0 hq1 (by omega) (by omega)]
    exact hc k hk1 (by omega)
  rw [Nat.add_sub_cancel' hi, Nat.cast_sub hi] at this
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    simp
  · rw [logb_succ_sub hq0 hq1 (by omega)] at this
    linarith

/-- **T1 Lemma 4.1 (ii), mirror image, from below.**  For lattice points `i ≤ i₀ ≤ N` and any
`c̄ ≥ c_N(k)` for `i < k < i₀`:
`log b_N(i) ≥ log b_N(i₀) − (i₀ − i)Δ(i₀ − 1) − (c̄/2)(i₀ − i)(i₀ − i − 1)`. -/
theorem logb_taylor_left_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N i0 i : ℕ} (hi : i ≤ i0)
    (hiN : i0 ≤ N) (cbar : ℝ) (hc : ∀ k, i < k → k < i0 → curvN N k ≤ cbar) :
    logb q N i0 - ((i0 : ℝ) - i) * logIncr q N (i0 - 1) -
        cbar / 2 * (((i0 : ℝ) - i) * ((i0 : ℝ) - i - 1)) ≤ logb q N i := by
  have := seq_taylor_left_ge (logb q N) cbar i0 (i0 - i) (by omega) fun k hk1 hk2 => by
    rw [scurv_logb hq0 hq1 (by omega) (by omega)]
    exact hc k (by omega) hk2
  rw [Nat.sub_sub_self hi, Nat.cast_sub hi] at this
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    simp
  · have e := logb_succ_sub hq0 hq1 (by omega : i0 - 1 < N)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ i0)] at e
    rw [e] at this
    linarith

/-- **T1 Lemma 4.1 (ii), mirror image, from above.**  For lattice points `i ≤ i₀ ≤ N` and any
`c̲ ≤ c_N(k)` for `i < k < i₀`:
`log b_N(i) ≤ log b_N(i₀) − (i₀ − i)Δ(i₀ − 1) − (c̲/2)(i₀ − i)(i₀ − i − 1)`. -/
theorem logb_taylor_left_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N i0 i : ℕ} (hi : i ≤ i0)
    (hiN : i0 ≤ N) (cund : ℝ) (hc : ∀ k, i < k → k < i0 → cund ≤ curvN N k) :
    logb q N i ≤ logb q N i0 - ((i0 : ℝ) - i) * logIncr q N (i0 - 1) -
        cund / 2 * (((i0 : ℝ) - i) * ((i0 : ℝ) - i - 1)) := by
  have := seq_taylor_left_le (logb q N) cund i0 (i0 - i) (by omega) fun k hk1 hk2 => by
    rw [scurv_logb hq0 hq1 (by omega) (by omega)]
    exact hc k (by omega) hk2
  rw [Nat.sub_sub_self hi, Nat.cast_sub hi] at this
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    simp
  · have e := logb_succ_sub hq0 hq1 (by omega : i0 - 1 < N)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ i0)] at e
    rw [e] at this
    linarith

end Erdos993Lean.Analytic.NoValley
