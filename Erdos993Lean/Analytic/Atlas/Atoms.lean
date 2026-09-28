import Mathlib
import Erdos993Lean.Analytic.Atlas.Taylor
import Erdos993Lean.Analytic.Atlas.Bounds

/-!
# The O4 atlas (lane A9): what the atom checks mean

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  The checker is
`Erdos993Lean/Analytic/Atlas/Checker.lean` (exact rational arithmetic, core Lean only); this file proves,
for arbitrary data, what its per-atom Booleans mean, from the analytic bounds of `Atlas/Kernel.lean`
and `Atlas/Bounds.lean` (Soul's `SOUL/O4/ATLAS_PROOF.md`, first-order q-uniform bound).

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* `qabs_cast`, `qmax_cast`, `qmin_cast`, `sumList_eq`: the rational helpers.
* `binom_pascal`; `BinomFn` (a function giving the binomial point masses at `q`), the Pascal invariant
  `PasInv` preserved by `pascalStep` (`pasInv_step`); `kapRow_cast`.
* `pabs_bound`, `dpabs_bound`, `labs_bound`, `wmax_bound`: the checker's `|P|_max`, `|P'|_max`,
  `|L|_max`, `W_max` bound the real functions on `[ql, qh]`.
* `joint_cast`, `lpabs_cast`: the second-order alternative.
* **`atomMid_sound`, `atomNeg_sound`, `atomTop_sound`**: a passing atom `(M, j)`,
  `−1 ≤ j ≤ M + 1` (by the first-order bound of `Atlas/Kernel.lean` or the second-order bound of
  `Atlas/Taylor.lean`), gives the pointwise bound (B) `rhs ≤ κ_q(M, j) + c(j − qM) + μ(j − qM)²` for every
  `q ∈ [ql, qh]`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.Atlas

/-! ## Sound: rational helpers -/

@[simp] theorem qabs_cast (x : ℚ) : ((qabs x : ℚ) : ℝ) = |(x : ℝ)| := by
  unfold qabs
  split_ifs with h
  · have : (x : ℝ) < 0 := by exact_mod_cast h
    rw [abs_of_neg this]
    push_cast
    ring
  · push_neg at h
    have : (0 : ℝ) ≤ x := by exact_mod_cast h
    rw [abs_of_nonneg this]

@[simp] theorem qmax_cast (a b : ℚ) : ((qmax a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  unfold qmax
  split_ifs with h
  · rw [max_eq_right (by exact_mod_cast h)]
  · push_neg at h
    rw [max_eq_left (by exact_mod_cast h.le)]

@[simp] theorem qmin_cast (a b : ℚ) : ((qmin a b : ℚ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  unfold qmin
  split_ifs with h
  · rw [min_eq_left (by exact_mod_cast h)]
  · push_neg at h
    rw [min_eq_right (by exact_mod_cast h.le)]

theorem sumList_eq (l : List ℚ) : sumList l = l.sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sumList, ih]

/-! ## Sound: binomial rows -/

/-- Pascal's rule for the point masses: `b_{M+1}(j) = (1 − q) b_M(j) + q b_M(j − 1)`. -/
theorem binom_pascal (M : ℕ) (q : ℝ) (j : ℤ) :
    binom (M + 1) q j = (1 - q) * binom M q j + q * binom M q (j - 1) := by
  have h1 := binom_step_right M q j
  have h2 := binom_step_left M q j
  have hM : (M : ℝ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hM
  linear_combination -h1 - h2

theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (j : ℕ) (d : α) :
    (Array.ofFn f).getD j d = if h : j < n then f ⟨j, h⟩ else d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split_ifs <;> simp_all

/-- `f` gives the binomial point masses `b_M(j; q)`. -/
def BinomFn (q : ℚ) (M : ℕ) (f : ℕ → ℚ) : Prop := ∀ j : ℕ, ((f j : ℚ) : ℝ) = binom M (q : ℝ) j

/-- The Pascal invariant: `pas = (C(M, j))_j` with `pas.size = M + 1`. -/
def PasInv (M : ℕ) (pas : Array ℕ) : Prop :=
  pas.size = M + 1 ∧ ∀ j : ℕ, pas.getD j 0 = M.choose j

theorem pasInv_zero : PasInv 0 #[1] := by
  refine ⟨rfl, fun j => ?_⟩
  rcases j with _ | j <;> simp

theorem pasInv_step {M : ℕ} {pas : Array ℕ} (h : PasInv M pas) : PasInv (M + 1) (pascalStep pas) := by
  obtain ⟨hs, hv⟩ := h
  refine ⟨by simp [pascalStep, hs], fun j => ?_⟩
  unfold pascalStep
  rw [getD_ofFn]
  by_cases h1 : j < pas.size + 1
  · rw [dif_pos h1]
    dsimp only
    by_cases h2 : j = 0
    · subst h2
      simp [hv 0]
    · rw [if_neg h2]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hv, hv, Nat.add_sub_cancel, Nat.choose_succ_succ, add_comm]
  · rw [dif_neg h1]
    rw [hs] at h1
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm

/-! ## Sound: the kernel from a row -/

theorem kapRow_cast {q : ℚ} {M j : ℕ} {f : ℕ → ℚ} (hf : BinomFn q M f) (hq0 : (0 : ℝ) < q)
    (hq1 : (q : ℝ) < 1) : ((kapRow q j f : ℚ) : ℝ) = kappa (q : ℝ) M (j : ℤ) := by
  have h0 : (q : ℝ) ≠ 0 := hq0.ne'
  have h1 : (1 : ℝ) - q ≠ 0 := by linarith
  unfold kapRow kappa
  push_cast
  rw [hf j, hf (j + 1)]
  have ep : (((j + 1 : ℕ) : ℤ)) = (j : ℤ) + 1 := by push_cast; ring
  rw [ep]
  split_ifs with hj
  · subst hj
    rw [binom_of_neg (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0)]
    field_simp
    ring
  · rw [hf (j - 1), show (((j - 1 : ℕ) : ℤ)) = (j : ℤ) - 1 by omega]
    field_simp
    ring

/-! ## Sound: the atom quantities -/

theorem coefA_cast (M j : ℕ) : ((coefA M j : ℚ) : ℝ) = coefAR M j := by
  unfold coefA coefAR; push_cast; ring

theorem coefB_cast (M j : ℕ) : ((coefB M j : ℚ) : ℝ) = coefBR M j := by
  unfold coefB coefBR; push_cast; ring

theorem pval_cast (a bb x : ℚ) : ((pval a bb x : ℚ) : ℝ) = Pf a bb x := by
  unfold pval Pf; push_cast; ring

theorem dpval_cast (a bb x : ℚ) : ((dpval a bb x : ℚ) : ℝ) = dPf a bb x := by
  unfold dpval dPf; push_cast; ring

theorem lcomb_cast (M j : ℕ) (u v : ℚ) : ((lcomb M j u v : ℚ) : ℝ) = lcombR M j u v := by
  unfold lcomb lcombR; push_cast; ring

theorem star_cast (M j : ℕ) : ((star M j : ℚ) : ℝ) = ((j : ℝ) - 1) / ((M : ℝ) - 2) := by
  unfold star; push_cast; ring

theorem pabs_bound {a bb ql qh : ℚ} {x : ℝ} (hx : (ql : ℝ) ≤ x) (hx' : x ≤ qh) :
    |Pf (a : ℝ) (bb : ℝ) x| ≤ ((pabs a bb ql qh : ℚ) : ℝ) := by
  have hl : |Pf (a : ℝ) (bb : ℝ) (ql : ℝ)| ≤ ((pabs a bb ql qh : ℚ) : ℝ) := by
    unfold pabs
    split_ifs
    · simp only [qmax_cast, qabs_cast, pval_cast]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · simp only [qmax_cast, qabs_cast, pval_cast]
      exact le_max_left _ _
  have hh : |Pf (a : ℝ) (bb : ℝ) (qh : ℝ)| ≤ ((pabs a bb ql qh : ℚ) : ℝ) := by
    unfold pabs
    split_ifs
    · simp only [qmax_cast, qabs_cast, pval_cast]
      exact (le_max_right _ _).trans (le_max_left _ _)
    · simp only [qmax_cast, qabs_cast, pval_cast]
      exact le_max_right _ _
  refine abs_Pf_le hx hx' hl hh fun hs h1 h2 => ?_
  have hs' : a + bb ≠ 0 := by
    intro h; apply hs; exact_mod_cast congrArg (fun r : ℚ => (r : ℝ)) h
  have hv : ((a / (a + bb) : ℚ) : ℝ) = (a : ℝ) / ((a : ℝ) + bb) := by push_cast; ring
  have h1' : ql < a / (a + bb) := by exact_mod_cast (hv ▸ h1)
  have h2' : a / (a + bb) < qh := by exact_mod_cast (hv ▸ h2)
  unfold pabs
  rw [if_pos ⟨hs', h1', h2'⟩]
  simp only [qmax_cast, qabs_cast, pval_cast]
  rw [hv]
  exact le_max_right _ _

theorem dpabs_bound {a bb ql qh : ℚ} {x : ℝ} (hx : (ql : ℝ) ≤ x) (hx' : x ≤ qh) :
    |dPf (a : ℝ) (bb : ℝ) x| ≤ ((dpabs a bb ql qh : ℚ) : ℝ) := by
  unfold dpabs
  simp only [qmax_cast, qabs_cast, dpval_cast]
  exact abs_dPf_le hx hx'

theorem labs_bound {M j : ℕ} {ql qh : ℚ} {x : ℝ} (h0 : (0 : ℝ) < ql) (h1 : (qh : ℝ) < 1)
    (hx : (ql : ℝ) ≤ x) (hx' : x ≤ qh) : |Lf M j x| ≤ ((labs M j ql qh : ℚ) : ℝ) := by
  unfold labs
  simp only [qmax_cast, qabs_cast, lcomb_cast]
  exact abs_Lf_le h0 h1 hx hx'

theorem wmax_bound {M j : ℕ} (hj : j ≤ M) {ql qh : ℚ} {fl fh : ℕ → ℚ} {pas : Array ℕ}
    (hfl : BinomFn ql M fl) (hfh : BinomFn qh M fh) (hpas : PasInv M pas)
    (h0 : (0 : ℝ) < ql) (h1 : (qh : ℝ) < 1) {x : ℝ} (hx : (ql : ℝ) ≤ x) (hx' : x ≤ qh) :
    Wf M j x ≤ ((wmax M j ql qh fl fh pas : ℚ) : ℝ) := by
  have hWl : Wf M j ql = ((fl j / (ql * (1 - ql)) : ℚ) : ℝ) := by
    unfold Wf; push_cast; rw [hfl j]
  have hWh : Wf M j qh = ((fh j / (qh * (1 - qh)) : ℚ) : ℝ) := by
    unfold Wf; push_cast; rw [hfh j]
  refine Wf_le_of_candidates hj h0 h1 hx hx' ?_ ?_ ?_
  · rw [hWl]
    unfold wmax
    split_ifs
    · simp only [qmax_cast]; exact (le_max_left _ _).trans (le_max_left _ _)
    · simp only [qmax_cast]; exact le_max_left _ _
  · rw [hWh]
    unfold wmax
    split_ifs
    · simp only [qmax_cast]; exact (le_max_right _ _).trans (le_max_left _ _)
    · simp only [qmax_cast]; exact le_max_right _ _
  · intro hs1 hs2
    have hsq := star_cast M j
    have hs1' : ql < star M j := by exact_mod_cast (hsq ▸ hs1)
    have hs2' : star M j < qh := by exact_mod_cast (hsq ▸ hs2)
    have hM2 : M ≠ 2 := by
      rintro rfl
      have h0q : (0 : ℚ) < ql := by exact_mod_cast h0
      have : star 2 j = 0 := by unfold star; norm_num
      rw [this] at hs1'
      linarith
    unfold wmax
    rw [if_pos ⟨hM2, hs1', hs2'⟩]
    simp only [qmax_cast]
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    rw [Wf_eq hj, hpas.2 j, ← hsq]
    push_cast
    ring

/-! ## Sound: the atoms -/

theorem Box.q0_cast (b : Box) : ((b.q0 : ℚ) : ℝ) = ((b.ql : ℝ) + b.qh) / 2 := by
  unfold Box.q0; push_cast; ring

theorem Box.rad_cast (b : Box) : ((b.rad : ℚ) : ℝ) = ((b.qh : ℝ) - b.ql) / 2 := by
  unfold Box.rad; push_cast; ring

theorem joint_cast (b : Box) (M : ℕ) (j : ℤ) (kap k1 k2 : ℚ) :
    ((joint b M j kap k1 k2 : ℚ) : ℝ) =
      (kap : ℝ) + ((b.mu : ℝ) * (((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M) *
          ((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M)) + (b.c : ℝ) * ((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M)) -
        ((b.qh : ℝ) - b.ql) / 2 * |(k1 : ℝ) - (M : ℝ) * ((b.c : ℝ) + 2 * (b.mu : ℝ) *
          ((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M))| -
        ((b.qh : ℝ) - b.ql) / 2 * (((b.qh : ℝ) - b.ql) / 2) *
          ((k2 : ℝ) + 2 * (b.mu : ℝ) * ((M : ℝ) * (M : ℝ))) / 2 := by
  unfold joint
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div, qabs_cast, Rat.cast_intCast,
    Rat.cast_natCast, Rat.cast_ofNat, Box.q0_cast, Box.rad_cast]

theorem lpabs_cast (M j : ℕ) (ql qh : ℚ) : ((lpabs M j ql qh : ℚ) : ℝ) =
    |(j : ℝ) - 1| / ((ql : ℝ) * ql) + |(M : ℝ) - (j : ℝ) - 1| / ((1 - (qh : ℝ)) * (1 - qh)) := by
  unfold lpabs
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, qabs_cast, Rat.cast_sub, Rat.cast_natCast,
    Rat.cast_one]

/-- **The atom `(M, j)`, `0 ≤ j ≤ M`, of a passing fibre** (first- or second-order bound). -/
theorem atomMid_sound {b : Box} {M j : ℕ} (hj : j ≤ M) {fl f0 fh : ℕ → ℚ} {pas : Array ℕ}
    (hfl : BinomFn b.ql M fl) (hf0 : BinomFn b.q0 M f0) (hfh : BinomFn b.qh M fh) (hpas : PasInv M pas)
    (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (h1 : (b.qh : ℝ) < 1) (hmu : 0 < b.mu)
    {rhs : ℚ} (hok : atomMid b M j fl f0 fh pas rhs = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q)
    (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kappa q M (j : ℤ) + (b.c : ℝ) * (((j : ℤ) : ℝ) - q * M) +
      (b.mu : ℝ) * (((j : ℤ) : ℝ) - q * M) ^ 2 := by
  have hq0R : ((b.q0 : ℚ) : ℝ) = ((b.ql : ℝ) + b.qh) / 2 := Box.q0_cast b
  have hkap : ((kapRow b.q0 j f0 : ℚ) : ℝ) = kappa (((b.ql : ℝ) + b.qh) / 2) M (j : ℤ) := by
    rw [kapRow_cast hf0 (by rw [hq0R]; linarith) (by rw [hq0R]; linarith), hq0R]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hW := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => wmax_bound hj hfl hfh hpas h0 h1 hx hx'
  have hP := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => by
    have := pabs_bound (a := coefA M j) (bb := coefB M j) hx hx'
    rwa [coefA_cast, coefB_cast] at this
  have hdP := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => by
    have := dpabs_bound (a := coefA M j) (bb := coefB M j) hx hx'
    rwa [coefA_cast, coefB_cast] at this
  have hL := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => labs_bound (M := M) (j := j) h0 h1 hx hx'
  unfold atomMid at hok
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with hok | hok
  · have hR : (rhs : ℝ) ≤ ((kapRow b.q0 j f0 - b.rad * (wmax M j b.ql b.qh fl fh pas *
        (dpabs (coefA M j) (coefB M j) b.ql b.qh + labs M j b.ql b.qh * pabs (coefA M j) (coefB M j) b.ql b.qh)) +
        quadMinI b.mu b.c ((j : ℚ) - b.qh * (M : ℚ)) ((j : ℚ) - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    push_cast at hR
    have hFO := kappa_ge_firstOrder hj h0 hlh h1 hq hq' hW hP hdP hL
    have hQ := quadMinI_le (mu := b.mu) (c := b.c) (lo := (j : ℚ) - b.qh * (M : ℚ))
      (hi := (j : ℚ) - b.ql * (M : ℚ)) hmu (x := ((j : ℤ) : ℝ) - q * M)
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    rw [Box.rad_cast, hkap] at hR
    push_cast at hQ ⊢
    nlinarith [hFO, hQ, hR]
  · have hR : (rhs : ℝ) ≤ ((joint b M (j : ℤ) (kapRow b.q0 j f0)
        (f0 j / (b.q0 * (1 - b.q0)) * (dpval (coefA M j) (coefB M j) b.q0 +
          lcomb M j b.q0 b.q0 * pval (coefA M j) (coefB M j) b.q0))
        (wmax M j b.ql b.qh fl fh pas * (qabs (2 * (coefA M j + coefB M j)) +
          2 * labs M j b.ql b.qh * dpabs (coefA M j) (coefB M j) b.ql b.qh +
          (labs M j b.ql b.qh * labs M j b.ql b.qh + lpabs M j b.ql b.qh) *
            pabs (coefA M j) (coefB M j) b.ql b.qh)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    rw [joint_cast, hkap] at hR
    have hk1 : ((f0 j / (b.q0 * (1 - b.q0)) * (dpval (coefA M j) (coefB M j) b.q0 +
          lcomb M j b.q0 b.q0 * pval (coefA M j) (coefB M j) b.q0) : ℚ) : ℝ) =
        k1f M j (coefAR M j) (coefBR M j) (((b.ql : ℝ) + b.qh) / 2) := by
      push_cast
      rw [hf0 j, dpval_cast, pval_cast, lcomb_cast, coefA_cast, coefB_cast, hq0R]
      unfold k1f Wf lcombR Lf
      ring
    have hk2 : ((wmax M j b.ql b.qh fl fh pas * (qabs (2 * (coefA M j + coefB M j)) +
          2 * labs M j b.ql b.qh * dpabs (coefA M j) (coefB M j) b.ql b.qh +
          (labs M j b.ql b.qh * labs M j b.ql b.qh + lpabs M j b.ql b.qh) *
            pabs (coefA M j) (coefB M j) b.ql b.qh) : ℚ) : ℝ) =
        ((wmax M j b.ql b.qh fl fh pas : ℚ) : ℝ) * (|2 * (coefAR M j + coefBR M j)| +
          2 * ((labs M j b.ql b.qh : ℚ) : ℝ) * ((dpabs (coefA M j) (coefB M j) b.ql b.qh : ℚ) : ℝ) +
          (((labs M j b.ql b.qh : ℚ) : ℝ) * ((labs M j b.ql b.qh : ℚ) : ℝ) +
            ((lpabs M j b.ql b.qh : ℚ) : ℝ)) * ((pabs (coefA M j) (coefB M j) b.ql b.qh : ℚ) : ℝ)) := by
      push_cast
      rw [qabs_cast]
      push_cast
      rw [coefA_cast, coefB_cast]
    rw [hk1, hk2] at hR
    have hLp : ∀ x, (b.ql : ℝ) ≤ x → x ≤ b.qh → |Lpf M j x| ≤ ((lpabs M j b.ql b.qh : ℚ) : ℝ) :=
      fun x hx hx' => by rw [lpabs_cast]; exact abs_Lpf_le h0 h1 hx hx'
    have hSO := kappa_ge_secondOrder hj h0 hlh h1 hq hq' (c := (b.c : ℝ)) (mu := (b.mu : ℝ))
      (by exact_mod_cast hmu.le) hW hP hdP hL hLp
    push_cast at hR ⊢
    linarith [hSO, hR]

/-- **The atom `(M, −1)` of a passing fibre.** -/
theorem atomNeg_sound {b : Box} {M : ℕ} (h1 : (b.qh : ℝ) < 1) (hlh : (b.ql : ℝ) ≤ b.qh) (hmu : 0 < b.mu)
    {rhs : ℚ} (hok : atomNeg b M rhs = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kappa q M (-1) + (b.c : ℝ) * (((-1 : ℤ) : ℝ) - q * M) +
      (b.mu : ℝ) * (((-1 : ℤ) : ℝ) - q * M) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  unfold atomNeg at hok
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with hok | hok
  · have hR : (rhs : ℝ) ≤ ((-((1 - b.q0) ^ M) - b.rad * ((M : ℚ) * (1 - b.ql) ^ (M - 1)) +
        quadMinI b.mu b.c (-1 - b.qh * (M : ℚ)) (-1 - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    push_cast at hR
    rw [Box.q0_cast, Box.rad_cast] at hR
    have hN := kappa_neg_one_ge M h1 hq hq'
    rw [kappa_neg_one (by linarith : ((b.ql : ℝ) + b.qh) / 2 < 1)] at hN
    have hQ := quadMinI_le (mu := b.mu) (c := b.c) (lo := -1 - b.qh * (M : ℚ))
      (hi := -1 - b.ql * (M : ℚ)) hmu (x := ((-1 : ℤ) : ℝ) - q * M)
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    push_cast at hQ ⊢
    nlinarith [hN, hQ, hR]
  · have hR : (rhs : ℝ) ≤ ((joint b M (-1) (-((1 - b.q0) ^ M)) ((M : ℚ) * (1 - b.q0) ^ (M - 1))
        ((M : ℚ) * ((M : ℚ) - 1) * (1 - b.ql) ^ (M - 2)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    rw [joint_cast] at hR
    push_cast at hR
    rw [Box.q0_cast] at hR
    have hSO := kappa_neg_one_ge_secondOrder M (c := (b.c : ℝ)) (mu := (b.mu : ℝ)) h1 hlh hq hq'
      (by exact_mod_cast hmu.le)
    push_cast at hSO ⊢
    linarith [hSO, hR]

/-- **The atom `(M, M + 1)` of a passing fibre.** -/
theorem atomTop_sound {b : Box} {M : ℕ} (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (hmu : 0 < b.mu)
    {rhs : ℚ} (hok : atomTop b M rhs = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kappa q M ((M : ℤ) + 1) + (b.c : ℝ) * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) +
      (b.mu : ℝ) * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  unfold atomTop at hok
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with hok | hok
  · have hR : (rhs : ℝ) ≤ ((-(b.q0 ^ M) - b.rad * ((M : ℚ) * b.qh ^ (M - 1)) +
        quadMinI b.mu b.c ((M : ℚ) + 1 - b.qh * (M : ℚ)) ((M : ℚ) + 1 - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    push_cast at hR
    rw [Box.q0_cast, Box.rad_cast] at hR
    have hT := kappa_top_ge M h0 hq hq'
    rw [kappa_top (by linarith : (0 : ℝ) < ((b.ql : ℝ) + b.qh) / 2)] at hT
    have hQ := quadMinI_le (mu := b.mu) (c := b.c) (lo := (M : ℚ) + 1 - b.qh * (M : ℚ))
      (hi := (M : ℚ) + 1 - b.ql * (M : ℚ)) hmu (x := (((M : ℤ) + 1 : ℤ) : ℝ) - q * M)
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    push_cast at hQ ⊢
    nlinarith [hT, hQ, hR]
  · have hR : (rhs : ℝ) ≤ ((joint b M ((M : ℤ) + 1) (-(b.q0 ^ M)) (-((M : ℚ) * b.q0 ^ (M - 1)))
        ((M : ℚ) * ((M : ℚ) - 1) * b.qh ^ (M - 2)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    rw [joint_cast] at hR
    push_cast at hR
    rw [Box.q0_cast] at hR
    have hSO := kappa_top_ge_secondOrder M (c := (b.c : ℝ)) (mu := (b.mu : ℝ)) h0 hlh hq hq'
      (by exact_mod_cast hmu.le)
    push_cast at hSO ⊢
    linarith [hSO, hR]

end Erdos993Lean.Analytic.Atlas
