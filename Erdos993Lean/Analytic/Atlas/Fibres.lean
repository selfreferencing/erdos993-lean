import Mathlib
import Erdos993Lean.Analytic.Atlas.Atoms

/-!
# The O4 atlas (lane A9): fibres, the tail `M ≥ N`, and the tail prices

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  Sources: Soul's `SOUL/O4/ATLAS_PROOF.md`
and `SOUL/O4/PARAMETER_BOX_PROOF.md`; the checker `Erdos993Lean/Analytic/Atlas/Checker.lean`.

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* `ZRowInv` (the integer binomial row `r^M b_M(j; p/r)`), `zRowInv_zero`, `zRowInv_step`,
  `bval_binomFn`.
* `FibreGood b M`: the pointwise bound (B) of the box `b` at the fibre `M` for every `q ∈ [ql, qh]`
  and every integer `j`.
* `atomAt_sound`, `atomsFrom_sound`; `kappa_ge_kapB` (`κ ≥ −B`: the Fourier bound for `vmin·M ≥ 25`,
  else `|κ| ≤ 1/(q(1 − q))`), `skip_sound` (completing the square), `jloOf_spec`, `jhiOf_spec`.
* `fibreOK_sound` (all integers `j`: half-lines outside `[−1, M + 1]`, skipped atoms, checked atoms),
  `fibresLoop_sound`, `tailOK_sound` (every `M ≥ N`, by the Fourier bound `κ ≥ −(1/(20u) + 1/u²)`,
  `u = Mq(1 − q) ≥ 25`, and monotonicity of `π`), **`box_pointwise`**: a box passing `sane`,
  `tailOK` and `fibresAll` satisfies (B) at every fibre.
* `sumList_drop_eq`, `costFrom_eq`, `sum_range_extend`, `sum_range_diff`, **`abel_tail`** (the Abel
  identity of the tail prices), `tailHat_ge`, `uList_getD`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.Atlas

/-! ## Sound: the tail `M ≥ N` -/

theorem sumList_nonneg {l : List ℚ} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ sumList l := by
  induction l with
  | nil => exact le_refl 0
  | cons x xs ih =>
    simp only [sumList]
    have := h x (List.mem_cons_self ..)
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    linarith

theorem Box.tailSum_nonneg {b : Box} (hz : ∀ x ∈ b.z, 0 ≤ x) (M : ℕ) : 0 ≤ b.tailSum M :=
  sumList_nonneg fun x hx => hz x (List.mem_of_mem_drop hx)

theorem Box.piQ_cast (b : Box) (M : ℕ) :
    ((b.piQ M : ℚ) : ℝ) = (b.alpha : ℝ) + (b.beta : ℝ) * ((M : ℝ) - (b.m0 : ℝ)) -
      (b.gamma : ℝ) * ((M : ℝ) - (b.m0 : ℝ)) ^ 2 := by
  unfold Box.piQ; push_cast; ring

theorem vmin_le {ql qh : ℚ} {q : ℝ} (hq : (ql : ℝ) ≤ q) (hq' : q ≤ qh) :
    ((qmin (ql * (1 - ql)) (qh * (1 - qh)) : ℚ) : ℝ) ≤ q * (1 - q) := by
  simp only [qmin_cast]
  push_cast
  rcases le_total (q + ql) 1 with h | h
  · exact (min_le_left _ _).trans (by nlinarith)
  · rcases le_total (q + qh) 1 with h' | h'
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact (min_le_right _ _).trans (by nlinarith)

/-! ## Fibres: integer rows -/

/-- The integer row invariant: `row.getD j = r^M b_M(j; q)`, `rM = r^M` (`q = p/r`, `r = q.den`). -/
def ZRowInv (q : ℚ) (M : ℕ) (row : Array ℕ) (rM : ℕ) : Prop :=
  row.size = M + 1 ∧ rM = (zq q).r ^ M ∧
    ∀ j : ℕ, ((row.getD j 0 : ℕ) : ℝ) = binom M (q : ℝ) j * ((zq q).r : ℝ) ^ M

theorem zRowInv_zero (q : ℚ) : ZRowInv q 0 #[1] 1 := by
  refine ⟨rfl, by simp, fun j => ?_⟩
  rcases j with _ | j
  · rw [binom_natCast_of_le _ (le_refl 0)]
    simp
  · rw [binom_natCast_of_lt _ (by omega : 0 < j + 1)]
    simp

theorem zq_p_eq {q : ℚ} (hq0 : 0 ≤ q) : (((zq q).p : ℕ) : ℝ) = (q : ℝ) * ((zq q).r : ℝ) := by
  unfold zq
  simp only
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have e : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
  rw [e]
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  rw [hq]
  have : (q.den : ℝ) ≠ 0 := by positivity
  field_simp

theorem zq_s_eq {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (((zq q).s : ℕ) : ℝ) = (1 - (q : ℝ)) * ((zq q).r : ℝ) := by
  have hp := zq_p_eq hq0
  unfold zq at hp ⊢
  simp only at hp ⊢
  have hle : q.num.toNat ≤ q.den := by
    have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
    have hd : (0 : ℝ) < q.den := by positivity
    have : ((q.num.toNat : ℕ) : ℝ) ≤ (q.den : ℝ) := by rw [hp]; nlinarith
    exact_mod_cast this
  rw [Nat.cast_sub hle, hp]
  ring

theorem zRowInv_step {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {M : ℕ} {row : Array ℕ} {rM : ℕ}
    (h : ZRowInv q M row rM) : ZRowInv q (M + 1) (zrowStep (zq q) row) (rM * (zq q).r) := by
  obtain ⟨hs, hr, hv⟩ := h
  refine ⟨by simp [zrowStep, hs], by rw [hr, pow_succ], fun j => ?_⟩
  have hp := zq_p_eq hq0
  have hsq := zq_s_eq hq0 hq1
  unfold zrowStep
  rw [getD_ofFn, binom_pascal]
  by_cases h1 : j < row.size + 1
  · rw [dif_pos h1]
    dsimp only
    by_cases h2 : j = 0
    · subst h2
      rw [if_pos rfl]
      simp only [Nat.cast_zero, zero_sub, mul_zero, add_zero]
      push_cast
      rw [hv 0, hsq, binom_of_neg (by norm_num : (-1 : ℤ) < 0)]
      simp only [Nat.cast_zero]
      ring
    · rw [if_neg h2]
      push_cast
      rw [hv j, hv (j - 1), hsq, hp, show (((j - 1 : ℕ) : ℤ)) = (j : ℤ) - 1 by omega]
      ring
  · rw [dif_neg h1]
    rw [hs] at h1
    rw [binom_natCast_of_lt _ (by omega : M < j),
      show (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) by omega, binom_natCast_of_lt _ (by omega : M < j - 1)]
    simp

theorem bval_binomFn {q : ℚ} {M : ℕ} {row : Array ℕ} {rM : ℕ} (h : ZRowInv q M row rM) :
    BinomFn q M (bval row rM) := by
  intro j
  obtain ⟨-, hr, hv⟩ := h
  have hd : (0 : ℝ) < ((zq q).r : ℝ) := by unfold zq; simp only; exact_mod_cast q.den_pos
  unfold bval
  push_cast
  rw [hv j, hr]
  push_cast
  field_simp

/-! ## Fibres: the atoms, the skip bound -/

/-- **The pointwise fibre bound (B)** of a box at the fibre `M`: for every `q ∈ [ql, qh]` and every
integer `j`, `rhs(M) ≤ κ_q(M, j) + c(j − qM) + μ(j − qM)²`. -/
def FibreGood (b : Box) (M : ℕ) : Prop :=
  ∀ q : ℝ, (b.ql : ℝ) ≤ q → q ≤ b.qh → ∀ j : ℤ,
    ((b.rhs M : ℚ) : ℝ) ≤ kappa q M j + (b.c : ℝ) * ((j : ℝ) - q * M) +
      (b.mu : ℝ) * ((j : ℝ) - q * M) ^ 2

theorem atomAt_sound {b : Box} {M : ℕ} {fl f0 fh : ℕ → ℚ} {pas : Array ℕ}
    (hfl : BinomFn b.ql M fl) (hf0 : BinomFn b.q0 M f0) (hfh : BinomFn b.qh M fh) (hpas : PasInv M pas)
    (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (h1 : (b.qh : ℝ) < 1) (hmu : 0 < b.mu)
    {rhs : ℚ} {j : ℤ} (hj : -1 ≤ j) (hj' : j ≤ (M : ℤ) + 1)
    (hok : atomAt b M fl f0 fh pas rhs j = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kappa q M j + (b.c : ℝ) * ((j : ℝ) - q * M) + (b.mu : ℝ) * ((j : ℝ) - q * M) ^ 2 := by
  unfold atomAt at hok
  split_ifs at hok with ha hb
  · subst ha
    exact atomNeg_sound h1 hlh hmu hok hq hq'
  · rw [hb]
    exact atomTop_sound h0 hlh hmu hok hq hq'
  · have hj0 : 0 ≤ j := by omega
    have hjM : j.toNat ≤ M := by omega
    have e : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have := atomMid_sound hjM hfl hf0 hfh hpas h0 hlh h1 hmu hok hq hq'
    rwa [e] at this

theorem atomsFrom_sound {b : Box} {M : ℕ} {fl f0 fh : ℕ → ℚ} {pas : Array ℕ} {rhs : ℚ} :
    ∀ (k : ℕ) (lo : ℤ), atomsFrom b M fl f0 fh pas rhs lo k = true →
      ∀ j : ℤ, lo ≤ j → j < lo + k → atomAt b M fl f0 fh pas rhs j = true := by
  intro k
  induction k with
  | zero => intro lo _ j h1 h2; push_cast at h2; omega
  | succ k ih =>
    intro lo h j h1 h2
    unfold atomsFrom at h
    simp only [Bool.and_eq_true] at h
    rcases eq_or_lt_of_le h1 with he | hlt
    · rw [← he]; exact h.1
    · exact ih (lo + 1) h.2 j (by omega) (by push_cast at h2 ⊢; omega)

/-- `κ ≥ −B` with the checker's `kapB`: the Fourier bound for `vmin·M ≥ 25`, else `|κ| ≤ 1/vmin`. -/
theorem kappa_ge_kapB {b : Box} (h0 : (0 : ℝ) < b.ql) (h1 : (b.qh : ℝ) < 1) (M : ℕ) {q : ℝ}
    (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) (j : ℤ) : -((kapB b M : ℚ) : ℝ) ≤ kappa q M j := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hvq := vmin_le (ql := b.ql) (qh := b.qh) hq hq'
  set v0 : ℝ := ((qmin (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh)) : ℚ) : ℝ) with hv0
  have hv0pos : 0 < v0 := by
    rw [hv0, qmin_cast]; push_cast
    have : (0 : ℝ) < b.ql * (1 - b.ql) := by nlinarith
    have : (0 : ℝ) < b.qh * (1 - b.qh) := by nlinarith
    exact lt_min ‹_› ‹_›
  unfold kapB
  split_ifs with h
  · have hu0 : (25 : ℝ) ≤ v0 * (M : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h; push_cast at this; rw [hv0]; exact_mod_cast this
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have huM : v0 * (M : ℝ) ≤ (M : ℝ) * (q * (1 - q)) := by nlinarith
    have hK := kappa_ge_fourier hq0 hq1 (M := M) (by linarith) j
    have hu0p : 0 < v0 * (M : ℝ) := by linarith
    have hup : 0 < (M : ℝ) * (q * (1 - q)) := by linarith
    have hE : 1 / (20 * ((M : ℝ) * (q * (1 - q)))) + 1 / (((M : ℝ) * (q * (1 - q))) * ((M : ℝ) * (q * (1 - q)))) ≤
        1 / (20 * (v0 * (M : ℝ))) + 1 / ((v0 * (M : ℝ)) * (v0 * (M : ℝ))) := by
      gcongr
    push_cast
    rw [← hv0]
    linarith
  · have hab := NoValley.abs_kappa_le hq0 hq1 M j
    have hq1' : 0 < 1 - q := by linarith
    have e : 1 / q + 1 / (1 - q) = 1 / (q * (1 - q)) := by field_simp; ring
    have hle : 1 / (q * (1 - q)) ≤ 1 / v0 := one_div_le_one_div_of_le hv0pos hvq
    have := neg_abs_le (kappa q M j)
    push_cast
    rw [← hv0]
    linarith

/-- **The skip bound**: `κ ≥ −B` and `μ(δ − vtx)² ≥ rhs + B + c²/(4μ)` give the atom. -/
theorem skip_sound {b : Box} (hmu : 0 < b.mu) {M : ℕ} {q : ℝ} {j : ℤ} {rhs B : ℚ}
    (hκ : -((B : ℚ) : ℝ) ≤ kappa q M j)
    (hlev : ((rhs + B + b.c * b.c / (4 * b.mu) : ℚ) : ℝ) ≤
      (b.mu : ℝ) * (((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)))) :
    (rhs : ℝ) ≤ kappa q M j + (b.c : ℝ) * ((j : ℝ) - q * M) + (b.mu : ℝ) * ((j : ℝ) - q * M) ^ 2 := by
  have hmuR : (0 : ℝ) < b.mu := by exact_mod_cast hmu
  have hv : ((vtx b : ℚ) : ℝ) = -(b.c : ℝ) / (2 * (b.mu : ℝ)) := by unfold vtx; push_cast; ring
  rw [hv] at hlev
  push_cast at hlev
  have e : (b.mu : ℝ) * (((j : ℝ) - q * M - -(b.c : ℝ) / (2 * (b.mu : ℝ))) *
      ((j : ℝ) - q * M - -(b.c : ℝ) / (2 * (b.mu : ℝ)))) =
      (b.c : ℝ) * ((j : ℝ) - q * M) + (b.mu : ℝ) * ((j : ℝ) - q * M) ^ 2 +
        (b.c : ℝ) * (b.c : ℝ) / (4 * (b.mu : ℝ)) := by
    field_simp; ring
  rw [e] at hlev
  linarith

theorem jloOf_spec {b : Box} {M : ℕ} {lev : ℚ} {j : ℤ} (hj : -1 ≤ j) (hlt : j < jloOf b M lev) :
    ∃ jlo : ℤ, j < jlo ∧ 0 ≤ leftY b M jlo ∧ lev ≤ b.mu * (leftY b M jlo * leftY b M jlo) := by
  unfold jloOf at hlt
  simp only at hlt
  split_ifs at hlt with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, by omega, h.1, h.2⟩
  · omega

theorem jhiOf_spec {b : Box} {M : ℕ} {lev : ℚ} {j : ℤ} (hj : j ≤ (M : ℤ) + 1) (hlt : jhiOf b M lev < j) :
    ∃ jhi : ℤ, jhi < j ∧ 0 ≤ rightY b M jhi ∧ lev ≤ b.mu * (rightY b M jhi * rightY b M jhi) := by
  unfold jhiOf at hlt
  simp only at hlt
  split_ifs at hlt with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, by omega, h.1, h.2⟩
  · omega

theorem fibreOK_sound {b : Box} {M : ℕ} {fl f0 fh : ℕ → ℚ} {pas : Array ℕ}
    (hfl : BinomFn b.ql M fl) (hf0 : BinomFn b.q0 M f0) (hfh : BinomFn b.qh M fh) (hpas : PasInv M pas)
    (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (h1 : (b.qh : ℝ) < 1) (hmu : 0 < b.mu)
    (hok : fibreOK b M fl f0 fh pas = true) : FibreGood b M := by
  unfold fibreOK at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hL, hRt⟩, hrest⟩ := hok
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hmuR : (0 : ℝ) < b.mu := by exact_mod_cast hmu
  intro q hq hq' j
  rcases lt_or_ge j (-1) with hj | hj
  · rw [NoValley.kappa_of_lt hj, zero_add]
    have hjr : (j : ℝ) ≤ -2 := by exact_mod_cast (by omega : j ≤ -2)
    have hQ := quadMinLeft_le (mu := b.mu) (c := b.c) (a := -2 - b.ql * (M : ℚ)) hmu
      (x := (j : ℝ) - q * M) (by push_cast; nlinarith)
    have hL' : ((b.rhs M : ℚ) : ℝ) ≤ ((quadMinLeft b.mu b.c (-2 - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hL
    nlinarith [hQ, hL']
  rcases lt_or_ge ((M : ℤ) + 1) j with hj2 | hj2
  · rw [NoValley.kappa_of_gt hj2, zero_add]
    have hjr : (M : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast (by omega : (M : ℤ) + 2 ≤ j)
    have hQ := quadMinRight_le (mu := b.mu) (c := b.c) (a := (M : ℚ) + 2 - b.qh * (M : ℚ)) hmu
      (x := (j : ℝ) - q * M) (by push_cast; nlinarith)
    have hR' : ((b.rhs M : ℚ) : ℝ) ≤ ((quadMinRight b.mu b.c ((M : ℚ) + 2 - b.qh * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hRt
    nlinarith [hQ, hR']
  have hκ := kappa_ge_kapB h0 h1 M hq hq' j
  have hsq : 0 ≤ ((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)) :=
    mul_self_nonneg _
  rcases hrest with hlev | hatoms
  · refine skip_sound hmu hκ ?_
    have := (Rat.cast_le (K := ℝ)).mpr hlev
    unfold skipLev at this
    push_cast at this ⊢
    nlinarith
  · by_cases hjl : j < jloOf b M (skipLev b M (b.rhs M))
    · obtain ⟨jlo, hjlo, hY0, hY⟩ := jloOf_spec hj hjl
      refine skip_sound hmu hκ ?_
      have hY0' : (0 : ℝ) ≤ ((leftY b M jlo : ℚ) : ℝ) := by exact_mod_cast hY0
      have hY' := (Rat.cast_le (K := ℝ)).mpr hY
      unfold skipLev at hY'
      have hLY : ((leftY b M jlo : ℚ) : ℝ) = (b.ql : ℝ) * M + ((vtx b : ℚ) : ℝ) - ((jlo : ℝ) - 1) := by
        unfold leftY; push_cast; ring
      have hjj : (j : ℝ) ≤ (jlo : ℝ) - 1 := by exact_mod_cast (by omega : j ≤ jlo - 1)
      have hd : (j : ℝ) - q * M - ((vtx b : ℚ) : ℝ) ≤ -((leftY b M jlo : ℚ) : ℝ) := by
        rw [hLY]; nlinarith
      have hsq2 : ((leftY b M jlo : ℚ) : ℝ) * ((leftY b M jlo : ℚ) : ℝ) ≤
          ((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)) := by
        nlinarith
      push_cast at hY' ⊢
      nlinarith [mul_le_mul_of_nonneg_left hsq2 hmuR.le]
    by_cases hjh : jhiOf b M (skipLev b M (b.rhs M)) < j
    · obtain ⟨jhi, hjhi, hY0, hY⟩ := jhiOf_spec hj2 hjh
      refine skip_sound hmu hκ ?_
      have hY0' : (0 : ℝ) ≤ ((rightY b M jhi : ℚ) : ℝ) := by exact_mod_cast hY0
      have hY' := (Rat.cast_le (K := ℝ)).mpr hY
      unfold skipLev at hY'
      have hRY : ((rightY b M jhi : ℚ) : ℝ) = ((jhi : ℝ) + 1) - (b.qh : ℝ) * M - ((vtx b : ℚ) : ℝ) := by
        unfold rightY; push_cast; ring
      have hjj : (jhi : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : jhi + 1 ≤ j)
      have hd : ((rightY b M jhi : ℚ) : ℝ) ≤ (j : ℝ) - q * M - ((vtx b : ℚ) : ℝ) := by
        rw [hRY]; nlinarith
      have hsq2 : ((rightY b M jhi : ℚ) : ℝ) * ((rightY b M jhi : ℚ) : ℝ) ≤
          ((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((vtx b : ℚ) : ℝ)) := by
        nlinarith
      push_cast at hY' ⊢
      nlinarith [mul_le_mul_of_nonneg_left hsq2 hmuR.le]
    · push_neg at hjl hjh
      have hat := atomsFrom_sound _ _ hatoms j hjl (by
        have : jhiOf b M (skipLev b M (b.rhs M)) - jloOf b M (skipLev b M (b.rhs M)) + 1 ≥ 0 := by omega
        rw [Int.toNat_of_nonneg this]; omega)
      exact atomAt_sound hfl hf0 hfh hpas h0 hlh h1 hmu hj hj2 hat hq hq'

/-- The loop over the fibres (integer rows at `ql, q0, qh`). -/
theorem fibresLoop_sound {b : Box} (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh)
    (h1 : (b.qh : ℝ) < 1) (hmu : 0 < b.mu) :
    ∀ (k M : ℕ) (rl r0 rh : Array ℕ) (rlM r0M rhM : ℕ) (pas : Array ℕ),
      ZRowInv b.ql M rl rlM → ZRowInv b.q0 M r0 r0M → ZRowInv b.qh M rh rhM → PasInv M pas →
      fibresLoop b (zq b.ql) (zq b.q0) (zq b.qh) k M rl r0 rh rlM r0M rhM pas = true →
        ∀ M', M ≤ M' → M' < M + k → FibreGood b M' := by
  have hl0 : (0 : ℚ) ≤ b.ql := by exact_mod_cast h0.le
  have hl1 : b.ql ≤ 1 := by exact_mod_cast (by linarith : (b.ql : ℝ) ≤ 1)
  have hh0 : (0 : ℚ) ≤ b.qh := by exact_mod_cast (by linarith : (0 : ℝ) ≤ b.qh)
  have hh1 : b.qh ≤ 1 := by exact_mod_cast h1.le
  have hq00 : (0 : ℚ) ≤ b.q0 := by unfold Box.q0; linarith
  have hq01 : b.q0 ≤ 1 := by unfold Box.q0; linarith
  intro k
  induction k with
  | zero => intro M _ _ _ _ _ _ _ _ _ _ _ _ M' h1' h2'; omega
  | succ k ih =>
    intro M rl r0 rh rlM r0M rhM pas hrl hr0 hrh hpas hok M' hM1 hM2
    unfold fibresLoop at hok
    simp only [Bool.and_eq_true] at hok
    rcases eq_or_lt_of_le hM1 with he | hlt
    · subst he
      exact fibreOK_sound (bval_binomFn hrl) (bval_binomFn hr0) (bval_binomFn hrh) hpas h0 hlh h1 hmu
        hok.1
    · exact ih (M + 1) _ _ _ _ _ _ _ (zRowInv_step hl0 hl1 hrl) (zRowInv_step hq00 hq01 hr0)
        (zRowInv_step hh0 hh1 hrh) (pasInv_step hpas) hok.2 M' (by omega) (by omega)

/-- **The fibres `M ≥ N`** (Fourier bound for `u ≥ 25` and monotonicity). -/
theorem tailOK_sound {b : Box} (h0 : (0 : ℝ) < b.ql) (h1 : (b.qh : ℝ) < 1) (hmu : 0 < b.mu)
    (hga : 0 < b.gamma) (hz : ∀ x ∈ b.z, 0 ≤ x) (hok : tailOK b = true) :
    ∀ M, b.N ≤ M → FibreGood b M := by
  unfold tailOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hu, hpi⟩, hbeta⟩ := hok
  intro M hNM q hq hq' j
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  set v0 : ℝ := ((b.vmin : ℚ) : ℝ) with hv0
  have hvq : v0 ≤ q * (1 - q) := vmin_le hq hq'
  have hu0 : (25 : ℝ) ≤ v0 * (b.N : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hu; push_cast at this; exact this
  have hNM' : (b.N : ℝ) ≤ M := by exact_mod_cast hNM
  have hv0pos : 0 < v0 := by
    by_contra hc; push_neg at hc
    nlinarith [Nat.cast_nonneg (α := ℝ) b.N]
  have huM : v0 * (b.N : ℝ) ≤ (M : ℝ) * (q * (1 - q)) := by
    have := mul_le_mul hNM' hvq hv0pos.le (Nat.cast_nonneg M)
    linarith
  have hK := kappa_ge_fourier hq0 hq1 (M := M) (by linarith) j
  set u := (M : ℝ) * (q * (1 - q))
  set u0 := v0 * (b.N : ℝ)
  have hE : 1 / (20 * u) + 1 / (u * u) ≤ 1 / (20 * u0) + 1 / (u0 * u0) := by
    have hu0p : 0 < u0 := by linarith
    have hup : 0 < u := by linarith
    gcongr
  have hquad := NoValley.quad_lower_bound (ν := (b.mu : ℝ)) (by exact_mod_cast hmu) (b.c : ℝ)
    ((j : ℝ) - q * M)
  have hpiN : ((b.piQ b.N : ℚ) : ℝ) ≤
      -(1 / (20 * u0) + 1 / (u0 * u0)) - (b.c : ℝ) * (b.c : ℝ) / (4 * (b.mu : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hpi; push_cast at this; exact this
  have hmono : ((b.piQ M : ℚ) : ℝ) ≤ ((b.piQ b.N : ℚ) : ℝ) := by
    rw [Box.piQ_cast, Box.piQ_cast]
    have hb' : ((b.beta - 2 * b.gamma * ((b.N : ℚ) - b.m0) : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hbeta
    push_cast at hb'
    have hg : (0 : ℝ) ≤ b.gamma := by exact_mod_cast hga.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hNM') hg, mul_nonneg (sub_nonneg.mpr hNM') (sub_nonneg.mpr hNM')]
  have hts : (0 : ℝ) ≤ ((b.tailSum M : ℚ) : ℝ) := by exact_mod_cast Box.tailSum_nonneg hz M
  have hrhs : ((b.rhs M : ℚ) : ℝ) = ((b.piQ M : ℚ) : ℝ) - ((b.tailSum M : ℚ) : ℝ) := by
    unfold Box.rhs; push_cast; ring
  have hc2 : -(b.c : ℝ) ^ 2 / (4 * (b.mu : ℝ)) = -((b.c : ℝ) * (b.c : ℝ) / (4 * (b.mu : ℝ))) := by ring
  rw [hc2] at hquad
  rw [hrhs]
  linarith

/-- **The pointwise bound (B) at every fibre** of a box passing `sane`, `tailOK` and `fibresAll`. -/
theorem box_pointwise {b : Box} (hs : sane b = true) (ht : tailOK b = true) (hf : fibresAll b = true) :
    ∀ M, FibreGood b M := by
  unfold sane at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, hlh⟩, h1⟩, hmu⟩, hga⟩, hz⟩, -⟩, -⟩, -⟩ := hs
  have h0' : (0 : ℝ) < b.ql := by exact_mod_cast h0
  have hlh' : (b.ql : ℝ) ≤ b.qh := by exact_mod_cast hlh.le
  have h1' : (b.qh : ℝ) < 1 := by exact_mod_cast h1
  intro M
  rcases lt_or_ge M b.N with hMN | hMN
  · exact fibresLoop_sound h0' hlh' h1' hmu b.N 0 _ _ _ _ _ _ _ (zRowInv_zero _) (zRowInv_zero _)
      (zRowInv_zero _) pasInv_zero hf M (Nat.zero_le _) (by omega)
  · exact tailOK_sound h0' h1' hmu hga hz ht M hMN

/-! ## Sound: sums over the dual's tail prices -/

theorem sumList_drop_eq (l : List ℚ) (M : ℕ) :
    sumList (l.drop M) = ∑ i ∈ Finset.range l.length, if M ≤ i then l.getD i 0 else 0 := by
  induction l generalizing M with
  | nil => simp [sumList]
  | cons x xs ih =>
    rcases M with _ | M
    · simp only [List.drop_zero, sumList, List.length_cons, Finset.sum_range_succ', zero_le,
        if_true, List.getD_cons_succ, List.getD_cons_zero]
      have := ih 0
      simp only [List.drop_zero, zero_le, if_true] at this
      rw [this]
      ring
    · simp only [List.drop_succ_cons, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ]
      rw [ih M]
      simp

theorem costFrom_eq (U : List ℚ) (Λ : ℚ) (cm : ℕ) : ∀ (zs : List ℚ) (r0 : ℕ),
    costFrom U Λ cm r0 zs = ∑ i ∈ Finset.range zs.length,
      zs.getD i 0 * (if r0 + i ≤ cm then tailHat U Λ (r0 + i) else 1) := by
  intro zs
  induction zs with
  | nil => intro r0; simp [costFrom]
  | cons x xs ih =>
    intro r0
    simp only [costFrom, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, add_zero]
    rw [ih (r0 + 1)]
    have : ∀ i, r0 + 1 + i = r0 + (i + 1) := fun i => by ring
    simp only [this]
    ring

theorem sum_range_extend (l : List ℚ) (f : ℕ → ℚ) {K : ℕ} (hK : l.length ≤ K) :
    ∑ i ∈ Finset.range l.length, l.getD i 0 * f i = ∑ i ∈ Finset.range K, l.getD i 0 * f i := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr hK) fun i _ hi => ?_
  rw [Finset.mem_range, not_lt] at hi
  rw [List.getD_eq_default _ _ hi, zero_mul]

/-- Telescoping: `∑_{i ≤ n} (T i − T(i − 1)) = T n` with `T(−1) = 0`. -/
theorem sum_range_diff (T : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (T i - if i = 0 then 0 else T (i - 1)) = T n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
    ring

/-- **The Abel identity of the tail prices**: with `S(M') = tl(M') − tl(n)` and `tl(M) = z_M + tl(M + 1)`,
`∑_{M' < n} S(M') (T(M') − T(M' − 1)) = ∑_{r < n} z_r T(r)`. -/
theorem abel_tail (z tl T : ℕ → ℝ) (htl : ∀ M, tl M = z M + tl (M + 1)) (n : ℕ) :
    ∑ M' ∈ Finset.range n, (tl M' - tl n) * (T M' - if M' = 0 then 0 else T (M' - 1)) =
      ∑ r ∈ Finset.range n, z r * T r := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∀ M', tl M' - tl (n + 1) = (tl M' - tl n) + z n := fun M' => by rw [htl n]; ring
    simp only [e, add_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, sum_range_diff T n, Finset.sum_range_succ, ih, sub_self, zero_mul, add_zero,
      Finset.sum_range_succ]

/-! ## Sound: the tail bound `T̂` -/

theorem tailHat_ge {U : List ℚ} {Λ : ℚ} {r : ℕ} {t : ℝ} (h1 : t ≤ 1)
    (hk : ∀ k < 5, t ≤ ((U.getD k 0 * ((1 + Λ) / (1 + Λ * tvals.getD k 0)) ^ r : ℚ) : ℝ)) :
    t ≤ ((tailHat U Λ r : ℚ) : ℝ) := by
  unfold tailHat
  have key : ∀ (l : List ℕ) (acc : ℚ), (∀ k ∈ l, k < 5) → t ≤ (acc : ℝ) →
      t ≤ ((l.foldl (fun acc k => qmin acc (U.getD k 0 * ((1 + Λ) / (1 + Λ * tvals.getD k 0)) ^ r)) acc
        : ℚ) : ℝ) := by
    intro l
    induction l with
    | nil => intro acc _ h; simpa using h
    | cons k ks ih =>
      intro acc hl h
      simp only [List.foldl_cons]
      refine ih _ (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')) ?_
      rw [qmin_cast]
      exact le_min h (hk k (hl k List.mem_cons_self))
  exact key _ 1 (fun k hk => List.mem_range.mp hk) (by simpa using h1)

theorem uList_getD (band : Band) (ml : ℚ) {k : ℕ} (hk : k < 5) :
    (uList band ml).getD k 0 = expNegUpper (band.ell.getD k 0 * ml) := by
  unfold uList
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

end Erdos993Lean.Analytic.Atlas
