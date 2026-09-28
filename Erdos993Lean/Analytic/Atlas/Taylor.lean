import Mathlib
import Erdos993Lean.Analytic.Atlas.Kernel

/-!
# The O4 atlas (lane A9): Soul's second-order q-uniform bound

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  Source: Soul's `SOUL/O4/ATLAS_PROOF.md`
(section "Uniform finite-atom bounds in q", second-order part: `h' = W(P' + LP) − M[c + 2μ(j − qM)]`,
`κ'' = W[P'' + 2LP' + (L² + L')P]`, `L' = −(j − 1)/q² − (M − j − 1)/(1 − q)²`, Taylor's remainder) and the
frozen upper verifier `SOUL/O4/atlas_quadratic_frozen.py`, which accepts an atom when the first-order
or the second-order bound passes (the upper atlas `m ∈ [50, 400]` needs the second one).

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* `taylor2_lower`, **`taylor2_mid`**: `f(q) ≥ f(q0) − r|f'(q0)| − (r²/2) H` when `|f''| ≤ H` on
  `[ql, qh]`, `q0` the midpoint, `r = (qh − ql)/2` (monotonicity of `f − f(q0) − f'(q0)(x − q0) +
  H(x − q0)²/2`).
* `Lpf` (`L'`), `hasDerivAt_Lf`, `abs_Lpf_le`, `hasDerivAt_Pf`, `hasDerivAt_dPf`, `k1f` (`κ'`), `k2f`
  (`κ''`), `hasDerivAt_WP`, `hasDerivAt_k1f`, `abs_k2f_le`.
* **`kappa_ge_secondOrder`** (`0 ≤ j ≤ M`), **`kappa_neg_one_ge_secondOrder`** (`j = −1`),
  **`kappa_top_ge_secondOrder`** (`j = M + 1`): Soul's second-order bound for `κ + cδ + μδ²`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.Atlas

/-- **Second-order Taylor lower bound**: if `|f''| ≤ H` on `[a, b]` then
`f(x) ≥ f(x0) + f'(x0)(x − x0) − (H/2)(x − x0)²` for `x, x0 ∈ [a, b]`. -/
theorem taylor2_lower {f f' f'' : ℝ → ℝ} {a b x0 x H : ℝ}
    (hx0 : x0 ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y) (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hH : ∀ y ∈ Set.Icc a b, |f'' y| ≤ H) :
    f x0 + f' x0 * (x - x0) - H / 2 * (x - x0) ^ 2 ≤ f x := by
  -- `|f' y − f' x0| ≤ H |y − x0|` on `[a, b]`
  have hlip : ∀ y ∈ Set.Icc a b, |f' y - f' x0| ≤ H * |y - x0| := by
    intro y hy
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f') (f' := f'') (s := Set.Icc a b)
      (C := H) (fun z hz => (hf' z hz).hasDerivWithinAt) (fun z hz => by rw [Real.norm_eq_abs]; exact hH z hz)
      (convex_Icc a b) hx0 hy
    simpa [Real.norm_eq_abs] using this
  set g : ℝ → ℝ := fun y => f y - f x0 - f' x0 * (y - x0) + H / 2 * (y - x0) ^ 2 with hg
  have hgd : ∀ y ∈ Set.Icc a b, HasDerivAt g (f' y - f' x0 + H * (y - x0)) y := by
    intro y hy
    have h1 := hf y hy
    have h2 : HasDerivAt (fun y : ℝ => f' x0 * (y - x0)) (f' x0 * 1) y :=
      ((hasDerivAt_id y).sub_const x0).const_mul (f' x0)
    have h3 : HasDerivAt (fun y : ℝ => H / 2 * (y - x0) ^ 2) (H / 2 * (2 * (y - x0) ^ 1 * 1)) y := by
      have := ((hasDerivAt_id y).sub_const x0).pow 2
      simpa using this.const_mul (H / 2)
    have := ((h1.sub_const (f x0)).sub h2).add h3
    convert this using 1
    ring
  have hg0 : g x0 = 0 := by simp [hg]
  have hcont : ∀ c d, Set.Icc c d ⊆ Set.Icc a b → ContinuousOn g (Set.Icc c d) := fun c d hcd y hy =>
    (hgd y (hcd hy)).continuousAt.continuousWithinAt
  have key : 0 ≤ g x := by
    rcases le_total x0 x with hle | hle
    · have hmono : MonotoneOn g (Set.Icc x0 x) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => f' y - f' x0 + H * (y - x0))
          (convex_Icc x0 x) (hcont _ _ fun y hy => ⟨hx0.1.trans hy.1, hy.2.trans hx.2⟩) ?_ ?_
        · intro y hy
          rw [interior_Icc] at hy
          exact (hgd y ⟨hx0.1.trans hy.1.le, hy.2.le.trans hx.2⟩).hasDerivWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          have := hlip y ⟨hx0.1.trans hy.1.le, hy.2.le.trans hx.2⟩
          rw [abs_of_pos (by linarith [hy.1] : (0 : ℝ) < y - x0)] at this
          have := neg_abs_le (f' y - f' x0)
          show 0 ≤ f' y - f' x0 + H * (y - x0)
          linarith
      have := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
      linarith
    · have hanti : AntitoneOn g (Set.Icc x x0) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => f' y - f' x0 + H * (y - x0))
          (convex_Icc x x0) (hcont _ _ fun y hy => ⟨hx.1.trans hy.1, hy.2.trans hx0.2⟩) ?_ ?_
        · intro y hy
          rw [interior_Icc] at hy
          exact (hgd y ⟨hx.1.trans hy.1.le, hy.2.le.trans hx0.2⟩).hasDerivWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          have := hlip y ⟨hx.1.trans hy.1.le, hy.2.le.trans hx0.2⟩
          rw [abs_of_neg (by linarith [hy.2] : y - x0 < 0)] at this
          have := le_abs_self (f' y - f' x0)
          show f' y - f' x0 + H * (y - x0) ≤ 0
          linarith
      have := hanti ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
      linarith
  simp only [hg] at key
  linarith

/-- The second-order bound at the midpoint: `f(q) ≥ f(q0) − r|f'(q0)| − (r²/2) H`, `r = (qh − ql)/2`. -/
theorem taylor2_mid {f f' f'' : ℝ → ℝ} {ql qh q H : ℝ} (hlh : ql ≤ qh) (hq : ql ≤ q) (hq' : q ≤ qh)
    (hf : ∀ y ∈ Set.Icc ql qh, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc ql qh, HasDerivAt f' (f'' y) y)
    (hH : ∀ y ∈ Set.Icc ql qh, |f'' y| ≤ H) :
    f ((ql + qh) / 2) - (qh - ql) / 2 * |f' ((ql + qh) / 2)| - (qh - ql) / 2 * ((qh - ql) / 2) * H / 2 ≤
      f q := by
  have hmid : (ql + qh) / 2 ∈ Set.Icc ql qh := ⟨by linarith, by linarith⟩
  have h := taylor2_lower hmid ⟨hq, hq'⟩ hf hf' hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH _ hmid)
  have hd : |q - (ql + qh) / 2| ≤ (qh - ql) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 : -((qh - ql) / 2 * |f' ((ql + qh) / 2)|) ≤ f' ((ql + qh) / 2) * (q - (ql + qh) / 2) := by
    have := neg_abs_le (f' ((ql + qh) / 2) * (q - (ql + qh) / 2))
    rw [abs_mul] at this
    nlinarith [abs_nonneg (f' ((ql + qh) / 2))]
  have h2 : (q - (ql + qh) / 2) ^ 2 ≤ (qh - ql) / 2 * ((qh - ql) / 2) := by
    have := sq_abs (q - (ql + qh) / 2)
    nlinarith [abs_nonneg (q - (ql + qh) / 2)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hH0]

/-! ### Second derivatives -/

/-- `L'(x) = −(j − 1)/x² − (M − j − 1)/(1 − x)²`. -/
noncomputable def Lpf (M j : ℕ) (x : ℝ) : ℝ := -(((j : ℝ) - 1) / x ^ 2) - ((M : ℝ) - (j : ℝ) - 1) / (1 - x) ^ 2

theorem hasDerivAt_Lf (M j : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (Lf M j) (Lpf M j x) x := by
  have h1 : (1 - x) ≠ 0 := by linarith
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have ha := (hasDerivAt_inv hx0.ne').const_mul ((j : ℝ) - 1)
  have hb := ((hasDerivAt_inv h1).comp x hsub).const_mul ((M : ℝ) - (j : ℝ) - 1)
  have hfun : Lf M j = fun y => ((j : ℝ) - 1) * y⁻¹ -
      ((M : ℝ) - (j : ℝ) - 1) * ((fun y : ℝ => y⁻¹) ∘ (fun y : ℝ => 1 - y)) y := by
    funext y
    unfold Lf
    simp [Function.comp, div_eq_mul_inv]
  rw [hfun]
  convert ha.sub hb using 1
  unfold Lpf
  field_simp

theorem abs_Lpf_le {M j : ℕ} {ql qh x : ℝ} (h0 : 0 < ql) (h1 : qh < 1) (hx : ql ≤ x) (hx' : x ≤ qh) :
    |Lpf M j x| ≤ |(j : ℝ) - 1| / (ql * ql) + |(M : ℝ) - (j : ℝ) - 1| / ((1 - qh) * (1 - qh)) := by
  unfold Lpf
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < 1 - x := by linarith
  have e1 : |(j : ℝ) - 1| / x ^ 2 ≤ |(j : ℝ) - 1| / (ql * ql) := by
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity); nlinarith
  have e2 : |(M : ℝ) - (j : ℝ) - 1| / (1 - x) ^ 2 ≤ |(M : ℝ) - (j : ℝ) - 1| / ((1 - qh) * (1 - qh)) := by
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by nlinarith) ; nlinarith
  calc |-(((j : ℝ) - 1) / x ^ 2) - ((M : ℝ) - (j : ℝ) - 1) / (1 - x) ^ 2|
      ≤ |((j : ℝ) - 1) / x ^ 2| + |((M : ℝ) - (j : ℝ) - 1) / (1 - x) ^ 2| := by
        rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
    _ = |(j : ℝ) - 1| / x ^ 2 + |(M : ℝ) - (j : ℝ) - 1| / (1 - x) ^ 2 := by
        rw [abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2),
          abs_of_pos (by positivity : (0 : ℝ) < (1 - x) ^ 2)]
    _ ≤ _ := add_le_add e1 e2

theorem hasDerivAt_Pf (a b x : ℝ) : HasDerivAt (Pf a b) (dPf a b x) x := by
  have : Pf a b = fun y => a - 2 * a * y + (a + b) * y ^ 2 := by funext y; unfold Pf; ring
  rw [this]
  have := (((hasDerivAt_id x).const_mul (2 * a)).const_sub a).add ((hasDerivAt_pow 2 x).const_mul (a + b))
  convert this using 1
  unfold dPf; simp; ring

theorem hasDerivAt_dPf (a b x : ℝ) : HasDerivAt (dPf a b) (2 * (a + b)) x := by
  have : dPf a b = fun y => -2 * a + (2 * (a + b)) * y := by funext y; unfold dPf; ring
  rw [this]
  simpa using ((hasDerivAt_id x).const_mul (2 * (a + b))).const_add (-2 * a)

/-- `κ' = W (L P + P')` (for `κ = W P`). -/
noncomputable def k1f (M j : ℕ) (a b x : ℝ) : ℝ := Wf M j x * (Lf M j x * Pf a b x + dPf a b x)

/-- `κ'' = W ((L² + L') P + 2 L P' + P'')`. -/
noncomputable def k2f (M j : ℕ) (a b x : ℝ) : ℝ :=
  Wf M j x * ((Lf M j x ^ 2 + Lpf M j x) * Pf a b x + 2 * Lf M j x * dPf a b x + 2 * (a + b))

theorem hasDerivAt_WP {M j : ℕ} (hj : j ≤ M) (a b : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Wf M j y * Pf a b y) (k1f M j a b x) x := by
  have := (hasDerivAt_Wf hj hx0 hx1).mul (hasDerivAt_Pf a b x)
  convert this using 1
  unfold k1f; ring

theorem hasDerivAt_k1f {M j : ℕ} (hj : j ≤ M) (a b : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (k1f M j a b) (k2f M j a b x) x := by
  have hW := hasDerivAt_Wf hj hx0 hx1
  have hL := hasDerivAt_Lf M j hx0 hx1
  have hP := hasDerivAt_Pf a b x
  have hdP := hasDerivAt_dPf a b x
  have := hW.mul ((hL.mul hP).add hdP)
  unfold k1f
  convert this using 1
  simp only [Pi.add_apply, Pi.mul_apply]
  unfold k2f
  ring

theorem abs_k2f_le {M j : ℕ} {a b x wm pa dp la lp : ℝ} (hW0 : 0 ≤ Wf M j x) (hW : Wf M j x ≤ wm)
    (hP : |Pf a b x| ≤ pa) (hdP : |dPf a b x| ≤ dp) (hL : |Lf M j x| ≤ la) (hLp : |Lpf M j x| ≤ lp) :
    |k2f M j a b x| ≤ wm * (|2 * (a + b)| + 2 * la * dp + (la * la + lp) * pa) := by
  unfold k2f
  have hla : 0 ≤ la := (abs_nonneg _).trans hL
  have hpa : 0 ≤ pa := (abs_nonneg _).trans hP
  have hdp : 0 ≤ dp := (abs_nonneg _).trans hdP
  have hlp : 0 ≤ lp := (abs_nonneg _).trans hLp
  have hin : |(Lf M j x ^ 2 + Lpf M j x) * Pf a b x + 2 * Lf M j x * dPf a b x + 2 * (a + b)| ≤
      |2 * (a + b)| + 2 * la * dp + (la * la + lp) * pa := by
    have t1 : |(Lf M j x ^ 2 + Lpf M j x) * Pf a b x| ≤ (la * la + lp) * pa := by
      rw [abs_mul]
      refine mul_le_mul ?_ hP (abs_nonneg _) (by positivity)
      calc |Lf M j x ^ 2 + Lpf M j x| ≤ |Lf M j x ^ 2| + |Lpf M j x| := abs_add_le _ _
        _ ≤ la * la + lp := by
          rw [abs_pow]; nlinarith [abs_nonneg (Lf M j x)]
    have t2 : |2 * Lf M j x * dPf a b x| ≤ 2 * la * dp := by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul hL hdP (abs_nonneg _) hla
      nlinarith
    calc _ ≤ |(Lf M j x ^ 2 + Lpf M j x) * Pf a b x| + |2 * Lf M j x * dPf a b x| + |2 * (a + b)| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  rw [abs_mul, abs_of_nonneg hW0]
  exact mul_le_mul hW hin (abs_nonneg _) (hW0.trans hW)

/-! ### Soul's second-order bound for the three kinds of atoms -/

theorem hasDerivAt_quadPart (c mu jr Mr y : ℝ) :
    HasDerivAt (fun y => c * (jr - y * Mr) + mu * (jr - y * Mr) ^ 2)
      (-(Mr * (c + 2 * mu * (jr - y * Mr)))) y := by
  have hlin : HasDerivAt (fun y : ℝ => jr - y * Mr) (-Mr) y := by
    simpa using ((hasDerivAt_id y).mul_const Mr).const_sub jr
  have := (hlin.const_mul c).add ((hlin.pow 2).const_mul mu)
  convert this using 1
  simp; ring

theorem hasDerivAt_quadPart' (c mu jr Mr y : ℝ) :
    HasDerivAt (fun y => -(Mr * (c + 2 * mu * (jr - y * Mr)))) (2 * mu * (Mr * Mr)) y := by
  have hlin : HasDerivAt (fun y : ℝ => jr - y * Mr) (-Mr) y := by
    simpa using ((hasDerivAt_id y).mul_const Mr).const_sub jr
  have := (((hlin.const_mul (2 * mu)).const_add c).const_mul Mr).neg
  convert this using 1
  ring

/-- **Soul's second-order bound, atoms `0 ≤ j ≤ M`** (`atlas_quadratic_frozen.py`). -/
theorem kappa_ge_secondOrder {M j : ℕ} (hj : j ≤ M) {ql qh q wm pa dp la lp c mu : ℝ}
    (h0 : 0 < ql) (hlh : ql ≤ qh) (h1 : qh < 1) (hq : ql ≤ q) (hq' : q ≤ qh) (hmu : 0 ≤ mu)
    (hW : ∀ x, ql ≤ x → x ≤ qh → Wf M j x ≤ wm)
    (hP : ∀ x, ql ≤ x → x ≤ qh → |Pf (coefAR M j) (coefBR M j) x| ≤ pa)
    (hdP : ∀ x, ql ≤ x → x ≤ qh → |dPf (coefAR M j) (coefBR M j) x| ≤ dp)
    (hL : ∀ x, ql ≤ x → x ≤ qh → |Lf M j x| ≤ la)
    (hLp : ∀ x, ql ≤ x → x ≤ qh → |Lpf M j x| ≤ lp) :
    kappa ((ql + qh) / 2) M j + (mu * (((j : ℝ) - (ql + qh) / 2 * M) * ((j : ℝ) - (ql + qh) / 2 * M)) +
        c * ((j : ℝ) - (ql + qh) / 2 * M)) -
      (qh - ql) / 2 * |k1f M j (coefAR M j) (coefBR M j) ((ql + qh) / 2) -
        (M : ℝ) * (c + 2 * mu * ((j : ℝ) - (ql + qh) / 2 * M))| -
      (qh - ql) / 2 * ((qh - ql) / 2) *
        (wm * (|2 * (coefAR M j + coefBR M j)| + 2 * la * dp + (la * la + lp) * pa) +
          2 * mu * ((M : ℝ) * (M : ℝ))) / 2 ≤
      kappa q M j + c * ((j : ℝ) - q * M) + mu * ((j : ℝ) - q * M) ^ 2 := by
  set a := coefAR M j
  set b := coefBR M j
  set f : ℝ → ℝ := fun y => Wf M j y * Pf a b y + (c * ((j : ℝ) - y * M) + mu * ((j : ℝ) - y * M) ^ 2)
  set f' : ℝ → ℝ := fun y => k1f M j a b y + -((M : ℝ) * (c + 2 * mu * ((j : ℝ) - y * M)))
  set f'' : ℝ → ℝ := fun y => k2f M j a b y + 2 * mu * ((M : ℝ) * (M : ℝ))
  have hin : ∀ y ∈ Set.Icc ql qh, 0 < y ∧ y < 1 := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hf : ∀ y ∈ Set.Icc ql qh, HasDerivAt f (f' y) y := fun y hy =>
    (hasDerivAt_WP hj a b (hin y hy).1 (hin y hy).2).add (hasDerivAt_quadPart c mu j M y)
  have hf' : ∀ y ∈ Set.Icc ql qh, HasDerivAt f' (f'' y) y := fun y hy =>
    (hasDerivAt_k1f hj a b (hin y hy).1 (hin y hy).2).add (hasDerivAt_quadPart' c mu j M y)
  have hH : ∀ y ∈ Set.Icc ql qh, |f'' y| ≤
      wm * (|2 * (a + b)| + 2 * la * dp + (la * la + lp) * pa) + 2 * mu * ((M : ℝ) * (M : ℝ)) := by
    intro y hy
    have hk := abs_k2f_le (Wf_pos hj (hin y hy).1 (hin y hy).2).le (hW y hy.1 hy.2) (hP y hy.1 hy.2)
      (hdP y hy.1 hy.2) (hL y hy.1 hy.2) (hLp y hy.1 hy.2)
    have h2 : 0 ≤ 2 * mu * ((M : ℝ) * (M : ℝ)) := by positivity
    calc |f'' y| ≤ |k2f M j a b y| + |2 * mu * ((M : ℝ) * (M : ℝ))| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg h2]; linarith
  have hT := taylor2_mid hlh hq hq' hf hf' hH
  have hq0 : 0 < (ql + qh) / 2 ∧ (ql + qh) / 2 < 1 := ⟨by linarith, by linarith⟩
  have ef : f q = kappa q M j + c * ((j : ℝ) - q * M) + mu * ((j : ℝ) - q * M) ^ 2 := by
    simp only [f]; rw [kappa_eq_WP hj (by linarith) (by linarith)]; ring
  have ef0 : f ((ql + qh) / 2) = kappa ((ql + qh) / 2) M j + (mu * (((j : ℝ) - (ql + qh) / 2 * M) *
      ((j : ℝ) - (ql + qh) / 2 * M)) + c * ((j : ℝ) - (ql + qh) / 2 * M)) := by
    simp only [f]; rw [kappa_eq_WP hj hq0.1 hq0.2]; ring
  have ef'0 : f' ((ql + qh) / 2) = k1f M j a b ((ql + qh) / 2) -
      (M : ℝ) * (c + 2 * mu * ((j : ℝ) - (ql + qh) / 2 * M)) := by simp only [f']; ring
  rw [← ef, ← ef0, ← ef'0]
  exact hT

/-- The second derivative bound `|M(M − 1) y^{M−2}| ≤ M(M − 1) x^{M−2}` for `0 ≤ y ≤ x`, with the
`ℕ`-cast of `M − 1` as produced by `hasDerivAt_pow`. -/
theorem natCast_pred_pow_le (M : ℕ) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    |(M : ℝ) * (((M - 1 : ℕ) : ℝ) * y ^ (M - 1 - 1))| ≤ (M : ℝ) * ((M : ℝ) - 1) * x ^ (M - 2) := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · have hc : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub h]; simp
    rw [hc, show M - 1 - 1 = M - 2 by omega]
    have hM1 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast h
      linarith
    rw [abs_of_nonneg (by positivity), ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyx _) (by positivity)

/-- **Soul's second-order bound, atom `j = −1`**: `κ = −(1 − q)^M`. -/
theorem kappa_neg_one_ge_secondOrder (M : ℕ) {ql qh q c mu : ℝ} (h1 : qh < 1) (hlh : ql ≤ qh)
    (hq : ql ≤ q) (hq' : q ≤ qh) (hmu : 0 ≤ mu) :
    -((1 - (ql + qh) / 2) ^ M) + (mu * ((-1 - (ql + qh) / 2 * M) * (-1 - (ql + qh) / 2 * M)) +
        c * (-1 - (ql + qh) / 2 * M)) -
      (qh - ql) / 2 * |(M : ℝ) * (1 - (ql + qh) / 2) ^ (M - 1) -
        (M : ℝ) * (c + 2 * mu * (-1 - (ql + qh) / 2 * M))| -
      (qh - ql) / 2 * ((qh - ql) / 2) *
        ((M : ℝ) * ((M : ℝ) - 1) * (1 - ql) ^ (M - 2) + 2 * mu * ((M : ℝ) * (M : ℝ))) / 2 ≤
      kappa q M (-1) + c * (((-1 : ℤ) : ℝ) - q * M) + mu * (((-1 : ℤ) : ℝ) - q * M) ^ 2 := by
  have hsub : ∀ y, HasDerivAt (fun y : ℝ => 1 - y) (-1) y := fun y => by
    simpa using (hasDerivAt_id y).const_sub 1
  set f : ℝ → ℝ := fun y => -((1 - y) ^ M) + (c * (-1 - y * M) + mu * (-1 - y * M) ^ 2)
  set f' : ℝ → ℝ := fun y => (M : ℝ) * (1 - y) ^ (M - 1) + -((M : ℝ) * (c + 2 * mu * (-1 - y * M)))
  set f'' : ℝ → ℝ := fun y => -((M : ℝ) * (((M - 1 : ℕ) : ℝ) * (1 - y) ^ (M - 1 - 1))) +
    2 * mu * ((M : ℝ) * (M : ℝ))
  have hf : ∀ y ∈ Set.Icc ql qh, HasDerivAt f (f' y) y := by
    intro y _
    have := (((hsub y).pow M).neg).add (hasDerivAt_quadPart c mu (-1) M y)
    convert this using 1
    simp only [f']; ring
  have hf' : ∀ y ∈ Set.Icc ql qh, HasDerivAt f' (f'' y) y := by
    intro y _
    have := (((hsub y).pow (M - 1)).const_mul (M : ℝ)).add (hasDerivAt_quadPart' c mu (-1) M y)
    convert this using 1
    simp only [f'']; ring
  have hH : ∀ y ∈ Set.Icc ql qh, |f'' y| ≤
      (M : ℝ) * ((M : ℝ) - 1) * (1 - ql) ^ (M - 2) + 2 * mu * ((M : ℝ) * (M : ℝ)) := by
    intro y hy
    have hb := natCast_pred_pow_le M (x := 1 - ql) (y := 1 - y) (by linarith [hy.2]) (by linarith [hy.1])
    have h2 : 0 ≤ 2 * mu * ((M : ℝ) * (M : ℝ)) := by positivity
    calc |f'' y| ≤ |-((M : ℝ) * (((M - 1 : ℕ) : ℝ) * (1 - y) ^ (M - 1 - 1)))| +
          |2 * mu * ((M : ℝ) * (M : ℝ))| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg, abs_of_nonneg h2]; linarith
  have hT := taylor2_mid hlh hq hq' hf hf' hH
  have ef : f q = kappa q M (-1) + c * (((-1 : ℤ) : ℝ) - q * M) + mu * (((-1 : ℤ) : ℝ) - q * M) ^ 2 := by
    simp only [f]; rw [kappa_neg_one (by linarith)]; push_cast; ring
  have ef0 : f ((ql + qh) / 2) = -((1 - (ql + qh) / 2) ^ M) + (mu * ((-1 - (ql + qh) / 2 * M) *
      (-1 - (ql + qh) / 2 * M)) + c * (-1 - (ql + qh) / 2 * M)) := by simp only [f]; ring
  have ef'0 : f' ((ql + qh) / 2) = (M : ℝ) * (1 - (ql + qh) / 2) ^ (M - 1) -
      (M : ℝ) * (c + 2 * mu * (-1 - (ql + qh) / 2 * M)) := by simp only [f']; ring
  rw [← ef, ← ef0, ← ef'0]
  exact hT

/-- **Soul's second-order bound, atom `j = M + 1`**: `κ = −q^M`. -/
theorem kappa_top_ge_secondOrder (M : ℕ) {ql qh q c mu : ℝ} (h0 : 0 < ql) (hlh : ql ≤ qh)
    (hq : ql ≤ q) (hq' : q ≤ qh) (hmu : 0 ≤ mu) :
    -(((ql + qh) / 2) ^ M) + (mu * (((M : ℝ) + 1 - (ql + qh) / 2 * M) * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) +
        c * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) -
      (qh - ql) / 2 * |-((M : ℝ) * ((ql + qh) / 2) ^ (M - 1)) -
        (M : ℝ) * (c + 2 * mu * ((M : ℝ) + 1 - (ql + qh) / 2 * M))| -
      (qh - ql) / 2 * ((qh - ql) / 2) *
        ((M : ℝ) * ((M : ℝ) - 1) * qh ^ (M - 2) + 2 * mu * ((M : ℝ) * (M : ℝ))) / 2 ≤
      kappa q M ((M : ℤ) + 1) + c * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) +
        mu * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) ^ 2 := by
  set f : ℝ → ℝ := fun y => -(y ^ M) + (c * (((M : ℝ) + 1) - y * M) + mu * (((M : ℝ) + 1) - y * M) ^ 2)
  set f' : ℝ → ℝ := fun y => -((M : ℝ) * y ^ (M - 1)) + -((M : ℝ) * (c + 2 * mu * (((M : ℝ) + 1) - y * M)))
  set f'' : ℝ → ℝ := fun y => -((M : ℝ) * (((M - 1 : ℕ) : ℝ) * y ^ (M - 1 - 1))) +
    2 * mu * ((M : ℝ) * (M : ℝ))
  have hf : ∀ y ∈ Set.Icc ql qh, HasDerivAt f (f' y) y := by
    intro y _
    have := ((hasDerivAt_pow M y).neg).add (hasDerivAt_quadPart c mu ((M : ℝ) + 1) M y)
    convert this using 1
  have hf' : ∀ y ∈ Set.Icc ql qh, HasDerivAt f' (f'' y) y := by
    intro y _
    have := (((hasDerivAt_pow (M - 1) y).const_mul (M : ℝ)).neg).add
      (hasDerivAt_quadPart' c mu ((M : ℝ) + 1) M y)
    convert this using 1
  have hH : ∀ y ∈ Set.Icc ql qh, |f'' y| ≤
      (M : ℝ) * ((M : ℝ) - 1) * qh ^ (M - 2) + 2 * mu * ((M : ℝ) * (M : ℝ)) := by
    intro y hy
    have hb := natCast_pred_pow_le M (x := qh) (y := y) (by linarith [hy.1]) hy.2
    have h2 : 0 ≤ 2 * mu * ((M : ℝ) * (M : ℝ)) := by positivity
    calc |f'' y| ≤ |-((M : ℝ) * (((M - 1 : ℕ) : ℝ) * y ^ (M - 1 - 1)))| +
          |2 * mu * ((M : ℝ) * (M : ℝ))| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg, abs_of_nonneg h2]; linarith
  have hT := taylor2_mid hlh hq hq' hf hf' hH
  have ef : f q = kappa q M ((M : ℤ) + 1) + c * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) +
      mu * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) ^ 2 := by
    simp only [f]; rw [kappa_top (by linarith)]; push_cast; ring
  have ef0 : f ((ql + qh) / 2) = -(((ql + qh) / 2) ^ M) + (mu * (((M : ℝ) + 1 - (ql + qh) / 2 * M) *
      ((M : ℝ) + 1 - (ql + qh) / 2 * M)) + c * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) := by
    simp only [f]; ring
  have ef'0 : f' ((ql + qh) / 2) = -((M : ℝ) * ((ql + qh) / 2) ^ (M - 1)) -
      (M : ℝ) * (c + 2 * mu * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) := by simp only [f']; ring
  rw [← ef, ← ef0, ← ef'0]
  exact hT

end Erdos993Lean.Analytic.Atlas
