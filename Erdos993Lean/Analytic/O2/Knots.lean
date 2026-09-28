import Erdos993Lean.Analytic.O2.Defs

/-!
# O2: the coefficient fields are piecewise affine; the parent-knot reduction

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A16; for lane A18's certificate checker).
Source: `PRO_R2_PROOF.md` §6: "For fixed `λ, p, r` and fixed `z`, `Φ` is affine in the quadruple
`(u(t), v(t), s(t), τ(t))`.  All four are piecewise linear on the same parent knots.  Therefore it
suffices to check the actual admissible parent interval's endpoints and its common interior knots."

* `AffOn a c g`: `g` agrees with an affine function on `[a, c]`; closed under sums, scalar
  multiples, constants and affine reparametrization;
* `hat_affOn`: the hat function is affine on every integer cell `[m, m + 1]`;
  `pwLin_affOn`: `pwLin f` is affine on every cell `[k/8, (k+1)/8]`;
* **`pwLin_knot`**: `pwLin f (j/8) = f j`; **`pwLin_eq_cell`**: on `[k/8, (k+1)/8]` (`k < 8`),
  `pwLin f x = f_k + (8x − k)(f_{k+1} − f_k)` (the evaluation formula for a checker);
* `BandData.field_affOn`: every coefficient field is affine in the cavity probability on every
  parent cell `[q k/8, q (k+1)/8]`; `BandData.phi_affOn`: so is `t ↦ Φ(λ, p, r, t, z)`;
* **`BandData.phi_nonneg_of_knots`** (the reduction): if `0 ≤ t_lo ≤ t_hi ≤ q`, and `Φ ≥ 0` at
  `t_lo`, at `t_hi` and at every knot `q j/8` in between, then `Φ ≥ 0` on all of `[t_lo, t_hi]`.
  (For the six R2 formats `t_lo = 1 − r`, `t_hi = λ(1−p)/(1+λ(1−p))`; for the retained-`Y` format
  `t_hi` is the smaller retained bound.)
-/

namespace Erdos993Lean.Analytic.O2

/-! ### Affine pieces -/

/-- `g` agrees with an affine function on `[a, c]`. -/
def AffOn (a c : ℝ) (g : ℝ → ℝ) : Prop := ∃ α β : ℝ, ∀ x, a ≤ x → x ≤ c → g x = α + β * x

namespace AffOn

variable {a c : ℝ}

theorem const (k : ℝ) : AffOn a c (fun _ => k) := ⟨k, 0, fun _ _ _ => by ring⟩

theorem add {f g : ℝ → ℝ} (hf : AffOn a c f) (hg : AffOn a c g) :
    AffOn a c (fun x => f x + g x) := by
  obtain ⟨α1, β1, h1⟩ := hf
  obtain ⟨α2, β2, h2⟩ := hg
  exact ⟨α1 + α2, β1 + β2, fun x hx1 hx2 => by dsimp only; rw [h1 x hx1 hx2, h2 x hx1 hx2]; ring⟩

theorem const_mul (k : ℝ) {f : ℝ → ℝ} (hf : AffOn a c f) : AffOn a c (fun x => k * f x) := by
  obtain ⟨α, β, h⟩ := hf
  exact ⟨k * α, k * β, fun x hx1 hx2 => by dsimp only; rw [h x hx1 hx2]; ring⟩

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, AffOn a c (f i)) :
    AffOn a c (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (a := a) (c := c) 0
  | insert i s his ih =>
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert his] using add h1 h2

/-- Affine reparametrization. -/
theorem comp {a' c' m d : ℝ} {g φ : ℝ → ℝ} (hg : AffOn a' c' g) (hφ : ∀ x, φ x = m * x + d)
    (hmap : ∀ x, a ≤ x → x ≤ c → a' ≤ φ x ∧ φ x ≤ c') :
    AffOn a c (fun x => g (φ x)) := by
  obtain ⟨α, β, h⟩ := hg
  exact ⟨α + β * d, β * m, fun x hx1 hx2 => by
    dsimp only; rw [h _ (hmap x hx1 hx2).1 (hmap x hx1 hx2).2, hφ]; ring⟩

theorem mono {a' c' : ℝ} {g : ℝ → ℝ} (hg : AffOn a c g) (h1 : a ≤ a') (h2 : c' ≤ c) :
    AffOn a' c' g := by
  obtain ⟨α, β, h⟩ := hg
  exact ⟨α, β, fun x hx1 hx2 => h x (h1.trans hx1) (hx2.trans h2)⟩

/-- An affine function nonnegative at both ends of an interval is nonnegative on it. -/
theorem nonneg {g : ℝ → ℝ} (hg : AffOn a c g) (ha : 0 ≤ g a) (hc : 0 ≤ g c) {x : ℝ}
    (hx1 : a ≤ x) (hx2 : x ≤ c) : 0 ≤ g x := by
  obtain ⟨α, β, h⟩ := hg
  have hac : a ≤ c := hx1.trans hx2
  rw [h a le_rfl hac] at ha
  rw [h c hac le_rfl] at hc
  rw [h x hx1 hx2]
  rcases le_total 0 β with hβ | hβ
  · nlinarith [mul_le_mul_of_nonneg_left hx1 hβ]
  · nlinarith [mul_le_mul_of_nonpos_left hx2 hβ]

end AffOn

/-! ### The hat function and the interpolation -/

/-- The hat function is affine on every integer cell `[m, m + 1]`. -/
theorem hat_affOn (m : ℤ) : AffOn m (m + 1) hat := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rcases eq_or_lt_of_le (Int.le_sub_one_of_lt hm) with hm1 | hm1
    · -- m = -1: hat y = 1 + y on [-1, 0]
      have hm' : (m : ℝ) = -1 := by rw [hm1]; norm_num
      refine ⟨1, 1, fun x hx1 hx2 => ?_⟩
      rw [hm'] at hx1 hx2
      unfold hat
      rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
      ring
    · -- m ≤ -2: hat y = 0 on [m, m + 1] ⊆ (-∞, -1]
      have hm' : (m : ℝ) ≤ -2 := by
        have : m ≤ -2 := by omega
        exact_mod_cast this
      refine ⟨0, 0, fun x hx1 hx2 => ?_⟩
      unfold hat
      rw [abs_of_neg (by linarith), max_eq_left (by linarith)]
      ring
  · -- m = 0: hat y = 1 - y on [0, 1]
    subst hm
    refine ⟨1, -1, fun x hx1 hx2 => ?_⟩
    push_cast at hx1 hx2
    unfold hat
    rw [abs_of_nonneg hx1, max_eq_right (by linarith)]
    ring
  · -- m ≥ 1: hat y = 0 on [m, m + 1] ⊆ [1, ∞)
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    refine ⟨0, 0, fun x hx1 hx2 => ?_⟩
    unfold hat
    rw [abs_of_pos (by linarith), max_eq_left (by linarith)]
    ring

/-- `pwLin f` is affine on every cell `[k/8, (k+1)/8]`. -/
theorem pwLin_affOn (f : Fin 9 → ℝ) (k : ℕ) : AffOn ((k : ℝ) / 8) (((k : ℝ) + 1) / 8) (pwLin f) := by
  unfold pwLin
  refine AffOn.sum _ fun j _ => AffOn.const_mul (f j) ?_
  refine AffOn.comp (hat_affOn ((k : ℤ) - ((j : ℕ) : ℤ))) (m := 8) (d := -((j : ℕ) : ℝ))
    (fun x => by ring) (fun x hx1 hx2 => ⟨?_, ?_⟩)
  · push_cast; linarith
  · push_cast; linarith

theorem hat_int (m : ℤ) : hat m = if m = 0 then 1 else 0 := by
  unfold hat
  split_ifs with hm
  · subst hm; norm_num
  · have : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hm
    rw [max_eq_left (by linarith)]

/-- **The value at a knot**: `pwLin f (j/8) = f j`. -/
theorem pwLin_knot (f : Fin 9 → ℝ) (j : Fin 9) : pwLin f ((j : ℕ) / 8) = f j := by
  unfold pwLin
  rw [Finset.sum_eq_single j]
  · have : (8 : ℝ) * ((j : ℕ) / 8) - (j : ℕ) = ((0 : ℤ) : ℝ) := by push_cast; ring
    rw [this, hat_int]
    simp
  · intro i _ hij
    have : (8 : ℝ) * ((j : ℕ) / 8) - (i : ℕ) = (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) := by
      push_cast; ring
    rw [this, hat_int, if_neg, mul_zero]
    intro h
    apply hij
    exact Fin.ext (by omega)
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **The evaluation formula on a cell**: for `k < 8` and `x ∈ [k/8, (k+1)/8]`,
`pwLin f x = f_k + (8x − k)(f_{k+1} − f_k)`. -/
theorem pwLin_eq_cell (f : Fin 9 → ℝ) (k : ℕ) (hk : k < 8) {x : ℝ} (hx1 : (k : ℝ) / 8 ≤ x)
    (hx2 : x ≤ ((k : ℝ) + 1) / 8) :
    pwLin f x = f ⟨k, by omega⟩ + (8 * x - k) * (f ⟨k + 1, by omega⟩ - f ⟨k, by omega⟩) := by
  obtain ⟨α, β, h⟩ := pwLin_affOn f k
  have ha : pwLin f ((k : ℝ) / 8) = f ⟨k, by omega⟩ := pwLin_knot f ⟨k, by omega⟩
  have hc : pwLin f (((k : ℝ) + 1) / 8) = f ⟨k + 1, by omega⟩ := by
    have := pwLin_knot f ⟨k + 1, by omega⟩
    simpa using this
  have hle : (k : ℝ) / 8 ≤ ((k : ℝ) + 1) / 8 := by linarith
  rw [h _ le_rfl hle] at ha
  rw [h _ hle le_rfl] at hc
  rw [h x hx1 hx2]
  have hβ : β = 8 * (f ⟨k + 1, by omega⟩ - f ⟨k, by omega⟩) := by linarith
  subst hβ
  linarith

/-! ### The fields and the payment as functions of the parent's cavity probability -/

namespace BandData

variable (b : BandData)

/-- Every coefficient field is affine in the cavity probability on every cell
`[q k/8, q (k+1)/8]`. -/
theorem field_affOn (sel : CoeffTable → Fin 9 → ℚ) {lam : ℝ} (hq : 0 < actQ lam) (k : ℕ) :
    AffOn (actQ lam * k / 8) (actQ lam * (k + 1) / 8) (b.field sel lam) := by
  unfold field
  refine AffOn.comp (pwLin_affOn (b.knots sel lam) k) (m := 1 / actQ lam) (d := 0)
    (fun x => by ring) (fun x hx1 hx2 => ⟨?_, ?_⟩)
  · rw [le_div_iff₀ hq]; linarith
  · rw [div_le_iff₀ hq]; linarith

/-- For fixed `λ, p, r, z`, the payment is `Φ(0)` plus a fixed combination of the four parent
fields' increments. -/
theorem phi_eq_parent (lam p r t z : ℝ) :
    b.Phi lam p r t z = b.Phi lam p r 0 z +
      (-(hFun p * (max (-z) 0) ^ 2)) * (b.uF lam t - b.uF lam 0) +
      (-(hFun p * (max z 0) ^ 2)) * (b.vF lam t - b.vF lam 0) +
      (-((1 - r) * (1 - p) * z ^ 2)) * (b.sF lam t - b.sF lam 0) +
      ((1 - r) * z) * (b.tauF lam t - b.tauF lam 0) := by
  unfold Phi Ru Rv Rs Rtau
  ring

/-- **`t ↦ Φ(λ, p, r, t, z)` is affine on every parent cell `[q k/8, q (k+1)/8]`.** -/
theorem phi_affOn {lam : ℝ} (hq : 0 < actQ lam) (p r z : ℝ) (k : ℕ) :
    AffOn (actQ lam * k / 8) (actQ lam * (k + 1) / 8) (fun t => b.Phi lam p r t z) := by
  have hu := b.field_affOn CoeffTable.u hq k
  have hv := b.field_affOn CoeffTable.v hq k
  have hs := b.field_affOn CoeffTable.s hq k
  have hτ := b.field_affOn CoeffTable.tau hq k
  have h := AffOn.add (AffOn.add (AffOn.add (AffOn.add
    (AffOn.const (a := actQ lam * k / 8) (c := actQ lam * (k + 1) / 8) (b.Phi lam p r 0 z))
    (AffOn.const_mul (-(hFun p * (max (-z) 0) ^ 2))
      (AffOn.add hu (AffOn.const (-b.uF lam 0)))))
    (AffOn.const_mul (-(hFun p * (max z 0) ^ 2)) (AffOn.add hv (AffOn.const (-b.vF lam 0)))))
    (AffOn.const_mul (-((1 - r) * (1 - p) * z ^ 2)) (AffOn.add hs (AffOn.const (-b.sF lam 0)))))
    (AffOn.const_mul ((1 - r) * z) (AffOn.add hτ (AffOn.const (-b.tauF lam 0))))
  have e : (fun t => b.Phi lam p r t z) = fun t => b.Phi lam p r 0 z +
      -(hFun p * (max (-z) 0) ^ 2) * (b.field CoeffTable.u lam t + -b.uF lam 0) +
      -(hFun p * (max z 0) ^ 2) * (b.field CoeffTable.v lam t + -b.vF lam 0) +
      -((1 - r) * (1 - p) * z ^ 2) * (b.field CoeffTable.s lam t + -b.sF lam 0) +
      (1 - r) * z * (b.field CoeffTable.tau lam t + -b.tauF lam 0) := by
    funext t
    rw [b.phi_eq_parent lam p r t z]
    unfold uF vF sF tauF
    ring
  rw [e]
  exact h

/-- **The parent-knot reduction.**  If `0 ≤ t_lo ≤ t_hi ≤ q`, and `Φ ≥ 0` at `t = t_lo`, at
`t = t_hi` and at every knot `t = q j/8` with `t_lo ≤ q j/8 ≤ t_hi`, then `Φ ≥ 0` at every
`t ∈ [t_lo, t_hi]` (for fixed `λ, p, r, z`). -/
theorem phi_nonneg_of_knots {lam p r z tlo thi : ℝ} (hq : 0 < actQ lam) (h0 : 0 ≤ tlo)
    (hq1 : thi ≤ actQ lam) (hlo : 0 ≤ b.Phi lam p r tlo z) (hhi : 0 ≤ b.Phi lam p r thi z)
    (hknot : ∀ j : ℕ, j ≤ 8 → tlo ≤ actQ lam * j / 8 → actQ lam * j / 8 ≤ thi →
      0 ≤ b.Phi lam p r (actQ lam * j / 8) z)
    {t : ℝ} (ht1 : tlo ≤ t) (ht2 : t ≤ thi) : 0 ≤ b.Phi lam p r t z := by
  have ht0 : 0 ≤ t := h0.trans ht1
  have htq : t ≤ actQ lam := ht2.trans hq1
  obtain ⟨k, hk7, hcell1, hcell2⟩ : ∃ k : ℕ, k ≤ 7 ∧ actQ lam * k / 8 ≤ t ∧
      t ≤ actQ lam * (k + 1) / 8 := by
    have hx : 0 ≤ 8 * t / actQ lam := by positivity
    rcases le_or_gt ⌊8 * t / actQ lam⌋₊ 7 with h | h
    · refine ⟨⌊8 * t / actQ lam⌋₊, h, ?_, ?_⟩
      · have hfl := Nat.floor_le hx
        rw [le_div_iff₀ hq] at hfl
        linarith
      · have hlt := Nat.lt_floor_add_one (8 * t / actQ lam)
        rw [div_lt_iff₀ hq] at hlt
        linarith
    · refine ⟨7, le_rfl, ?_, ?_⟩
      · have h8 : ((8 : ℕ) : ℝ) ≤ (⌊8 * t / actQ lam⌋₊ : ℝ) := by exact_mod_cast h
        have hfl := Nat.floor_le hx
        have : (7 : ℝ) ≤ 8 * t / actQ lam := by push_cast at h8; linarith
        rw [le_div_iff₀ hq] at this
        push_cast
        linarith
      · push_cast
        linarith
  have haff := b.phi_affOn hq p r z k
  have hPa : 0 ≤ b.Phi lam p r (max tlo (actQ lam * k / 8)) z := by
    rcases le_total tlo (actQ lam * k / 8) with h | h
    · rw [max_eq_right h]
      exact hknot k (by omega) h (hcell1.trans ht2)
    · rw [max_eq_left h]
      exact hlo
  have hPc : 0 ≤ b.Phi lam p r (min thi (actQ lam * (k + 1) / 8)) z := by
    rcases le_total thi (actQ lam * (k + 1) / 8) with h | h
    · rw [min_eq_left h]
      exact hhi
    · rw [min_eq_right h]
      have h' := hknot (k + 1) (by omega) (by push_cast; linarith) (by push_cast; linarith)
      push_cast at h'
      exact h'
  exact (haff.mono (le_max_right _ _) (min_le_right _ _)).nonneg hPa hPc (max_le ht1 hcell1)
    (le_min ht2 hcell2)

end BandData

end Erdos993Lean.Analytic.O2
