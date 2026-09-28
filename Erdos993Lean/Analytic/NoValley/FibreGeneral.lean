import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.LossForm
import Erdos993Lean.Analytic.NoValley.LogConcave

/-!
# The explicit fibre bound for all `q` (T1 Proposition 4.3; E4)

Source: T1 (`ProofRuns/2026-09-27_zhang_review/reports/T1.md`), §4, Proposition 4.3 (lines 201–205),
with Theorem 3.1 (§3) and Lemma 4.1 (§4).  The loss is `Φ_M(i) = (μ̃ − W(i)) Q_κ(i) − c'_M (i − i_v)`
(`lossPhi`, `NoValley/LossForm.lean`) and `L_M = max_i Φ_M(i)`.

T1's Proposition 4.3: `L_M ≤ L̄_M := max_i Φ̄_M(i)`, where `Φ̄_M` is `Φ_M` with `W` replaced by the
Lemma 4.1 lower bound (the maximum of the chord bound and the Taylor bound from the mode) on
`{Q_κ ≥ 0} = [i₋, i₊]`, by the Lemma 4.1 upper bound (anchored at `i₊` resp. `i₋`, with a curvature
below `c_N` over the lobe) on the lobes, and `W = 0` off `[0, N]`.

The principle (`lossPhi_le_lossPhiRep`): `Φ_M(i) − Φ̄_M(i) = (Ŵ(i) − W(i)) Q_κ(i)`, so replacing `W`
by a lower bound where `Q_κ ≥ 0` and by an upper bound where `Q_κ ≤ 0` can only increase `Φ`.

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

* `lossPhiRep` (`Φ̄_M` for a replacement weight `Ŵ`), `lossPhi_le_lossPhiRep` (the principle).
* `logLower` (max of chord and Taylor-from-anchor lower bounds for `log b_N`), `logLower_le`;
  `logUpper` (Taylor upper bounds anchored at `i₊`, `i₋`), `logb_le_logUpper`.
* `weightRep` (T1's explicit `W̄`: `exp(logLower)/(N(N − 1)v²)` on `[i₋, i₊]`,
  `exp(logUpper)/(N(N − 1)v²)` on the lobes of `[0, N]`, `0` off `[0, N]`), with
  `weightRep_le_kappaWeight`, `kappaWeight_le_weightRep`, `weightRep_off`.
* **T1 Proposition 4.3** (`prop43`, `prop43_max`): if `Q_κ ≥ 0` on `[i₋, i₊]` and `Q_κ ≤ 0` on the
  lobes, and the curvature constants are valid (`c_in ≤ c_N` on `(i₋, i₊)`, `c̄ ≥ c_N` between the
  anchor `i₀` and `[i₋, i₊]`, `c_R ≤ c_N` on `(i₊, N)`, `c_L ≤ c_N` on `(0, i₋)`; T1's min/max are
  such constants), then `Φ_M(i) ≤ Φ̄_M(i)` for every integer `i`; hence `Φ_M ≤ L̄` for every
  `L̄ ≥ max_i Φ̄_M(i)`, i.e. `L_M ≤ L̄_M`.
* `prop43_fibre`: then `P(M) − L̄` is a pointwise fibre bound with `ν = aμ̃` (Theorem 3.1).
-/

namespace Erdos993Lean.Analytic.NoValley

/-! ## The replacement principle -/

/-- `Φ̄_M(i) = (μ̃ − Ŵ(i)) Q_κ(i) − c'_M (i − i_v)` for a replacement weight `Ŵ`. -/
noncomputable def lossPhiRep (q μ c : ℝ) (M : ℕ) (Wr : ℤ → ℝ) (i : ℤ) : ℝ :=
  (μ - Wr i) * kappaQuad q M i - slopeC q μ c M * ((i : ℝ) - vertexI q M)

/-- **The replacement principle.**  If `Ŵ(i) ≤ W(i)` where `Q_κ(i) ≥ 0`, or `Ŵ(i) ≥ W(i)` where
`Q_κ(i) ≤ 0`, then `Φ_M(i) ≤ Φ̄_M(i)`. -/
theorem lossPhi_le_lossPhiRep {q μ c : ℝ} {M : ℕ} {Wr : ℤ → ℝ} {i : ℤ}
    (h : (0 ≤ kappaQuad q M i ∧ Wr i ≤ kappaWeight q M i) ∨
      (kappaQuad q M i ≤ 0 ∧ kappaWeight q M i ≤ Wr i)) :
    lossPhi q μ c M i ≤ lossPhiRep q μ c M Wr i := by
  have e : lossPhi q μ c M i - lossPhiRep q μ c M Wr i =
      (Wr i - kappaWeight q M i) * kappaQuad q M i := by
    unfold lossPhi lossPhiRep
    ring
  rcases h with ⟨hQ, hW⟩ | ⟨hQ, hW⟩
  · have := mul_nonneg (sub_nonneg.mpr hW) hQ
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hW) hQ
    nlinarith

/-! ## Explicit lower and upper bounds for `log b_N` (from T1 Lemma 4.1) -/

/-- The lower bound for `log b_N(i)` on `[i₋, i₊]`: the maximum of the chord bound (T1 Lemma 4.1 (i),
curvature `c_in`) and the Taylor bound from the anchor `i₀` (Lemma 4.1 (ii), curvature `c̄`; T1 takes
`i₀` = the mode of `b_N`). -/
noncomputable def logLower (q : ℝ) (N im ip i0 : ℕ) (cin cbar : ℝ) (i : ℕ) : ℝ :=
  max (logb q N im + ((i : ℝ) - im) / ((ip : ℝ) - im) * (logb q N ip - logb q N im) +
      cin / 2 * (((i : ℝ) - im) * ((ip : ℝ) - i)))
    (if i0 ≤ i then
      logb q N i0 + ((i : ℝ) - i0) * logIncr q N i0 -
        cbar / 2 * (((i : ℝ) - i0) * ((i : ℝ) - i0 - 1))
    else
      logb q N i0 - ((i0 : ℝ) - i) * logIncr q N (i0 - 1) -
        cbar / 2 * (((i0 : ℝ) - i) * ((i0 : ℝ) - i - 1)))

/-- The upper bound for `log b_N(i)` on the lobes: the Taylor bound from above anchored at `i₊` (to
the right, curvature `c_R`) or at `i₋` (to the left, curvature `c_L`) (T1 Lemma 4.1 (ii)). -/
noncomputable def logUpper (q : ℝ) (N im ip : ℕ) (cL cR : ℝ) (i : ℕ) : ℝ :=
  if ip < i then
    logb q N ip + ((i : ℝ) - ip) * logIncr q N ip - cR / 2 * (((i : ℝ) - ip) * ((i : ℝ) - ip - 1))
  else
    logb q N im - ((im : ℝ) - i) * logIncr q N (im - 1) -
      cL / 2 * (((im : ℝ) - i) * ((im : ℝ) - i - 1))

theorem logLower_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N im ip i0 : ℕ} (hmp : im ≤ ip)
    (hpN : ip ≤ N) (hi0N : i0 ≤ N) {cin cbar : ℝ} (hcin : ∀ k, im < k → k < ip → cin ≤ curvN N k)
    (hcbar : ∀ k, (i0 < k ∧ k < ip) ∨ (im < k ∧ k < i0) → curvN N k ≤ cbar) {i : ℕ}
    (hi1 : im ≤ i) (hi2 : i ≤ ip) : logLower q N im ip i0 cin cbar i ≤ logb q N i := by
  unfold logLower
  apply max_le
  · rcases eq_or_lt_of_le hmp with h | h
    · subst h
      have : i = im := le_antisymm hi2 hi1
      subst this
      simp
    · exact logb_chord_ge hq0 hq1 h hpN cin hcin i hi1 hi2
  · split_ifs with hle
    · exact logb_taylor_ge hq0 hq1 hle (by omega) cbar fun k hk1 hk2 =>
        hcbar k (Or.inl ⟨hk1, by omega⟩)
    · exact logb_taylor_left_ge hq0 hq1 (by omega) hi0N cbar fun k hk1 hk2 =>
        hcbar k (Or.inr ⟨by omega, hk2⟩)

theorem logb_le_logUpper {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N im ip : ℕ} (hmp : im ≤ ip)
    (hpN : ip ≤ N) {cL cR : ℝ} (hcR : ∀ k, ip < k → k < N → cR ≤ curvN N k)
    (hcL : ∀ k, 0 < k → k < im → cL ≤ curvN N k) {i : ℕ} (hiN : i ≤ N)
    (hlobe : i < im ∨ ip < i) : logb q N i ≤ logUpper q N im ip cL cR i := by
  unfold logUpper
  split_ifs with h
  · exact logb_taylor_le hq0 hq1 h.le hiN cR fun k hk1 hk2 => hcR k hk1 (by omega)
  · have him : i < im := by omega
    exact logb_taylor_left_le hq0 hq1 him.le (by omega) cL fun k hk1 hk2 => hcL k (by omega) hk2

/-! ## T1's explicit replacement weight -/

/-- T1's explicit replacement weight on the lattice `[0, N]` (`N = M + 2`): `exp(logLower)` on
`[i₋, i₊]` and `exp(logUpper)` on the lobes, divided by `N(N − 1)v²`. -/
noncomputable def weightRepNat (q : ℝ) (M im ip i0 : ℕ) (cin cbar cL cR : ℝ) (i : ℕ) : ℝ :=
  (if im ≤ i ∧ i ≤ ip then Real.exp (logLower q (M + 2) im ip i0 cin cbar i)
    else Real.exp (logUpper q (M + 2) im ip cL cR i)) /
    (((M : ℝ) + 2) * ((M : ℝ) + 1) * (q * (1 - q)) ^ 2)

/-- T1's explicit replacement weight `W̄` on `ℤ` (zero off `[0, N]`, where `W = 0`). -/
noncomputable def weightRep (q : ℝ) (M im ip i0 : ℕ) (cin cbar cL cR : ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i ∧ i ≤ (M : ℤ) + 2 then weightRepNat q M im ip i0 cin cbar cL cR i.toNat else 0

theorem weightRep_le_kappaWeight {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {M im ip i0 : ℕ}
    (hmp : im ≤ ip) (hpN : ip ≤ M + 2) (hi0N : i0 ≤ M + 2) {cin cbar cL cR : ℝ}
    (hcin : ∀ k, im < k → k < ip → cin ≤ curvN (M + 2) k)
    (hcbar : ∀ k, (i0 < k ∧ k < ip) ∨ (im < k ∧ k < i0) → curvN (M + 2) k ≤ cbar) {i : ℤ}
    (hi1 : (im : ℤ) ≤ i) (hi2 : i ≤ ip) :
    weightRep q M im ip i0 cin cbar cL cR i ≤ kappaWeight q M i := by
  have hi0 : 0 ≤ i := le_trans (Int.natCast_nonneg _) hi1
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k := ⟨i.toNat, (Int.toNat_of_nonneg hi0).symm⟩
  have hk1 : im ≤ k := by exact_mod_cast hi1
  have hk2 : k ≤ ip := by exact_mod_cast hi2
  have hkN : k ≤ M + 2 := le_trans hk2 hpN
  have hb := binom_pos hq0 hq1 hkN
  unfold weightRep weightRepNat kappaWeight
  rw [if_pos ⟨by positivity, by exact_mod_cast hkN⟩, Int.toNat_natCast, if_pos ⟨hk1, hk2⟩]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc Real.exp (logLower q (M + 2) im ip i0 cin cbar k)
      ≤ Real.exp (logb q (M + 2) k) :=
        Real.exp_le_exp.mpr (logLower_le hq0 hq1 hmp hpN hi0N hcin hcbar hk1 hk2)
    _ = binom (M + 2) q (k : ℤ) := Real.exp_log hb

theorem kappaWeight_le_weightRep {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {M im ip i0 : ℕ}
    (hmp : im ≤ ip) (hpN : ip ≤ M + 2) {cin cbar cL cR : ℝ}
    (hcR : ∀ k, ip < k → k < M + 2 → cR ≤ curvN (M + 2) k)
    (hcL : ∀ k, 0 < k → k < im → cL ≤ curvN (M + 2) k) {i : ℤ} (h0 : 0 ≤ i)
    (hN : i ≤ (M : ℤ) + 2) (hlobe : i < im ∨ (ip : ℤ) < i) :
    kappaWeight q M i ≤ weightRep q M im ip i0 cin cbar cL cR i := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k := ⟨i.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hkN : k ≤ M + 2 := by exact_mod_cast hN
  have hlobe' : k < im ∨ ip < k := by omega
  have hb := binom_pos hq0 hq1 hkN
  unfold weightRep weightRepNat kappaWeight
  rw [if_pos ⟨by positivity, hN⟩, Int.toNat_natCast, if_neg (by omega)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc binom (M + 2) q (k : ℤ) = Real.exp (logb q (M + 2) k) := (Real.exp_log hb).symm
    _ ≤ Real.exp (logUpper q (M + 2) im ip cL cR k) :=
        Real.exp_le_exp.mpr (logb_le_logUpper hq0 hq1 hmp hpN hcR hcL hkN hlobe')

theorem weightRep_off {q : ℝ} {M im ip i0 : ℕ} {cin cbar cL cR : ℝ} {i : ℤ}
    (hoff : i < 0 ∨ (M : ℤ) + 2 < i) :
    weightRep q M im ip i0 cin cbar cL cR i = kappaWeight q M i := by
  unfold weightRep kappaWeight
  rw [if_neg (by omega)]
  rcases hoff with h | h
  · rw [binom_of_neg h, zero_div]
  · rw [binom_of_gt (by push_cast; omega), zero_div]

/-! ## T1 Proposition 4.3 -/

/-- **T1 Proposition 4.3 (all `q`), pointwise form.**  Let `0 < q < 1`, `N = M + 2`, lattice points
`i₋ ≤ i₊ ≤ N` with `Q_κ ≥ 0` on `[i₋, i₊]` and `Q_κ ≤ 0` on the lobes `[0, i₋) ∪ (i₊, N]`, an anchor
`i₀ ≤ N` (T1: the mode), and curvature constants `c_in ≤ c_N` on `(i₋, i₊)`, `c̄ ≥ c_N` on
`(i₀, i₊) ∪ (i₋, i₀)`, `c_R ≤ c_N` on `(i₊, N)`, `c_L ≤ c_N` on `(0, i₋)` (T1's min/max over these
ranges are such constants).  Then for every integer `i`: `Φ_M(i) ≤ Φ̄_M(i)` with `Ŵ = weightRep`. -/
theorem prop43 {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (μ c : ℝ) {M im ip i0 : ℕ}
    {cin cbar cL cR : ℝ} (hmp : im ≤ ip) (hpN : ip ≤ M + 2) (hi0N : i0 ≤ M + 2)
    (hcin : ∀ k, im < k → k < ip → cin ≤ curvN (M + 2) k)
    (hcbar : ∀ k, (i0 < k ∧ k < ip) ∨ (im < k ∧ k < i0) → curvN (M + 2) k ≤ cbar)
    (hcR : ∀ k, ip < k → k < M + 2 → cR ≤ curvN (M + 2) k)
    (hcL : ∀ k, 0 < k → k < im → cL ≤ curvN (M + 2) k)
    (hQin : ∀ i : ℤ, (im : ℤ) ≤ i → i ≤ ip → 0 ≤ kappaQuad q M i)
    (hQout : ∀ i : ℤ, 0 ≤ i → i ≤ (M : ℤ) + 2 → (i < im ∨ (ip : ℤ) < i) → kappaQuad q M i ≤ 0)
    (i : ℤ) :
    lossPhi q μ c M i ≤ lossPhiRep q μ c M (weightRep q M im ip i0 cin cbar cL cR) i := by
  by_cases hoff : i < 0 ∨ (M : ℤ) + 2 < i
  · unfold lossPhi lossPhiRep
    rw [weightRep_off hoff]
  push_neg at hoff
  obtain ⟨h0, hN⟩ := hoff
  apply lossPhi_le_lossPhiRep
  by_cases hin : (im : ℤ) ≤ i ∧ i ≤ ip
  · exact Or.inl ⟨hQin i hin.1 hin.2,
      weightRep_le_kappaWeight hq0 hq1 hmp hpN hi0N hcin hcbar hin.1 hin.2⟩
  · have hlobe : i < im ∨ (ip : ℤ) < i := by omega
    exact Or.inr ⟨hQout i h0 hN hlobe,
      kappaWeight_le_weightRep hq0 hq1 hmp hpN hcR hcL h0 hN hlobe⟩

/-- **T1 Proposition 4.3: `L_M ≤ L̄_M`.**  Under the hypotheses of `prop43`, every upper bound `L̄`
of `Φ̄_M` over the integers is an upper bound of `Φ_M` over the integers. -/
theorem prop43_max {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (μ c : ℝ) {M im ip i0 : ℕ}
    {cin cbar cL cR : ℝ} (hmp : im ≤ ip) (hpN : ip ≤ M + 2) (hi0N : i0 ≤ M + 2)
    (hcin : ∀ k, im < k → k < ip → cin ≤ curvN (M + 2) k)
    (hcbar : ∀ k, (i0 < k ∧ k < ip) ∨ (im < k ∧ k < i0) → curvN (M + 2) k ≤ cbar)
    (hcR : ∀ k, ip < k → k < M + 2 → cR ≤ curvN (M + 2) k)
    (hcL : ∀ k, 0 < k → k < im → cL ≤ curvN (M + 2) k)
    (hQin : ∀ i : ℤ, (im : ℤ) ≤ i → i ≤ ip → 0 ≤ kappaQuad q M i)
    (hQout : ∀ i : ℤ, 0 ≤ i → i ≤ (M : ℤ) + 2 → (i < im ∨ (ip : ℤ) < i) → kappaQuad q M i ≤ 0)
    (Lbar : ℝ)
    (hL : ∀ i : ℤ, lossPhiRep q μ c M (weightRep q M im ip i0 cin cbar cL cR) i ≤ Lbar) (i : ℤ) :
    lossPhi q μ c M i ≤ Lbar :=
  le_trans (prop43 hq0 hq1 μ c hmp hpN hi0N hcin hcbar hcR hcL hQin hQout i) (hL i)

/-- **The explicit fibre bound (T1 Theorem 3.1 + Proposition 4.3).**  Under the hypotheses of
`prop43`, if `Φ̄_M ≤ L̄` on the integers then `P(M) − L̄ ≤ κ(M, j) + cδ + aμ̃δ²` for every integer
`j` (`δ = j − qM`): `P(M) − L̄` is a pointwise fibre bound with `ν = aμ̃`. -/
theorem prop43_fibre {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (μ c : ℝ) {M im ip i0 : ℕ}
    {cin cbar cL cR : ℝ} (hmp : im ≤ ip) (hpN : ip ≤ M + 2) (hi0N : i0 ≤ M + 2)
    (hcin : ∀ k, im < k → k < ip → cin ≤ curvN (M + 2) k)
    (hcbar : ∀ k, (i0 < k ∧ k < ip) ∨ (im < k ∧ k < i0) → curvN (M + 2) k ≤ cbar)
    (hcR : ∀ k, ip < k → k < M + 2 → cR ≤ curvN (M + 2) k)
    (hcL : ∀ k, 0 < k → k < im → cL ≤ curvN (M + 2) k)
    (hQin : ∀ i : ℤ, (im : ℤ) ≤ i → i ≤ ip → 0 ≤ kappaQuad q M i)
    (hQout : ∀ i : ℤ, 0 ≤ i → i ≤ (M : ℤ) + 2 → (i < im ∨ (ip : ℤ) < i) → kappaQuad q M i ≤ 0)
    (Lbar : ℝ)
    (hL : ∀ i : ℤ, lossPhiRep q μ c M (weightRep q M im ip i0 cin cbar cL cR) i ≤ Lbar) (j : ℤ) :
    chebP q μ c M - Lbar ≤
      kappa q M j + c * ((j : ℝ) - q * M) + lossA q * μ * ((j : ℝ) - q * M) ^ 2 := by
  rw [loss_form hq0.ne' hq1.ne μ c M j]
  linarith [prop43_max hq0 hq1 μ c hmp hpN hi0N hcin hcbar hcR hcL hQin hQout Lbar hL (j + 1)]

end Erdos993Lean.Analytic.NoValley
