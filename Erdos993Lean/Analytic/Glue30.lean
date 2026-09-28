import Erdos993Lean.Analytic.Assembly
import Erdos993Lean.Analytic.Family
import Erdos993Lean.Analytic.Density.Main

/-!
# The certified profile: O4 reduced to the atlas, and the state of the route

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  For the certified profile `Profile30.P`:

* `Db_bounds`, `θb_bounds`: the profile's caps meet the hypotheses of the large-mean no-valley theorem
  (`D ≤ 8/5`; `θ ≤ 7/10` for `q ∈ [3/8, 8/13]`, `θ ≤ 1` outside);
* `tail_third`: the profile's tail function gives `P(M < m/3) ≤ e^{−m/30}` for `m ≥ 400` (per band:
  `1 + λ_{i+1} ≤ e^{3ℓ_{i,0} − 1/10}`, checked by an exact Taylor lower sum, `third_check`);
* `thresholdNoValley_profile30`: O4 for the profile from the atlas numerics on `m < 400` alone (the large-mean
  theorem covers `m ≥ 400`);
* `erdos993_of_profile30`: **Erdős #993 from O1, O2, O3 for the profile and the atlas numerics** (O5 is proved:
  `densityBound_profile30`); `coreUnion_unimodal_of_profile30`: the same for Sol's core-union family with the
  family O1/O2.
-/

namespace Erdos993Lean.Analytic.Glue30

open Profile30 Density

theorem Dt_bounds : ∀ i < 30, (0 : ℚ) ≤ Dt.getD i (8/5) ∧ Dt.getD i (8/5) ≤ 8/5 := by decide +kernel

theorem θt_low : ∀ i < 6, θt.getD i 1 = 1 := by decide +kernel

theorem θt_mid : ∀ i < 25, 6 ≤ i → (0 : ℚ) ≤ θt.getD i 1 ∧ θt.getD i 1 ≤ 7/10 := by decide +kernel

theorem θt_high : ∀ i < 30, 25 ≤ i → θt.getD i 1 = 1 := by decide +kernel

theorem edges_six : edges.getD 6 0 = 3/5 := by decide +kernel

theorem edges_twentyfive : edges.getD 25 0 = 8/5 := by decide +kernel

theorem tvals_zero : tvals.getD 0 0 = 0 := by decide +kernel

/-- Per band `i`: `x = 3 ℓ_{i,0} − 1/10 ≥ 0` and `1 + λ_{i+1} ≤ Σ_{j < 14} x^j/j!` (exact). -/
theorem third_check : ∀ i < 30, (0 : ℚ) ≤ 3 * (rates.getD i []).getD 0 0 - 1/10 ∧
    1 + edges.getD (i + 1) 0 ≤ ∑ j ∈ Finset.range 14,
      (3 * (rates.getD i []).getD 0 0 - 1/10) ^ j / (j.factorial : ℚ) := by decide +kernel

theorem Db_bounds {t : ℝ} (hR : InRange t) : 0 ≤ Profile30.P.Db t ∧ Profile30.P.Db t ≤ 8 / 5 := by
  have hi := (bandOf_spec hR).1
  obtain ⟨h0, h1⟩ := Dt_bounds _ hi
  show (0 : ℝ) ≤ ((Dt.getD (bandOf t) (8/5) : ℚ) : ℝ) ∧ ((Dt.getD (bandOf t) (8/5) : ℚ) : ℝ) ≤ 8 / 5
  have h0' := (Rat.cast_le (K := ℝ)).mpr h0
  have h1' := (Rat.cast_le (K := ℝ)).mpr h1
  push_cast at h0' h1'
  exact ⟨h0', h1'⟩

theorem θb_bounds {t : ℝ} (hR : InRange t) : 0 ≤ Profile30.P.θb t ∧
    ((3 / 8 ≤ actQ t ∧ actQ t ≤ 8 / 13 ∧ Profile30.P.θb t ≤ 7 / 10) ∨
      ((actQ t ≤ 3 / 8 ∨ 8 / 13 ≤ actQ t) ∧ Profile30.P.θb t ≤ 1)) := by
  obtain ⟨hi, -, hlo, hhi⟩ := bandOf_spec hR
  have ht0 : 0 ≤ t := le_trans (by norm_num) hR.1
  have hθdef : Profile30.P.θb t = ((θt.getD (bandOf t) 1 : ℚ) : ℝ) := rfl
  have hq35 : actQ (3 / 5 : ℝ) = 3 / 8 := by unfold actQ; norm_num
  have hq85 : actQ (8 / 5 : ℝ) = 8 / 13 := by unfold actQ; norm_num
  have e6 : edgeR 6 = 3 / 5 := by unfold edgeR; rw [edges_six]; norm_num
  have e25 : edgeR 25 = 8 / 5 := by unfold edgeR; rw [edges_twentyfive]; norm_num
  rcases lt_or_ge (bandOf t) 6 with h6 | h6
  · have hθ := θt_low _ h6
    have hle : t ≤ 3 / 5 := by
      rw [← e6]; exact le_trans hhi (edgeR_le (by omega) (by norm_num))
    refine ⟨by rw [hθdef, hθ]; norm_num, Or.inr ⟨Or.inl ?_, by rw [hθdef, hθ]; norm_num⟩⟩
    calc actQ t ≤ actQ (3 / 5) := actQ_le_actQ ht0 hle
      _ = 3 / 8 := hq35
  · rcases lt_or_ge (bandOf t) 25 with h25 | h25
    · obtain ⟨hθ0, hθ1⟩ := θt_mid _ h25 h6
      have hge : 3 / 5 ≤ t := by
        rw [← e6]; exact le_trans (edgeR_le h6 (by omega)) hlo
      have hle : t ≤ 8 / 5 := by
        rw [← e25]; exact le_trans hhi (edgeR_le (by omega) (by norm_num))
      have hθ0' := (Rat.cast_le (K := ℝ)).mpr hθ0
      have hθ1' := (Rat.cast_le (K := ℝ)).mpr hθ1
      push_cast at hθ0' hθ1'
      refine ⟨by rw [hθdef]; exact hθ0', Or.inl ⟨?_, ?_, by rw [hθdef]; exact hθ1'⟩⟩
      · calc (3 / 8 : ℝ) = actQ (3 / 5) := hq35.symm
          _ ≤ actQ t := actQ_le_actQ (by norm_num) hge
      · calc actQ t ≤ actQ (8 / 5) := actQ_le_actQ ht0 hle
          _ = 8 / 13 := hq85
    · have hθ := θt_high _ hi h25
      have hge : 8 / 5 ≤ t := by
        rw [← e25]; exact le_trans (edgeR_le h25 (by omega)) hlo
      refine ⟨by rw [hθdef, hθ]; norm_num, Or.inr ⟨Or.inr ?_, by rw [hθdef, hθ]; norm_num⟩⟩
      calc (8 / 13 : ℝ) = actQ (8 / 5) := hq85.symm
        _ ≤ actQ t := actQ_le_actQ (by norm_num) hge

/-- **The third-mean tail of the profile**: for `m ≥ 400` the tail value at `r = ⌈m/3⌉ − 1` is at most
`e^{−m/30}`. -/
theorem tail_third {t : ℝ} (hR : InRange t) {m : ℝ} (hm : 400 ≤ m) :
    ∃ r : ℕ, r < Profile30.P.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧
      Profile30.P.Tb t m r ≤ Real.exp (-(m / 30)) := by
  obtain ⟨hi, -, -, -⟩ := bandOf_spec hR
  obtain ⟨hx0, hsum⟩ := third_check (bandOf t) hi
  set ℓ : ℚ := (rates.getD (bandOf t) []).getD 0 0 with hℓ
  set h : ℚ := edges.getD (bandOf t + 1) 0 with hh
  have hm3 : 0 < m / 3 := by linarith
  have hc1 : 1 ≤ ⌈m / 3⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hm3).ne'
  refine ⟨⌈m / 3⌉₊ - 1, ?_, ?_, ?_⟩
  · show ⌈m / 3⌉₊ - 1 < ⌈m⌉₊ + 1
    have : ⌈m / 3⌉₊ ≤ ⌈m⌉₊ := Nat.ceil_mono (by linarith)
    omega
  · have : ((⌈m / 3⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈m / 3⌉₊ : ℝ) := by
      rw [Nat.cast_sub hc1]; ring
    rw [this]
    exact Nat.le_ceil _
  · -- the tail function is at most its `t = 0` term
    set r : ℕ := ⌈m / 3⌉₊ - 1 with hr
    have hTb : Profile30.P.Tb t m r ≤ tailTerm t m r 0 := by
      show tailFn t m r ≤ tailTerm t m r 0
      unfold tailFn
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    refine le_trans hTb ?_
    have hterm : tailTerm t m r 0 = Real.exp (-((ℓ : ℝ) * m)) * (1 + (h : ℝ)) ^ r := by
      unfold tailTerm ell hiEdge
      rw [tvals_zero]
      simp only [Rat.cast_zero, mul_zero, add_zero, div_one]
      rfl
    rw [hterm]
    -- `1 + h ≤ e^x`, `x = 3ℓ − 1/10`
    have hx0R : (0 : ℝ) ≤ 3 * (ℓ : ℝ) - 1 / 10 := by
      have := (Rat.cast_le (K := ℝ)).mpr hx0
      push_cast at this
      exact this
    have hexp : (1 + (h : ℝ)) ≤ Real.exp (3 * (ℓ : ℝ) - 1 / 10) := by
      have hs := Real.sum_le_exp_of_nonneg hx0R 14
      have hsumR := (Rat.cast_le (K := ℝ)).mpr hsum
      push_cast at hsumR
      linarith
    have hh0 : (0 : ℝ) ≤ h := by
      have := edges_lt_succ 0 (by norm_num)
      have hpos : (0 : ℚ) ≤ edges.getD (bandOf t + 1) 0 := by
        have h1 : edges.getD 0 0 ≤ edges.getD (bandOf t + 1) 0 :=
          (edgesQ_lt (Nat.succ_pos _) (by omega)).le
        rw [edges_zero] at h1
        linarith
      have := (Rat.cast_le (K := ℝ)).mpr hpos
      push_cast at this
      exact this
    have h1h : (0 : ℝ) < 1 + h := by linarith
    have hlog : Real.log (1 + (h : ℝ)) ≤ 3 * (ℓ : ℝ) - 1 / 10 := by
      rw [Real.log_le_iff_le_exp h1h]; exact hexp
    have hlog0 : 0 ≤ Real.log (1 + (h : ℝ)) := Real.log_nonneg (by linarith)
    have hrm : (r : ℝ) ≤ m / 3 := by
      have hlt : (⌈m / 3⌉₊ : ℝ) < m / 3 + 1 := Nat.ceil_lt_add_one hm3.le
      have : (r : ℝ) = (⌈m / 3⌉₊ : ℝ) - 1 := by rw [hr, Nat.cast_sub hc1]; ring
      linarith
    have hpow : (1 + (h : ℝ)) ^ r = Real.exp ((r : ℝ) * Real.log (1 + (h : ℝ))) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos h1h r)]
    rw [hpow, ← Real.exp_add, Real.exp_le_exp]
    have : (r : ℝ) * Real.log (1 + (h : ℝ)) ≤ m / 3 * (3 * (ℓ : ℝ) - 1 / 10) :=
      mul_le_mul hrm hlog hlog0 hm3.le
    nlinarith

/-- **O4 for the certified profile from the atlas numerics alone**: the large-mean theorem covers `m ≥ 400`. -/
theorem thresholdNoValley_profile30
    (hsmall : ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m)) :
    ThresholdNoValley Profile30.P :=
  thresholdNoValley_of_split hsmall (fun _ hR => Db_bounds hR) (fun _ hR => θb_bounds hR)
    (fun _ hR _ hm => tail_third hR hm)

/-- **The state of the route**: Erdős #993 from O1, O2 and O3 for the certified profile and the atlas
numerics for `m < 400` (O5 and the large-mean part of O4 are proved; standard axioms). -/
theorem erdos993_of_profile30 (h1 : VarianceBound Profile30.P) (h2 : VarianceRatioBound Profile30.P)
    (h3 : TailBound Profile30.P)
    (hsmall : ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m)) :
    Erdos993Statement :=
  erdos993_of_analytic_inputs_std
    ⟨h1, h2, h3, thresholdNoValley_profile30 hsmall, densityBound_profile30⟩

/-- **Sol's core-union family**, same state: from the family O1/O2, O3 and the atlas numerics. -/
theorem coreUnion_unimodal_of_profile30
    (h1 : VarianceBoundOn CoreUnion Profile30.P) (h2 : VarianceRatioBoundOn CoreUnion Profile30.P)
    (h3 : TailBound Profile30.P)
    (hsmall : ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m))
    (F : FiniteForest) (hF : CoreUnion F) : independenceSequenceUnimodal F :=
  coreUnion_unimodal_of_inputs h1 h2 h3 (thresholdNoValley_profile30 hsmall) densityBound_profile30 F hF

end Erdos993Lean.Analytic.Glue30
