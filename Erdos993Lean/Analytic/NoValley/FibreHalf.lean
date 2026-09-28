import Mathlib
import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.NoValley.Identities
import Erdos993Lean.Analytic.NoValley.LogConcave

/-!
# The explicit fibre bound at `q = 1/2` (T1 Proposition 4.2; E4)

Source: T1 (`ProofRuns/2026-09-27_zhang_review/reports/T1.md`), §4, Proposition 4.2 and its proof
(lines 184–199).  At `q = 1/2` (`λ = 1`) the valley kernel is `f_C`, and with `N = M + 2`,
`G = N/4`, lattice points `u = i − N/2` (`i ∈ ℤ`, i.e. `u ∈ ℤ + N/2`) and
`W(u) = 16 b_N(N/2 + u)/(N(N − 1))` (= `kappaWeight (1/2) M i`), Lemma 1.1 (b) reads
`f_C = W(u)(G − u²)` (`fC_half`).

* `Δ_* = max{u ≥ 0 on the lattice : u² ≤ G}` is `i_* − N/2` for the lattice index `i_*` with
  `N ≤ 2i_*`, `(2i_* − N)² ≤ N < (2i_* + 2 − N)²` (`IsIStar`; it exists, `exists_isIStar`);
* `ρ = 2/(N + 1)` (`rhoN`), the minimal chord slope;
* `b̃ = W(Δ_*) e^{−ρ(G − Δ_*²)}` (`bTilde`), `b̂ = W(Δ_* + 1) e^{ρ((Δ_* + 1)² − G)}` (`bHat`);
* `ψ(r) = sup_{s ≥ 0} s(e^{−s} − r)` (`psiLoss`), `ψ̃(R) = sup_{z ≥ 0} z(R − e^z)` (`psiGain`).

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

* `psiLoss_eq_zero` (`ψ(r) = 0` for `r ≥ 1`), `psiLoss_le_sq` (`ψ(r) ≤ (1 − r)²/(4r)`),
  `psiLoss_le_exp` (`ψ(r) ≤ 1/e`); `psiGain_eq_zero` (`ψ̃(R) = 0` for `R ≤ 1`),
  `psiGain_le_sq` (`ψ̃(R) ≤ (R − 1)²/4`).
* `two_mul_div_le_log`: `log((A + x)/(A − x)) ≥ 2x/A` for `0 ≤ x < A` (the chord slopes of `−log W`
  in `u²` are `σ(u) = (1/x) log((A + x)/(A − x)) ≥ ρ`, `A = N + 1`, `x = 2u + 1`).
* **T1 Proposition 4.2** (`bHat_le_bTilde`, `prop42`): `b̂ ≤ b̃`, and for `μ > 0` and every
  integer `j` (`u = j + 1 − N/2`),
  `f_C(M, j) + μu² ≥ μG − (b̂/ρ) ψ(μ/b̂) − (b̃/ρ) ψ̃(μ/b̃)`,
  i.e. `H_μ(M) = min_u [f_C + μu²] ≥ μG − (b̂/ρ)ψ(μ/b̂) − (b̃/ρ)ψ̃(μ/b̃)`.
* `prop42_fibre`: the same bound as the pointwise condition of `ExplicitThreshold` at `q = 1/2`
  (`κ = f_C`, `δ = u`, `c = 0`, `ν = μ`).
-/

namespace Erdos993Lean.Analytic.NoValley

open Finset

/-! ## The functions `ψ` and `ψ̃` -/

/-- `ψ(r) = sup_{s ≥ 0} s(e^{−s} − r)`. -/
noncomputable def psiLoss (r : ℝ) : ℝ :=
  ⨆ s : Set.Ici (0 : ℝ), (s : ℝ) * (Real.exp (-(s : ℝ)) - r)

/-- `ψ̃(R) = sup_{z ≥ 0} z(R − e^z)`. -/
noncomputable def psiGain (R : ℝ) : ℝ :=
  ⨆ z : Set.Ici (0 : ℝ), (z : ℝ) * (R - Real.exp (z : ℝ))

theorem mul_exp_neg_le_exp_neg_one (s : ℝ) : s * Real.exp (-s) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (s - 1)
  rw [sub_add_cancel] at h
  have hpos := Real.exp_pos (-s)
  calc s * Real.exp (-s) ≤ Real.exp (s - 1) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

theorem psiLoss_term_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    s * (Real.exp (-s) - r) ≤ Real.exp (-1) := by
  have h1 := mul_exp_neg_le_exp_neg_one s
  have h2 := mul_nonneg hs hr
  nlinarith

theorem le_psiLoss {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) : s * (Real.exp (-s) - r) ≤ psiLoss r := by
  have hb : BddAbove (Set.range fun s : Set.Ici (0 : ℝ) => (s : ℝ) * (Real.exp (-(s : ℝ)) - r)) :=
    ⟨Real.exp (-1), by rintro _ ⟨s, rfl⟩; exact psiLoss_term_le hr s.2⟩
  exact le_ciSup (f := fun s : Set.Ici (0 : ℝ) => (s : ℝ) * (Real.exp (-(s : ℝ)) - r)) hb ⟨s, hs⟩

theorem psiLoss_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ psiLoss r := by
  have := le_psiLoss hr (le_refl 0)
  simpa using this

theorem psiLoss_le_exp {r : ℝ} (hr : 0 ≤ r) : psiLoss r ≤ Real.exp (-1) := by
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.self_mem_Ici⟩⟩
  exact ciSup_le fun s => psiLoss_term_le hr s.2

theorem psiLoss_eq_zero {r : ℝ} (hr : 1 ≤ r) : psiLoss r = 0 := by
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.self_mem_Ici⟩⟩
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨s, hs⟩
    have hs' : 0 ≤ s := hs
    have : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact mul_nonpos_of_nonneg_of_nonpos hs' (by linarith)
  · exact psiLoss_nonneg (by linarith)

theorem psiLoss_le_sq {r : ℝ} (hr : 0 < r) : psiLoss r ≤ (1 - r) ^ 2 / (4 * r) := by
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.self_mem_Ici⟩⟩
  apply ciSup_le
  rintro ⟨s, hs⟩
  have hs' : 0 ≤ s := hs
  show s * (Real.exp (-s) - r) ≤ (1 - r) ^ 2 / (4 * r)
  set E := Real.exp (-s) with hE
  have hE1 : E * (1 + s) ≤ 1 := by
    have h := Real.add_one_le_exp s
    have hpos := Real.exp_pos (-s)
    calc E * (1 + s) ≤ E * Real.exp s := mul_le_mul_of_nonneg_left (by linarith) hpos.le
      _ = 1 := by rw [hE, ← Real.exp_add]; simp
  have hsE : s * E * (1 + s) ≤ s := by nlinarith
  have key : (4 * r * (s * (E - r))) * (1 + s) ≤ (1 - r) ^ 2 * (1 + s) := by
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hsE), sq_nonneg (2 * r * s - (1 - r)),
      mul_nonneg hs' (sq_nonneg (1 - r))]
  have key' := le_of_mul_le_mul_right key (by linarith : (0 : ℝ) < 1 + s)
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem psiGain_term_le (R : ℝ) {z : ℝ} (hz : 0 ≤ z) : z * (R - Real.exp z) ≤ (R - 1) ^ 2 / 4 := by
  have h := Real.add_one_le_exp z
  have h2 := mul_le_mul_of_nonneg_left h hz
  nlinarith [sq_nonneg (2 * z - (R - 1))]

theorem le_psiGain (R : ℝ) {z : ℝ} (hz : 0 ≤ z) : z * (R - Real.exp z) ≤ psiGain R := by
  have hb : BddAbove (Set.range fun z : Set.Ici (0 : ℝ) => (z : ℝ) * (R - Real.exp (z : ℝ))) :=
    ⟨(R - 1) ^ 2 / 4, by rintro _ ⟨z, rfl⟩; exact psiGain_term_le R z.2⟩
  exact le_ciSup (f := fun z : Set.Ici (0 : ℝ) => (z : ℝ) * (R - Real.exp (z : ℝ))) hb ⟨z, hz⟩

theorem psiGain_nonneg (R : ℝ) : 0 ≤ psiGain R := by
  have := le_psiGain R (le_refl 0)
  simpa using this

theorem psiGain_le_sq (R : ℝ) : psiGain R ≤ (R - 1) ^ 2 / 4 := by
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.self_mem_Ici⟩⟩
  exact ciSup_le fun z => psiGain_term_le R z.2

theorem psiGain_eq_zero {R : ℝ} (hR : R ≤ 1) : psiGain R = 0 := by
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.self_mem_Ici⟩⟩
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨z, hz⟩
    have hz' : 0 ≤ z := hz
    have : 1 ≤ Real.exp z := Real.one_le_exp hz'
    exact mul_nonpos_of_nonneg_of_nonpos hz' (by linarith)
  · exact psiGain_nonneg R

/-! ## The chord slope of `−log W` -/

/-- `log((A + x)/(A − x)) ≥ 2x/A` for `0 ≤ x < A` (from the series of `log(1 + y) − log(1 − y)`). -/
theorem two_mul_div_le_log {x A : ℝ} (hx : 0 ≤ x) (hxA : x < A) :
    2 * x / A ≤ Real.log ((A + x) / (A - x)) := by
  have hA : 0 < A := lt_of_le_of_lt hx hxA
  set y := x / A with hy
  have hy0 : 0 ≤ y := div_nonneg hx hA.le
  have hy1 : y < 1 := (div_lt_one hA).mpr hxA
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have h0 := le_hasSum hs 0 fun k _ =>
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (pow_nonneg hy0 _)
  norm_num at h0
  have e : (A + x) / (A - x) = (1 + y) / (1 - y) := by
    rw [hy]
    field_simp
  rw [e, Real.log_div (by linarith) (by linarith)]
  have e2 : 2 * x / A = 2 * y := by rw [hy]; ring
  rw [e2]
  exact h0

/-! ## The binomial at `q = 1/2` -/

/-- At `q = 1/2`: `b_N(N − i) = b_N(i)`. -/
theorem binom_half_symm (N : ℕ) (i : ℤ) : binom N (1 / 2) ((N : ℤ) - i) = binom N (1 / 2) i := by
  rcases lt_or_ge i 0 with h | h
  · rw [binom_of_neg h, binom_of_gt (by omega)]
  rcases lt_or_ge (N : ℤ) i with h' | h'
  · rw [binom_of_gt h', binom_of_neg (by omega)]
  lift i to ℕ using h
  have hiN : i ≤ N := by exact_mod_cast h'
  have e : (N : ℤ) - (i : ℤ) = ((N - i : ℕ) : ℤ) := by omega
  rw [e, binom_natCast_of_le _ (Nat.sub_le N i), binom_natCast_of_le _ hiN, Nat.choose_symm hiN,
    Nat.sub_sub_self hiN]
  ring

/-- `ρ = 2/(N + 1)` with `N = M + 2`. -/
noncomputable def rhoN (M : ℕ) : ℝ := 2 / ((M : ℝ) + 3)

theorem rhoN_pos (M : ℕ) : 0 < rhoN M := by
  unfold rhoN
  positivity

/-- **The slope bound at `q = 1/2`.**  For lattice points `N − 1 ≤ 2i` and `i + 1 ≤ N`:
`log b_N(i) − log b_N(i + 1) ≥ ρ (2i + 1 − N)`, i.e. `ρ((u + 1)² − u²)`. -/
theorem half_slope (M i : ℕ) (h1 : M + 2 ≤ 2 * i + 1) (h2 : i + 1 ≤ M + 2) :
    rhoN M * (2 * (i : ℝ) + 1 - ((M : ℝ) + 2)) ≤
      logb (1 / 2) (M + 2) i - logb (1 / 2) (M + 2) (i + 1) := by
  have hb := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by omega : i ≤ M + 2)
  have hb1 := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by omega : i + 1 ≤ M + 2)
  have hr := binom_ratio (M + 2) (1 / 2) i
  have ecast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
  rw [ecast] at hb1
  unfold logb
  rw [ecast, ← Real.log_div hb.ne' hb1.ne']
  have hi1 : (2 * (i : ℝ) + 1 - ((M : ℝ) + 2)) < (M : ℝ) + 3 := by
    have : (i : ℝ) + 1 ≤ (M : ℝ) + 2 := by exact_mod_cast h2
    linarith
  have hi0 : 0 ≤ 2 * (i : ℝ) + 1 - ((M : ℝ) + 2) := by
    have : ((M : ℝ) + 2) ≤ 2 * (i : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hlog := two_mul_div_le_log hi0 hi1
  have e : binom (M + 2) (1 / 2) (i : ℤ) / binom (M + 2) (1 / 2) ((i : ℤ) + 1) =
      ((M : ℝ) + 3 + (2 * (i : ℝ) + 1 - ((M : ℝ) + 2))) /
        ((M : ℝ) + 3 - (2 * (i : ℝ) + 1 - ((M : ℝ) + 2))) := by
    have hden : (M : ℝ) + 3 - (2 * (i : ℝ) + 1 - ((M : ℝ) + 2)) ≠ 0 := by linarith
    rw [div_eq_div_iff hb1.ne' hden]
    push_cast at hr
    linear_combination (-4 : ℝ) * hr
  rw [e]
  unfold rhoN
  calc 2 / ((M : ℝ) + 3) * (2 * (i : ℝ) + 1 - ((M : ℝ) + 2)) =
      2 * (2 * (i : ℝ) + 1 - ((M : ℝ) + 2)) / ((M : ℝ) + 3) := by ring
    _ ≤ _ := hlog

/-- **Telescoped slopes at `q = 1/2`.**  For lattice points `a ≤ b ≤ N` with `N − 1 ≤ 2a`:
`log b_N(a) − log b_N(b) ≥ ρ((b − N/2)² − (a − N/2)²)`. -/
theorem half_tele (M a b : ℕ) (hab : a ≤ b) (hbN : b ≤ M + 2) (ha : M + 2 ≤ 2 * a + 1) :
    rhoN M * (((b : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 - ((a : ℝ) - ((M : ℝ) + 2) / 2) ^ 2) ≤
      logb (1 / 2) (M + 2) a - logb (1 / 2) (M + 2) b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have ih' := ih (by omega)
    have hs := half_slope M b (by omega) hbN
    have e : rhoN M * ((((b + 1 : ℕ) : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 -
        ((a : ℝ) - ((M : ℝ) + 2) / 2) ^ 2) =
        rhoN M * (((b : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 - ((a : ℝ) - ((M : ℝ) + 2) / 2) ^ 2) +
          rhoN M * (2 * (b : ℝ) + 1 - ((M : ℝ) + 2)) := by
      push_cast
      ring
    rw [e]
    linarith

/-- The inside bound on `b_N` at `q = 1/2`: for lattice points `N ≤ 2i`, `i ≤ i_* ≤ N`,
`b_N(i) ≥ b_N(i_*) e^{ρ(Δ_*² − u²)}`. -/
theorem half_inside {M i istar : ℕ} (hi : M + 2 ≤ 2 * i) (hle : i ≤ istar) (hsN : istar ≤ M + 2) :
    binom (M + 2) (1 / 2) (istar : ℤ) *
        Real.exp (rhoN M * (((istar : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 -
          ((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2)) ≤ binom (M + 2) (1 / 2) (i : ℤ) := by
  have ht := half_tele M i istar hle hsN (by omega)
  have hbi := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by omega : i ≤ M + 2)
  have hbs := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hsN
  unfold logb at ht
  have h := Real.exp_le_exp.mpr ht
  rw [Real.exp_sub, Real.exp_log hbi, Real.exp_log hbs, le_div_iff₀ hbs] at h
  rw [mul_comm]
  exact h

/-- The outside bound on `b_N` at `q = 1/2`: for lattice points `i_* + 1 ≤ i ≤ N` with `N ≤ 2i_*`,
`b_N(i) ≤ b_N(i_* + 1) e^{−ρ(u² − (Δ_* + 1)²)}`. -/
theorem half_outside {M i istar : ℕ} (hs : M + 2 ≤ 2 * istar) (hlt : istar + 1 ≤ i)
    (hiN : i ≤ M + 2) :
    binom (M + 2) (1 / 2) (i : ℤ) ≤ binom (M + 2) (1 / 2) ((istar : ℤ) + 1) *
      Real.exp (-(rhoN M * (((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 -
        ((istar : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2))) := by
  have ht := half_tele M (istar + 1) i hlt hiN (by omega)
  have hbi := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hiN
  have hbs := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by omega : istar + 1 ≤ M + 2)
  have ecast : ((istar + 1 : ℕ) : ℤ) = (istar : ℤ) + 1 := by push_cast; ring
  rw [ecast] at hbs
  unfold logb at ht
  rw [ecast] at ht
  push_cast at ht
  have h := Real.exp_le_exp.mpr (show Real.log (binom (M + 2) (1 / 2) (i : ℤ)) ≤
      Real.log (binom (M + 2) (1 / 2) ((istar : ℤ) + 1)) -
        rhoN M * (((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 - ((istar : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2)
      by linarith)
  rw [Real.exp_log hbi, Real.exp_sub, Real.exp_log hbs] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact h

/-! ## The lattice index `i_*` and the constants `b̃`, `b̂` -/

/-- `i_* = N/2 + Δ_*` with `Δ_* = max{u ≥ 0 on the lattice ℤ + N/2 : u² ≤ G}`, `G = N/4`,
`N = M + 2`; in integers: `N ≤ 2i_*` and `(2i_* − N)² ≤ N < (2i_* + 2 − N)²`. -/
def IsIStar (M istar : ℕ) : Prop :=
  M + 2 ≤ 2 * istar ∧ (2 * (istar : ℤ) - ((M : ℤ) + 2)) ^ 2 ≤ (M : ℤ) + 2 ∧
    (M : ℤ) + 2 < (2 * (istar : ℤ) - M) ^ 2

theorem IsIStar.succ_le {M istar : ℕ} (h : IsIStar M istar) : istar + 1 ≤ M + 2 := by
  obtain ⟨-, h2, -⟩ := h
  by_contra hc
  have h3 : (M : ℤ) + 2 ≤ 2 * (istar : ℤ) - ((M : ℤ) + 2) := by omega
  nlinarith

/-- `Δ_*` exists: the lattice index `i_*` is `Nat.findGreatest` of the condition. -/
theorem exists_isIStar (M : ℕ) : ∃ istar, IsIStar M istar := by
  classical
  let P : ℕ → Prop := fun i => M + 2 ≤ 2 * i ∧ (2 * (i : ℤ) - ((M : ℤ) + 2)) ^ 2 ≤ (M : ℤ) + 2
  have hm : P ((M + 3) / 2) := by
    refine ⟨by omega, ?_⟩
    have h01 : 2 * (((M + 3) / 2 : ℕ) : ℤ) - ((M : ℤ) + 2) = 0 ∨
        2 * (((M + 3) / 2 : ℕ) : ℤ) - ((M : ℤ) + 2) = 1 := by omega
    rcases h01 with h | h <;> rw [h] <;> norm_num <;> omega
  have hP : P (Nat.findGreatest P (M + 2)) := Nat.findGreatest_spec (m := (M + 3) / 2) (by omega) hm
  refine ⟨Nat.findGreatest P (M + 2), hP.1, hP.2, ?_⟩
  have hle : Nat.findGreatest P (M + 2) ≤ M + 2 := Nat.findGreatest_le _
  by_contra hc
  push_neg at hc
  by_cases hlt : Nat.findGreatest P (M + 2) + 1 ≤ M + 2
  · refine Nat.findGreatest_is_greatest (by omega : Nat.findGreatest P (M + 2) <
      Nat.findGreatest P (M + 2) + 1) hlt ⟨by omega, ?_⟩
    have e : 2 * ((Nat.findGreatest P (M + 2) + 1 : ℕ) : ℤ) - ((M : ℤ) + 2) =
        2 * ((Nat.findGreatest P (M + 2) : ℕ) : ℤ) - M := by push_cast; ring
    rw [e]
    exact hc
  · have h2 := hP.2
    have h3 : (M : ℤ) + 2 ≤ 2 * ((Nat.findGreatest P (M + 2) : ℕ) : ℤ) - ((M : ℤ) + 2) := by
      omega
    nlinarith

/-- `b̃ = W(Δ_*) e^{−ρ(G − Δ_*²)}` (`W = kappaWeight (1/2) M`, `Δ_* = i_* − N/2`). -/
noncomputable def bTilde (M istar : ℕ) : ℝ :=
  kappaWeight (1 / 2) M istar *
    Real.exp (-(rhoN M * (((M : ℝ) + 2) / 4 - ((istar : ℝ) - ((M : ℝ) + 2) / 2) ^ 2)))

/-- `b̂ = W(Δ_* + 1) e^{ρ((Δ_* + 1)² − G)}`. -/
noncomputable def bHat (M istar : ℕ) : ℝ :=
  kappaWeight (1 / 2) M ((istar : ℤ) + 1) *
    Real.exp (rhoN M * (((istar : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4))

theorem kappaWeight_half_den_pos (M : ℕ) :
    0 < ((M : ℝ) + 2) * ((M : ℝ) + 1) * ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ 2 := by positivity

theorem bTilde_pos {M istar : ℕ} (hs : IsIStar M istar) : 0 < bTilde M istar := by
  unfold bTilde kappaWeight
  have hb := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (by have := hs.succ_le; omega : istar ≤ M + 2)
  exact mul_pos (div_pos hb (kappaWeight_half_den_pos M)) (Real.exp_pos _)

theorem bHat_pos {M istar : ℕ} (hs : IsIStar M istar) : 0 < bHat M istar := by
  unfold bHat kappaWeight
  have hb := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hs.succ_le
  have ecast : ((istar + 1 : ℕ) : ℤ) = (istar : ℤ) + 1 := by push_cast; ring
  rw [ecast] at hb
  exact mul_pos (div_pos hb (kappaWeight_half_den_pos M)) (Real.exp_pos _)

/-- **T1 Proposition 4.2, first claim:** `b̂ ≤ b̃`. -/
theorem bHat_le_bTilde {M istar : ℕ} (hs : IsIStar M istar) : bHat M istar ≤ bTilde M istar := by
  have hsl := half_slope M istar (by have := hs.1; omega) hs.succ_le
  have hbi := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (by have := hs.succ_le; omega : istar ≤ M + 2)
  have hbs := binom_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hs.succ_le
  have ecast : ((istar + 1 : ℕ) : ℤ) = (istar : ℤ) + 1 := by push_cast; ring
  rw [ecast] at hbs
  unfold logb at hsl
  rw [ecast] at hsl
  -- `b(i_* + 1) ≤ b(i_*) e^{−ρ(2i_* + 1 − N)}`
  have h := Real.exp_le_exp.mpr (show Real.log (binom (M + 2) (1 / 2) ((istar : ℤ) + 1)) ≤
      Real.log (binom (M + 2) (1 / 2) (istar : ℤ)) -
        rhoN M * (2 * (istar : ℝ) + 1 - ((M : ℝ) + 2)) by linarith)
  rw [Real.exp_log hbs, Real.exp_sub, Real.exp_log hbi] at h
  have h' : binom (M + 2) (1 / 2) ((istar : ℤ) + 1) ≤ binom (M + 2) (1 / 2) (istar : ℤ) *
      Real.exp (-(rhoN M * (2 * (istar : ℝ) + 1 - ((M : ℝ) + 2)))) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact h
  have h2 : binom (M + 2) (1 / 2) ((istar : ℤ) + 1) *
        Real.exp (rhoN M * (((istar : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4)) ≤
      binom (M + 2) (1 / 2) (istar : ℤ) *
        Real.exp (-(rhoN M * (((M : ℝ) + 2) / 4 - ((istar : ℝ) - ((M : ℝ) + 2) / 2) ^ 2))) := by
    calc _ ≤ binom (M + 2) (1 / 2) (istar : ℤ) *
          Real.exp (-(rhoN M * (2 * (istar : ℝ) + 1 - ((M : ℝ) + 2)))) *
          Real.exp (rhoN M * (((istar : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4)) :=
          mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
      _ = _ := by
          rw [mul_assoc (binom (M + 2) (1 / 2) (istar : ℤ)), ← Real.exp_add]
          congr 2
          ring
  have key := div_le_div_of_nonneg_right h2 (kappaWeight_half_den_pos M).le
  unfold bHat bTilde kappaWeight
  convert key using 1 <;> ring

/-! ## The weight bounds inside and outside `{u² ≤ G}` -/

/-- Inside: for a lattice point with `N ≤ 2k` and `u² ≤ G`, `W(k) ≥ b̃ e^{ρ(G − u²)}`. -/
theorem W_inside_nat {M istar : ℕ} (hs : IsIStar M istar) (k : ℕ) (hk : M + 2 ≤ 2 * k)
    (hin : (2 * (k : ℤ) - ((M : ℤ) + 2)) ^ 2 ≤ (M : ℤ) + 2) :
    bTilde M istar * Real.exp (rhoN M * (((M : ℝ) + 2) / 4 - ((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2)) ≤
      kappaWeight (1 / 2) M k := by
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hkle : k ≤ istar := by
    by_contra hc
    have h1 : 2 * (istar : ℤ) - M ≤ 2 * (k : ℤ) - ((M : ℤ) + 2) := by omega
    have h0 : 0 ≤ 2 * (istar : ℤ) - M := by omega
    nlinarith
  have hsN : istar ≤ M + 2 := by have := IsIStar.succ_le ⟨hs1, hs2, hs3⟩; omega
  have hin' := half_inside (M := M) hk hkle hsN
  have e : bTilde M istar *
      Real.exp (rhoN M * (((M : ℝ) + 2) / 4 - ((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2)) =
      kappaWeight (1 / 2) M (istar : ℤ) * Real.exp (rhoN M * (((istar : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 -
        ((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2)) := by
    unfold bTilde
    rw [mul_assoc (kappaWeight (1 / 2) M (istar : ℤ)), ← Real.exp_add]
    congr 2
    ring
  rw [e]
  unfold kappaWeight
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hin' (kappaWeight_half_den_pos M).le

/-- Outside: for a lattice point with `N ≤ 2k ≤ 2N` and `u² > G`, `W(k) ≤ b̂ e^{−ρ(u² − G)}`. -/
theorem W_outside_nat {M istar : ℕ} (hs : IsIStar M istar) (k : ℕ) (hk : M + 2 ≤ 2 * k)
    (hkN : k ≤ M + 2) (hout : (M : ℤ) + 2 < (2 * (k : ℤ) - ((M : ℤ) + 2)) ^ 2) :
    kappaWeight (1 / 2) M k ≤
      bHat M istar * Real.exp (-(rhoN M * (((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4))) := by
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hklt : istar + 1 ≤ k := by
    by_contra hc
    have h1 : 2 * (k : ℤ) - ((M : ℤ) + 2) ≤ 2 * (istar : ℤ) - ((M : ℤ) + 2) := by omega
    have h0 : 0 ≤ 2 * (k : ℤ) - ((M : ℤ) + 2) := by omega
    nlinarith
  have hout' := half_outside (M := M) hs1 hklt hkN
  have e : bHat M istar *
      Real.exp (-(rhoN M * (((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4))) =
      kappaWeight (1 / 2) M ((istar : ℤ) + 1) * Real.exp (-(rhoN M * (((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 -
        ((istar : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2))) := by
    unfold bHat
    rw [mul_assoc (kappaWeight (1 / 2) M ((istar : ℤ) + 1)), ← Real.exp_add]
    congr 2
    ring
  rw [e]
  have key := div_le_div_of_nonneg_right hout' (kappaWeight_half_den_pos M).le
  unfold kappaWeight
  convert key using 1
  ring

/-- Inside `{u² ≤ G}`, for every integer `i`: `W(i) ≥ b̃ e^{ρ(G − u²)}` (by symmetry for `u < 0`). -/
theorem W_inside {M istar : ℕ} (hs : IsIStar M istar) (i : ℤ)
    (hin : ((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 ≤ ((M : ℝ) + 2) / 4) :
    bTilde M istar * Real.exp (rhoN M * (((M : ℝ) + 2) / 4 - ((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2)) ≤
      kappaWeight (1 / 2) M i := by
  have hinZ : (2 * i - ((M : ℤ) + 2)) ^ 2 ≤ (M : ℤ) + 2 := by
    have : ((2 * i - ((M : ℤ) + 2) : ℤ) : ℝ) ^ 2 ≤ (((M : ℤ) + 2 : ℤ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hN2 : (M : ℤ) + 2 ≤ ((M : ℤ) + 2) ^ 2 := by nlinarith
  have habs : |2 * i - ((M : ℤ) + 2)| ≤ |(M : ℤ) + 2| := sq_le_sq.mp (le_trans hinZ hN2)
  rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (M : ℤ) + 2)] at habs
  obtain ⟨hl, hr⟩ := abs_le.mp habs
  have hi0 : 0 ≤ i := by omega
  rcases le_or_gt ((M : ℤ) + 2) (2 * i) with h2 | h2
  · lift i to ℕ using hi0
    exact W_inside_nat hs i (by exact_mod_cast h2) hinZ
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (M : ℤ) + 2 - i := ⟨((M : ℤ) + 2 - i).toNat, by omega⟩
    have hsym : kappaWeight (1 / 2) M i = kappaWeight (1 / 2) M k := by
      unfold kappaWeight
      have := binom_half_symm (M + 2) i
      push_cast at this
      rw [hk, this]
    have hkr : (k : ℝ) = (M : ℝ) + 2 - i := by exact_mod_cast hk
    have hsq : ((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 = ((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 := by
      rw [hkr]
      ring
    rw [hsym, ← hsq]
    refine W_inside_nat hs k (by omega) ?_
    have e : 2 * (k : ℤ) - ((M : ℤ) + 2) = -(2 * i - ((M : ℤ) + 2)) := by omega
    rw [e, neg_sq]
    exact hinZ

/-- Outside `{u² ≤ G}`, for every integer `i`: `W(i) ≤ b̂ e^{−ρ(u² − G)}` (`W = 0` off `[0, N]`). -/
theorem W_outside {M istar : ℕ} (hs : IsIStar M istar) (i : ℤ)
    (hout : ((M : ℝ) + 2) / 4 < ((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2) :
    kappaWeight (1 / 2) M i ≤
      bHat M istar * Real.exp (-(rhoN M * (((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4))) := by
  have houtZ : (M : ℤ) + 2 < (2 * i - ((M : ℤ) + 2)) ^ 2 := by
    have : (((M : ℤ) + 2 : ℤ) : ℝ) < ((2 * i - ((M : ℤ) + 2) : ℤ) : ℝ) ^ 2 := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hrhs : 0 ≤ bHat M istar *
      Real.exp (-(rhoN M * (((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4))) :=
    mul_nonneg (bHat_pos hs).le (Real.exp_pos _).le
  rcases lt_or_ge i 0 with hneg | hi0
  · unfold kappaWeight
    rw [binom_of_neg hneg, zero_div]
    exact hrhs
  rcases lt_or_ge ((M : ℤ) + 2) i with hbig | hiN
  · unfold kappaWeight
    rw [binom_of_gt (by push_cast; omega), zero_div]
    exact hrhs
  rcases le_or_gt ((M : ℤ) + 2) (2 * i) with h2 | h2
  · lift i to ℕ using hi0
    exact W_outside_nat hs i (by exact_mod_cast h2) (by exact_mod_cast hiN) houtZ
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (M : ℤ) + 2 - i := ⟨((M : ℤ) + 2 - i).toNat, by omega⟩
    have hsym : kappaWeight (1 / 2) M i = kappaWeight (1 / 2) M k := by
      unfold kappaWeight
      have := binom_half_symm (M + 2) i
      push_cast at this
      rw [hk, this]
    have hkr : (k : ℝ) = (M : ℝ) + 2 - i := by exact_mod_cast hk
    have hsq : ((k : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 = ((i : ℝ) - ((M : ℝ) + 2) / 2) ^ 2 := by
      rw [hkr]
      ring
    rw [hsym, ← hsq]
    refine W_outside_nat hs k (by omega) (by omega) ?_
    have e : 2 * (k : ℤ) - ((M : ℤ) + 2) = -(2 * i - ((M : ℤ) + 2)) := by omega
    rw [e, neg_sq]
    exact houtZ

/-! ## T1 Proposition 4.2 -/

/-- `f_C = W(u)(G − u²)` at `q = 1/2` (T1 Lemma 1.1 (b)), `u = j + 1 − N/2`. -/
theorem fC_half (M : ℕ) (j : ℤ) :
    fC (1 / 2) M j = kappaWeight (1 / 2) M (j + 1) *
      (((M : ℝ) + 2) / 4 - ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2) := by
  rw [fC_eq (by norm_num) (by norm_num) M j rfl rfl rfl rfl, kappaWeight]
  ring

/-- The inside step: `(W − μ)t ≥ −(b̃/ρ)ψ̃(μ/b̃)` when `W ≥ b̃ e^{ρt}`, `t ≥ 0`. -/
theorem inside_step {μ W bt ρ t : ℝ} (hρ : 0 < ρ) (hbt : 0 < bt) (ht : 0 ≤ t)
    (hW : bt * Real.exp (ρ * t) ≤ W) : -(bt / ρ * psiGain (μ / bt)) ≤ (W - μ) * t := by
  have hg := le_psiGain (μ / bt) (mul_nonneg hρ.le ht)
  have h1 : (bt * Real.exp (ρ * t) - μ) * t ≤ (W - μ) * t :=
    mul_le_mul_of_nonneg_right (by linarith) ht
  have e : (bt * Real.exp (ρ * t) - μ) * t =
      -(bt / ρ * ((ρ * t) * (μ / bt - Real.exp (ρ * t)))) := by
    field_simp
    ring
  have h2 := mul_le_mul_of_nonneg_left hg (div_nonneg hbt.le hρ.le)
  linarith

/-- The outside step: `(μ − W)τ ≥ −(b̂/ρ)ψ(μ/b̂)` when `W ≤ b̂ e^{−ρτ}`, `τ ≥ 0`, `μ ≥ 0`. -/
theorem outside_step {μ W bh ρ τ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 < ρ) (hbh : 0 < bh) (hτ : 0 ≤ τ)
    (hW : W ≤ bh * Real.exp (-(ρ * τ))) : -(bh / ρ * psiLoss (μ / bh)) ≤ (μ - W) * τ := by
  have hl := le_psiLoss (div_nonneg hμ hbh.le) (mul_nonneg hρ.le hτ)
  have h1 : (μ - bh * Real.exp (-(ρ * τ))) * τ ≤ (μ - W) * τ :=
    mul_le_mul_of_nonneg_right (by linarith) hτ
  have e : (μ - bh * Real.exp (-(ρ * τ))) * τ =
      -(bh / ρ * ((ρ * τ) * (Real.exp (-(ρ * τ)) - μ / bh))) := by
    field_simp
    ring
  have h2 := mul_le_mul_of_nonneg_left hl (div_nonneg hbh.le hρ.le)
  linarith

/-- **T1 Proposition 4.2 (`q = 1/2`, closed form).**  Let `N = M + 2`, `G = N/4`, `ρ = 2/(N + 1)`,
`i_*` the lattice index of `Δ_*` (`IsIStar`), `b̃`, `b̂` as in T1, and `μ > 0`.  Then for every integer
`j`, with `u = j + 1 − N/2`:
`f_C(M, j) + μu² ≥ μG − (b̂/ρ) ψ(μ/b̂) − (b̃/ρ) ψ̃(μ/b̃)`.
(With `bHat_le_bTilde`: `b̂ ≤ b̃`.) -/
theorem prop42 {M istar : ℕ} (hs : IsIStar M istar) {μ : ℝ} (hμ : 0 < μ) (j : ℤ) :
    μ * (((M : ℝ) + 2) / 4) - bHat M istar / rhoN M * psiLoss (μ / bHat M istar) -
        bTilde M istar / rhoN M * psiGain (μ / bTilde M istar) ≤
      fC (1 / 2) M j + μ * ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 := by
  have hρ := rhoN_pos M
  have hbt := bTilde_pos hs
  have hbh := bHat_pos hs
  have hA : 0 ≤ bHat M istar / rhoN M * psiLoss (μ / bHat M istar) :=
    mul_nonneg (div_nonneg hbh.le hρ.le) (psiLoss_nonneg (div_nonneg hμ.le hbh.le))
  have hB : 0 ≤ bTilde M istar / rhoN M * psiGain (μ / bTilde M istar) :=
    mul_nonneg (div_nonneg hbt.le hρ.le) (psiGain_nonneg _)
  have ecast : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [fC_half]
  by_cases hin : ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 ≤ ((M : ℝ) + 2) / 4
  · have hW := W_inside hs (j + 1) (by rw [ecast]; exact hin)
    rw [ecast] at hW
    have hstep := inside_step (μ := μ) hρ hbt (by linarith) hW
    have e : kappaWeight (1 / 2) M (j + 1) *
        (((M : ℝ) + 2) / 4 - ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2) +
          μ * ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 =
        μ * (((M : ℝ) + 2) / 4) + (kappaWeight (1 / 2) M (j + 1) - μ) *
          (((M : ℝ) + 2) / 4 - ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2) := by ring
    rw [e]
    linarith
  · push_neg at hin
    have hW := W_outside hs (j + 1) (by rw [ecast]; exact hin)
    rw [ecast] at hW
    have hstep := outside_step (μ := μ) hμ.le hρ hbh (by linarith) hW
    have e : kappaWeight (1 / 2) M (j + 1) *
        (((M : ℝ) + 2) / 4 - ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2) +
          μ * ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 =
        μ * (((M : ℝ) + 2) / 4) + (μ - kappaWeight (1 / 2) M (j + 1)) *
          (((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) ^ 2 - ((M : ℝ) + 2) / 4) := by ring
    rw [e]
    linarith

/-- The lattice index `i_*(M)` (a choice; it is unique). -/
noncomputable def istarOf (M : ℕ) : ℕ := Classical.choose (exists_isIStar M)

theorem isIStar_istarOf (M : ℕ) : IsIStar M (istarOf M) := Classical.choose_spec (exists_isIStar M)

/-- **T1's closed-form fibre bound at `q = 1/2`:**
`H(M) = μG − (b̂/ρ) ψ(μ/b̂) − (b̃/ρ) ψ̃(μ/b̃)`. -/
noncomputable def fibreHalf (μ : ℝ) (M : ℕ) : ℝ :=
  μ * (((M : ℝ) + 2) / 4) - bHat M (istarOf M) / rhoN M * psiLoss (μ / bHat M (istarOf M)) -
    bTilde M (istarOf M) / rhoN M * psiGain (μ / bTilde M (istarOf M))

/-- **T1 Proposition 4.2 as a fibre bound.**  At `q = 1/2` (`κ = f_C`, `δ = j − M/2 = u`),
`fibreHalf μ` satisfies the pointwise condition of `ExplicitThreshold` with `c = 0`, `ν = μ`. -/
theorem fibreHalf_le {μ : ℝ} (hμ : 0 < μ) (M : ℕ) (j : ℤ) :
    fibreHalf μ M ≤ kappa (1 / 2) M j + 0 * ((j : ℝ) - 1 / 2 * M) + μ * ((j : ℝ) - 1 / 2 * M) ^ 2 := by
  have h := prop42 (isIStar_istarOf M) hμ j
  rw [kappa_eq_fC_add (by norm_num) (by norm_num)]
  have e : ((j : ℝ) + 1 - ((M : ℝ) + 2) / 2) = (j : ℝ) - 1 / 2 * M := by ring
  rw [e] at h
  have e2 : (1 - 2 * (1 / 2 : ℝ)) ^ 2 / (1 / 2 * (1 - 1 / 2)) * binom M (1 / 2) j = 0 := by
    norm_num
  rw [e2]
  unfold fibreHalf
  linarith

end Erdos993Lean.Analytic.NoValley
