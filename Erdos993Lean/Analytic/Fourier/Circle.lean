import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.Fourier.CharFun

/-!
# Fourier inversion on the circle for binomial masses

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F1; interface `Analytic/Defs.lean` (`binom`).
Source: `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md` §2 (Fourier inversion) and the lane order
`LEAN/lanes/F1/PROMPT.md`, step 1.

* `integral_cexp_int_mul`: `∫_{−π}^{π} e^{int} dt = 2π·[n = 0]` for `n ∈ ℤ`;
* `psi_pow`: `(1 − q + q e^{it})^M = ∑_k C(M, k) q^k (1 − q)^{M−k} e^{ikt}`;
* `binom_eq_integral_psi`, `binom_eq_integral`: for every integer `j`, with `d = j − qM`,
  `b_M(j) = (2π)⁻¹ ∫_{−π}^{π} χ(t)^M e^{−itd} dt` (outside `0 ≤ j ≤ M` both sides vanish);
* `fC_eq_integral`: the curvature `f_C = 2b_M(j) − b_M(j − 1) − b_M(j + 1)` has the multiplier
  `2 − 2 cos t`: `f_C = (2π)⁻¹ ∫_{−π}^{π} χ(t)^M (2 − 2 cos t) e^{−itd} dt`.
-/

namespace Erdos993Lean.Analytic.Fourier

/-- `∫_{−π}^{π} e^{int} dt = 2π·[n = 0]`. -/
lemma integral_cexp_int_mul (n : ℤ) :
    ∫ t in (-Real.pi)..Real.pi, Complex.exp ((n : ℂ) * t * Complex.I) =
      if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    have : (fun t : ℝ => Complex.exp (((0 : ℤ) : ℂ) * t * Complex.I)) = fun _ => (1 : ℂ) := by
      ext t; simp
    rw [this, intervalIntegral.integral_const, Complex.real_smul, mul_one]
    push_cast; ring
  · have hc : (n : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have e : (fun t : ℝ => Complex.exp ((n : ℂ) * t * Complex.I)) =
        fun t : ℝ => Complex.exp ((n : ℂ) * Complex.I * t) := by
      ext t; congr 1; ring
    rw [e, integral_exp_mul_complex hc]
    have : Complex.exp ((n : ℂ) * Complex.I * (Real.pi : ℝ)) =
        Complex.exp ((n : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨n, by push_cast; ring⟩
    rw [this, sub_self, zero_div]

/-- The binomial expansion `ψ(t)^M = ∑_k C(M,k) q^k (1 − q)^{M−k} e^{ikt}`. -/
lemma psi_pow (M : ℕ) (q t : ℝ) :
    psi q t ^ M = ∑ k ∈ Finset.range (M + 1),
      ((((M.choose k : ℕ) : ℝ) * q ^ k * (1 - q) ^ (M - k) : ℝ) : ℂ) *
        Complex.exp ((k : ℂ) * t * Complex.I) := by
  rw [psi, add_comm (1 - (q : ℂ)), add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- **Fourier inversion on the circle**, in the `ψ` form:
`b_M(j) = (2π)⁻¹ ∫_{−π}^{π} ψ(t)^M e^{−ijt} dt` for every integer `j`. -/
theorem binom_eq_integral_psi (M : ℕ) (q : ℝ) (j : ℤ) :
    (binom M q j : ℂ) = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ t in (-Real.pi)..Real.pi, psi q t ^ M * Complex.exp (-((j : ℂ) * t * Complex.I)) := by
  have h1 : ∀ t : ℝ, psi q t ^ M * Complex.exp (-((j : ℂ) * t * Complex.I)) =
      ∑ k ∈ Finset.range (M + 1),
        ((((M.choose k : ℕ) : ℝ) * q ^ k * (1 - q) ^ (M - k) : ℝ) : ℂ) *
          Complex.exp ((((k : ℤ) - j : ℤ) : ℂ) * t * Complex.I) := by
    intro t
    rw [psi_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_finset_sum (fun k _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, integral_cexp_int_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases hj : 0 ≤ j ∧ j ≤ (M : ℤ)
  · obtain ⟨k0, rfl⟩ : ∃ k0 : ℕ, j = k0 := ⟨j.toNat, (Int.toNat_of_nonneg hj.1).symm⟩
    have hk0 : k0 ∈ Finset.range (M + 1) := by
      rw [Finset.mem_range]; have := hj.2; omega
    rw [Finset.sum_eq_single k0]
    · have hb : binom M q (k0 : ℤ) = ((M.choose k0 : ℕ) : ℝ) * q ^ k0 * (1 - q) ^ (M - k0) := by
        rw [binom, if_pos hj, Int.toNat_natCast]
      rw [hb, sub_self, if_pos rfl]
      push_cast
      field_simp
    · intro k _ hk
      rw [if_neg (by omega), mul_zero]
    · intro h; exact absurd hk0 h
  · have hne : ∀ k ∈ Finset.range (M + 1), ((k : ℤ) - j) ≠ 0 := by
      intro k hk h; apply hj; rw [Finset.mem_range] at hk; constructor <;> omega
    rw [Finset.sum_eq_zero (fun k hk => by rw [if_neg (hne k hk), mul_zero]), binom, if_neg hj]
    simp

lemma chi_pow_mul_exp (M : ℕ) (q t : ℝ) (j : ℤ) :
    chi q t ^ M * Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I) =
      psi q t ^ M * Complex.exp (-((j : ℂ) * t * Complex.I)) := by
  rw [chi_eq, mul_pow, ← Complex.exp_nat_mul,
    mul_comm (Complex.exp _) (psi q t ^ M), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Fourier inversion for the binomial mass**: with `d = j − qM`,
`b_M(j) = (2π)⁻¹ ∫_{−π}^{π} χ(t)^M e^{−itd} dt`. -/
theorem binom_eq_integral (M : ℕ) (q : ℝ) (j : ℤ) :
    (binom M q j : ℂ) = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ t in (-Real.pi)..Real.pi, chi q t ^ M *
        Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I) := by
  simp_rw [chi_pow_mul_exp]
  exact binom_eq_integral_psi M q j

/-- **Fourier inversion for the curvature** `f_C = 2b_M(j) − b_M(j − 1) − b_M(j + 1)`: its
multiplier is `2 − 2 cos t`. -/
theorem fC_eq_integral (M : ℕ) (q : ℝ) (j : ℤ) :
    ((2 * binom M q j - binom M q (j - 1) - binom M q (j + 1) : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t in (-Real.pi)..Real.pi, chi q t ^ M * ((2 - 2 * Real.cos t : ℝ) : ℂ) *
          Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I) := by
  have hpt : ∀ t : ℝ, chi q t ^ M * ((2 - 2 * Real.cos t : ℝ) : ℂ) *
        Complex.exp (-(((t * ((j : ℝ) - q * M)) : ℝ) : ℂ) * Complex.I) =
      2 * (psi q t ^ M * Complex.exp (-((j : ℂ) * t * Complex.I))) -
        psi q t ^ M * Complex.exp (-(((j - 1 : ℤ) : ℂ) * t * Complex.I)) -
        psi q t ^ M * Complex.exp (-(((j + 1 : ℤ) : ℂ) * t * Complex.I)) := by
    intro t
    rw [mul_comm (chi q t ^ M), mul_assoc, chi_pow_mul_exp]
    have e1 : Complex.exp (-(((j - 1 : ℤ) : ℂ) * t * Complex.I)) =
        Complex.exp (-((j : ℂ) * t * Complex.I)) * Complex.exp ((t : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp (-(((j + 1 : ℤ) : ℂ) * t * Complex.I)) =
        Complex.exp (-((j : ℂ) * t * Complex.I)) * Complex.exp (-(t : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have ecos : ((2 - 2 * Real.cos t : ℝ) : ℂ) =
        2 - (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I)) := by
      rw [← Complex.two_cos]; push_cast; ring
    rw [e1, e2, ecos]; ring
  have hi : ∀ n : ℤ, IntervalIntegrable
      (fun t : ℝ => psi q t ^ M * Complex.exp (-((n : ℂ) * t * Complex.I)))
      MeasureTheory.volume (-Real.pi) Real.pi := by
    intro n; apply Continuous.intervalIntegrable; unfold psi; fun_prop
  rw [show ((2 * binom M q j - binom M q (j - 1) - binom M q (j + 1) : ℝ) : ℂ) =
      2 * (binom M q j : ℂ) - (binom M q (j - 1) : ℂ) - (binom M q (j + 1) : ℂ) by push_cast; ring,
    binom_eq_integral_psi M q j, binom_eq_integral_psi M q (j - 1),
    binom_eq_integral_psi M q (j + 1)]
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub (((hi j).const_mul 2).sub (hi (j - 1))) (hi (j + 1)),
    intervalIntegral.integral_sub ((hi j).const_mul 2) (hi (j - 1)),
    intervalIntegral.integral_const_mul]
  ring

end Erdos993Lean.Analytic.Fourier
