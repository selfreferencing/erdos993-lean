import Erdos993Lean.Analytic.TopCert
import Erdos993Lean.Analytic.Fourier.Main
import Erdos993Lean.Analytic.LargeMean.Main
import Erdos993Lean.Analytic.NoValley.Core
import Erdos993Lean.ZhangKernel.Main

/-!
# The analytic route: assembly of the merged lanes

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).

* `fourierEstimates`: lane F1's binomial Fourier estimates in the form lane F2 consumes.
* `noValleyAt_largeMean`: the large-mean no-valley theorem (every `m ≥ 400`), unconditional (lanes F1,
  F2; Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md`, adjudicated CORRECT in
  `LEAN/referee/REVIEW_SOUL_ROUND2.md`).
* `actQ_mem_of_inRange`: activities in `[1/3, 7/3]` have `q ∈ [1/4, 7/10]`.
* `thresholdNoValley_of_split`: O4 on the whole parameter domain from T1 (`t1Core`, lane A2) and the
  threshold numerics on `m < 400`, and the large-mean theorem on `m ≥ 400` (given the profile's `D ≤ 8/5`,
  `θ` targets and a third-mean tail).
* `erdos993_of_analytic_inputs_std`: **Erdős #993 from the analytic inputs, standard axioms only** — the
  finite part's certificate layer is `Zhang.certificatesSound_kernel` (lane K, kernel-checked, no
  `native_decide`).
-/

namespace Erdos993Lean.Analytic

/-- Lane F1's estimates in lane F2's interface form. -/
theorem fourierEstimates : FourierEstimates :=
  fun M q hq0 hq1 j hu =>
    ⟨binom_sub_gaussPhi_le M q hq0 hq1 j hu, fC_sub_gaussCurv_le M q hq0 hq1 j hu⟩

/-- **The large-mean no-valley theorem (every `m ≥ 400`)**, unconditional. -/
theorem noValleyAt_largeMean {q m θ D : ℝ} {T : ℕ → ℝ} {M1 : ℕ}
    (hq : 1 / 4 ≤ q ∧ q ≤ 7 / 10) (hm : 400 ≤ m) (hD : D ≤ 8 / 5)
    (hθ : (3 / 8 ≤ q ∧ q ≤ 8 / 13 ∧ θ ≤ 7 / 10) ∨ ((q ≤ 3 / 8 ∨ 8 / 13 ≤ q) ∧ θ ≤ 1))
    (hθ0 : 0 ≤ θ) (hD0 : 0 ≤ D)
    (htail : ∃ r : ℕ, r < M1 ∧ m / 3 ≤ (r : ℝ) + 1 ∧ T r ≤ Real.exp (-(m / 30))) :
    NoValleyAt q m θ D T M1 :=
  noValleyAt_of_largeMean fourierEstimates hq hm hD hθ hθ0 hD0 htail

/-- Activities in range give `q = t/(1 + t) ∈ [1/4, 7/10]`. -/
theorem actQ_mem_of_inRange {t : ℝ} (hR : InRange t) : 1 / 4 ≤ actQ t ∧ actQ t ≤ 7 / 10 := by
  obtain ⟨h1, h2⟩ := hR
  have ht : 0 < 1 + t := by linarith
  unfold actQ
  constructor
  · rw [le_div_iff₀ ht]; linarith
  · rw [div_le_iff₀ ht]; linarith

/-- **O4 on the whole parameter domain** from the two routes: T1 and the threshold numerics below
`m = 400`, the large-mean theorem from `m = 400` on. -/
theorem thresholdNoValley_of_split {P : Profile}
    (hsmall : ∀ t, InRange t → ∀ m, P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P.θb t) (P.Db t) (P.Tb t m) (P.M1b t m))
    (hD : ∀ t, InRange t → 0 ≤ P.Db t ∧ P.Db t ≤ 8 / 5)
    (hθ : ∀ t, InRange t → 0 ≤ P.θb t ∧
      ((3 / 8 ≤ actQ t ∧ actQ t ≤ 8 / 13 ∧ P.θb t ≤ 7 / 10) ∨
        ((actQ t ≤ 3 / 8 ∨ 8 / 13 ≤ actQ t) ∧ P.θb t ≤ 1)))
    (htail : ∀ t, InRange t → ∀ m, 400 ≤ m →
      ∃ r : ℕ, r < P.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧ P.Tb t m r ≤ Real.exp (-(m / 30))) :
    ThresholdNoValley P := by
  intro t hR m hm
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  by_cases h400 : m < 400
  · refine t1Core _ _ _ _ _ _ (by unfold actQ; positivity) ?_ (hsmall t hR m hm h400)
    unfold actQ
    rw [div_lt_one (by linarith)]
    linarith
  · push_neg at h400
    exact noValleyAt_largeMean (actQ_mem_of_inRange hR) h400 (hD t hR).2 (hθ t hR).2
      (hθ t hR).1 (hD t hR).1 (htail t hR m h400)

/-- **Erdős #993 from the analytic inputs, standard axioms only.**  Every finite forest has a unimodal
independence sequence, given the analytic inputs O1–O5 for some profile `P`; the finite part
(forests with at most 60 vertices) uses the kernel-checked certificate layer
`Zhang.certificatesSound_kernel` (no `native_decide`). -/
theorem erdos993_of_analytic_inputs_std {P : Profile} (h : AnalyticInputs P) : Erdos993Statement :=
  erdos993_of_analytic_inputs_cert Zhang.certificatesSound_kernel h

end Erdos993Lean.Analytic
