import Erdos993Lean.Analytic.Defs
import Erdos993Lean.Analytic.Fourier.Gauss

/-!
# The large-mean no-valley theorem: the Fourier interface

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane F2 (interface with lane F1).
Source: Soul's `SOUL/O3/LOWER_CUTOFF/LARGE_MEAN_400_PROOF.md`, §2.

For `u = M q (1 − q)` and `d = j − qM`, the Gaussian density and the Gaussian curvature profile are
`φ_u(d) = e^{−d²/(2u)}/√(2πu)` (`gaussPhi`) and
`G_u(d) = (1 − d²/u) e^{−d²/(2u)}/(√(2π) u^{3/2})` (`gaussCurv`).

`FourierEstimates` is the pair of uniform binomial Fourier estimates of the source, §2, for
`u ≥ 25`:
* `|b_M(j) − φ_u(d)| ≤ |1 − 2q|/(6u) + 1/(4u^{3/2})`,
* `|f_C − G_u(d)| ≤ (2/3)|1 − 2q|/u² + 1/u^{5/2}`, with `f_C = 2b_M(j) − b_M(j − 1) − b_M(j + 1)`.

Lane F1 proves it (`Analytic/Fourier/`); lane F2 takes it as a hypothesis.  The three definitions
are stated verbatim as in the campaign order; `gaussPhi` and `gaussCurv` are F1's (merged by the lead).
-/

namespace Erdos993Lean.Analytic

-- `gaussPhi` and `gaussCurv` are lane F1's definitions (`Analytic/Fourier/Gauss.lean`), identical
-- to the text of the campaign order; lane F2's verbatim copies were merged into them by the lead.
/-- F1's two estimates, for u = M q (1 − q) ≥ 25. -/
def FourierEstimates : Prop := ∀ (M : ℕ) (q : ℝ), 0 < q → q < 1 → ∀ j : ℤ,
    25 ≤ (M : ℝ) * (q * (1 - q)) →
    |binom M q j - gaussPhi (M * (q * (1 - q))) (j - q * M)| ≤
        |1 - 2 * q| / (6 * (M * (q * (1 - q)))) + 1 / (4 * (M * (q * (1 - q))) ^ ((3 : ℝ) / 2)) ∧
    |(2 * binom M q j - binom M q (j - 1) - binom M q (j + 1)) - gaussCurv (M * (q * (1 - q))) (j - q * M)| ≤
        (2 / 3) * |1 - 2 * q| / (M * (q * (1 - q))) ^ 2 + 1 / (M * (q * (1 - q))) ^ ((5 : ℝ) / 2)

end Erdos993Lean.Analytic
