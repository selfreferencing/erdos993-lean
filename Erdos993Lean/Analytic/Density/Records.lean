import Erdos993Lean.Analytic.Density.Induction

/-!
# The two certified density records used on bands 16–30

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Source: Soul's
`SOUL/O6_O5/density_certified.json` (106 records, `SOUL/RESULTS/O5.md` §2), recomputed by the lane
(`LEAN/lanes/A8/scratch/cover.py`): at `n = 61` the ranks `k_min` of bands 16–30 are realized by the
two records `x = 1` (bands 16–18 here; it also covers 19–21, 23–25, 27–30) and `x = 11/10`
(bands 19–30).  The constants `r, s0, g, B0, h` are Soul's, verbatim; the path-tail parameters
`s_H, s_L, K, N₀` are the lane's (`s_L ≤ √(1 + 4x) ≤ s_H`).

* `rec1_valid`, `rec11_valid`: every finite condition of `Record.Valid` (the path values
  `μ_j − r j` for `j ≤ 12`, the 125 + 625 root-degree-3/4 tests, the branch-removal gains, the
  orderings), checked by the kernel (`decide +kernel`).
* **`hardCoreMean_ge_rec1`**, **`hardCoreMean_ge_rec11`**: for every forest with `n ≥ 8`,
  `μ_F(1) ≥ r₁ n + h₁` and `μ_F(11/10) ≥ r₁₁ n + h₁₁`.
-/

namespace Erdos993Lean.Analytic.Density

/-- Soul's certified density record at `x = 1`. -/
def rec1 : Record where
  x := 1
  r := 138196601 / 500000000
  s0 := 85410197 / 750000000
  g := 18053399 / 125000000
  B0 := 582468521 / 3500000000
  h := 104837389 / 687500000
  sH := 22361 / 10000
  sL := 559 / 250
  K := 1600
  N0 := 15

/-- Soul's certified density record at `x = 11/10`. -/
def rec11 : Record where
  x := 11 / 10
  r := 142417129 / 500000000
  s0 := 29457871 / 250000000
  g := 17147332513 / 112875000000
  B0 := 49331077272419 / 283316250000000
  h := 1398818642171 / 8643812500000
  sH := 23238 / 10000
  sL := 23237 / 10000
  K := 1600
  N0 := 15

/-- The record at `x = 1` satisfies every finite condition (kernel `decide`). -/
theorem rec1_valid : rec1.Valid := by
  constructor <;> decide +kernel

/-- The record at `x = 11/10` satisfies every finite condition (kernel `decide`). -/
theorem rec11_valid : rec11.Valid := by
  constructor <;> decide +kernel

/-- **The density record at `x = 1`**: `μ_F(1) ≥ r n + h` for every forest with `n ≥ 8`
(`r = 0.276393202`, `h = 0.15249…`). -/
theorem hardCoreMean_ge_rec1 (F : FiniteForest) (hn : 8 ≤ F.n) :
    ((138196601 / 500000000 : ℚ) : ℝ) * F.n + ((104837389 / 687500000 : ℚ) : ℝ) ≤
      hardCoreMean F 1 := by
  have h := rec1_valid.hardCoreMean_ge F hn
  simpa [rec1] using h

/-- **The density record at `x = 11/10`**: `μ_F(11/10) ≥ r n + h` for every forest with `n ≥ 8`
(`r = 0.284834258`, `h = 0.16182…`). -/
theorem hardCoreMean_ge_rec11 (F : FiniteForest) (hn : 8 ≤ F.n) :
    ((142417129 / 500000000 : ℚ) : ℝ) * F.n + ((1398818642171 / 8643812500000 : ℚ) : ℝ) ≤
      hardCoreMean F ((11 / 10 : ℚ) : ℝ) := by
  have h := rec11_valid.hardCoreMean_ge F hn
  simpa [rec11] using h

end Erdos993Lean.Analytic.Density
