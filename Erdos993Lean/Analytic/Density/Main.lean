import Erdos993Lean.Analytic.Density.Bands
import Erdos993Lean.Analytic.Density.Transfer
import Erdos993Lean.Analytic.Density.Records

/-!
# O5 on all 30 bands: `densityBound_profile30`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Sources: Soul's
`SOUL/RESULTS/O5.md` §1–§4 and `SOUL/O6_O5/density_bounds.py` (the band rule
`K(a, N) = max(⌈N/4⌉ + 1, max_{x ≤ a} ⌈√(q_a/q_x)(r_x N + h_x)⌉)` at `N = 61`), all adjudicated
CORRECT in `LEAN/referee/REVIEW_SOUL_ROUND1.md`.

**Theorem** (`densityBound_profile30 : DensityBound Profile30.P`).  For every forest with
`n ≥ 61`, every `t ∈ [1/3, 7/3]` at an interior rank `μ_F(t) = k` and every maximum-weight
independent set `B`, the expected free count satisfies `m ≥ mmin_{band(t)}`.

Proof (`Density.densityBound_of_rank`): `m ≥ k/(2q(t)) ≥ k_i/(2 q(λ_{i+1}))` once `k ≥ k_i`.
* Bands 1–15 (0-based `i < 15`): `k_i = 17 ≤ k` because `k > ⌈61/4⌉ = 16` (`kmin_le_of_low`).
* Bands 16–30 (`i ≥ 15`), `k_i ∈ {18, …, 21}` (`rank_high`): with the record `x = 1` on bands 16–18
  and `x = 11/10` on bands 19–30 (`recOf`), `μ_F(x) ≥ r n + h ≥ 61 r + h =: L`
  (`hardCoreMean_ge_rec1`, `hardCoreMean_ge_rec11`), `x ≤ λ_i ≤ t`, and the activity transfer
  (`le_of_transfer`) gives `k ≥ k_i` from the rational check `(k_i − 1)² < (q(λ_i)/q(x)) L²`
  (`band_checks`, kernel `decide`; no square roots).

Records used: `x = 1` (`r = 138196601/500000000`, `h = 104837389/687500000`) and `x = 11/10`
(`r = 142417129/500000000`, `h = 1398818642171/8643812500000`); tightest bands: band 16 with
`x = 1`, `√(q_a/q_x) L = 17.0125 > 17`, and band 26 with `x = 11/10`, `19.0079 > 19`.
-/

namespace Erdos993Lean.Analytic

namespace Density

open Profile30

/-- The record used on band `b` (0-based): `x = 1` on bands 15–17, `x = 11/10` on bands 18–29. -/
def recOf (b : ℕ) : Record := if b ≤ 17 then rec1 else rec11

theorem recOf_valid (b : ℕ) : (recOf b).Valid := by
  unfold recOf
  split_ifs
  · exact rec1_valid
  · exact rec11_valid

/-- **The band checks** (kernel `decide`): on bands 16–30, `k_i ≥ 1`, the record's activity lies
below the lower edge `λ_i`, and `(k_i − 1)² < (q(λ_i)/q(x)) (61 r + h)²`. -/
theorem band_checks : ∀ b < 30, 15 ≤ b →
    1 ≤ kmin.getD b 0 ∧ (recOf b).x ≤ edges.getD b 0 ∧
    ((kmin.getD b 0 : ℚ) - 1) ^ 2 <
      (edges.getD b 0 / (1 + edges.getD b 0)) / ((recOf b).x / (1 + (recOf b).x)) *
        (61 * (recOf b).r + (recOf b).h) ^ 2 := by
  decide +kernel

/-- **The rank bound on bands 16–30** from the density records and the activity transfer. -/
theorem rank_high {F : FiniteForest} (hn : 61 ≤ F.n) {t : ℝ} (hR : InRange t)
    (hb : 15 ≤ bandOf t) {k : ℕ} (hμ : hardCoreMean F t = k) : kmin.getD (bandOf t) 0 ≤ k := by
  obtain ⟨hb30, -, hle, -⟩ := bandOf_spec hR
  obtain ⟨hK1, hxe, hchk⟩ := band_checks (bandOf t) hb30 hb
  have hRv : (recOf (bandOf t)).Valid := recOf_valid (bandOf t)
  have hx : (0 : ℝ) < (recOf (bandOf t)).x := by exact_mod_cast hRv.x_pos
  have hxa : ((recOf (bandOf t)).x : ℝ) ≤ edgeR (bandOf t) := by
    unfold edgeR
    exact_mod_cast hxe
  have hμx := hRv.hardCoreMean_ge F (by omega)
  have hr : (0 : ℝ) ≤ (recOf (bandOf t)).r := by exact_mod_cast hRv.r_nonneg
  have hh : (0 : ℝ) ≤ (recOf (bandOf t)).h := by
    exact_mod_cast hRv.s0_nonneg.trans (hRv.s0_le_g.trans hRv.g_le_h)
  have hn' : (61 : ℝ) ≤ F.n := by exact_mod_cast hn
  have hL : (((61 * (recOf (bandOf t)).r + (recOf (bandOf t)).h : ℚ)) : ℝ) ≤
      hardCoreMean F (recOf (bandOf t)).x := by
    push_cast
    nlinarith
  have hL0 : (0 : ℝ) ≤ (((61 * (recOf (bandOf t)).r + (recOf (bandOf t)).h : ℚ)) : ℝ) := by
    push_cast
    positivity
  apply le_of_transfer F hx hxa hle hL0 hL hμ hK1
  have hq : actQ (edgeR (bandOf t)) / actQ ((recOf (bandOf t)).x : ℝ) =
      (((edges.getD (bandOf t) 0 / (1 + edges.getD (bandOf t) 0)) /
        ((recOf (bandOf t)).x / (1 + (recOf (bandOf t)).x)) : ℚ) : ℝ) := by
    unfold actQ edgeR
    push_cast
    ring
  rw [hq]
  exact_mod_cast hchk

end Density

open Density Profile30

/-- **O5 for the certified profile (all 30 bands).**  For every forest with `n ≥ 61`, every
activity `t ∈ [1/3, 7/3]` at an interior rank and every maximum-weight independent set `B`,
`Profile30.P.mfloor t ≤ m`: bands 1–15 from the integer rank `k ≥ 17`, bands 16–30 from the
certified density records at `x = 1` and `x = 11/10` transferred to `t` by
`μ_F(t)² / q(t) ≥ μ_F(x)² / q(x)`. -/
theorem densityBound_profile30 : DensityBound Profile30.P := by
  apply densityBound_of_rank
  intro F hn t hR k hk hμ
  rcases Nat.lt_or_ge (bandOf t) 15 with hb | hb
  · exact kmin_le_of_low hn hb hk
  · exact rank_high hn hR hb hμ

end Erdos993Lean.Analytic
