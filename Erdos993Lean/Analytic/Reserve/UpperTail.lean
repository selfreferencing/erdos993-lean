import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperBounds

/-!
# O1 on the upper band `[8/5, 7/3]`: the analytic tails (`UpperTailOK`, lane A14)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lane A14).  Sources: Astra's
`UPPER_SHARP_SIGNED_PORT_PROOF.md` (reviewed snapshot `LEAN/referee/astra_o1/snapshot_0845`), sections
"Complete parent tail Y>=4" and "Complete child tail T>=6, Y<=4"; the referee's line-by-line check
`LEAN/referee/REVIEW_ASTRA_O1_UPPER_PROOF.md`, TASK 3 (46 exact claims, `review_upper_proof/u3_tails_exact.py`).

With `δ = s − p` and the coefficients `E, H, L, J, Z` of `Reserve/Defs.lean`, `Reserve/Step.lean`, the three
comparisons of the signed reserve `α y + β u + γ u²/y` are
`CC = α E − β² δ² T/(4 y Z)`, `CB = CC + p γ L (s/y)²/Z + β p (γ s + L J)/(y Z)` and
`BC = α E + ((A − β) p − H)/Y − (T/y) (H s + β δ/2)²/Z`.  Both tails are first proved as statements about
real numbers (`parent_alg`, `child_alg`), from bounds that the messages satisfy on the tail
(`Reserve/UpperBounds.lean`):

* **parent tail** `Y ≥ 4` (every `T ≥ 0`), `parent_alg`: `p, y₀ ≤ 7/150`, `H ≤ (1 + γ) p`, `L ≥ γ/2`, so
  `Z ≥ p γ`, `Z ≥ L J`; with `w = p T/y` and `E = e₀ + w`, `e₀ = 1 − p − y₀/Y ≥ 113/120`:
  `δ² ≤ s² + p²` splits the CC cost into `β² J/(4Z) ≤ β²/(4L) ≤ 1/400` and `β² p² T/(4 y Z) ≤ w/800`,
  so `CC ≥ (4/13)(113/120) − 1/400 + (4/13 − 1/800) w > 0`; `CB ≥ CC` (`L ≥ 0`); for BC the exact cross term
  `(H s + β δ/2)² = ((H + β/2) s − β p/2)² ≤ (H + β/2)² s² + β² p²/4` gives the square cost
  `≤ (H + β/2)²/L + w/800 ≤ 1/20 + w/800`, and `((A − β) p − H)/Y ≥ −(β + γ) p/4 ≥ −1/100`;
* **child tail** `T ≥ 6`, `y ≤ Y ≤ 4`, `child_alg`: `y ≤ 7/1200`, `s ≤ y`, `J ≤ (3/62) γ`,
  `L ≥ −H Y ≥ −4 (1 + γ) p`, so `Z ≥ (13/20) p γ`; `E y ≥ p (T − 10/3)` (`y₀ ≤ (1 + λ) p`);
  `T s² ≤ (3/20) p²` gives `T δ² ≤ (41/40) T p²` and the CC cost `≤ (1/400) T p/y`, so
  `CC ≥ (16/117 − 1/400) T p/y`; if `L < 0`, `p γ L (s/y)²/Z ≥ −11 p` and `β p L J/(y Z) ≥ −(1/20) p/y`,
  so `CB ≥ (6 (16/117 − 1/400) − 1/20) p/y − 11 p > 0` (`p/y ≥ (1200/7) p`); for BC the sign-aware
  bound `((A − β) p − H)/Y ≥ −(β + γ − 3q/5) p/y` (`3q/5 ≤ β + γ`, `Y ≥ y`), `(a + b)² ≤ 2a² + 2b²`
  (square cost `≤ 2 H² J/Z + 2 CC-cost ≤ p/2 + (1/200) T p/y`) and `T p/y ≥ 6 p/y` give
  `BC ≥ ((29/15) q − β − γ − 3/100) p/y − p/2 > 0`.

**`upperTailOK : UpperTailOK`** follows (`Y ≥ 4`: the parent tail; `Y < 4`, `T ≥ 6`: the child tail).

Scalarity: `p, y₀, s, y` are the actual messages and log-masses of one parent–child pair, `T, Y` the
grandchild and child log-mass sums of the actual lists, `E` the entropy coefficient of the pair (its object
is the divergence of the two occupation laws plus the sibling log-mass, `Reserve/Entropy.lean`);
`H, L, J, Z` are local coefficients of the pair's completed square (not carried); `w = p T/y` is an
intermediate of this proof only; the margins are outputs.  The consumer is `stepCert_upper`
(`Reserve/UpperStep.lean`) and through it lane A11's `reserve_step_cert`.
-/

namespace Erdos993Lean.Analytic.Reserve

open Real

namespace Upper

/-! ### Generic estimates for the square costs -/

/-- `δ² ≤ s² + p²` splits the CC cost. -/
theorem cost_split {β s p T y Z : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) (hT : 0 ≤ T) (hy : 0 < y)
    (hZ : 0 < Z) :
    β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) ≤
      β ^ 2 * s ^ 2 * T / (4 * y * Z) + β ^ 2 * p ^ 2 * T / (4 * y * Z) := by
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h : 0 ≤ β ^ 2 * T * (s * p) := by positivity
  nlinarith [h]

/-- The `p`-part of the CC cost: `β² p² T/(4 y Z) ≤ c · p T/y` when `p γ ≤ Z` and `β² ≤ 4 c γ`. -/
theorem cost_p {β γ c p T y Z : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ) (hp : 0 < p) (hT : 0 ≤ T)
    (hy : 0 < y) (hZp : p * γ ≤ Z) (hβ : β ^ 2 ≤ 4 * c * γ) :
    β ^ 2 * p ^ 2 * T / (4 * y * Z) ≤ c * (p * T / y) := by
  have hZ : 0 < Z := lt_of_lt_of_le (mul_pos hp hγ) hZp
  rw [div_le_iff₀ (by positivity)]
  have e : c * (p * T / y) * (4 * y * Z) = 4 * c * (p * T) * Z := by
    field_simp
  rw [e]
  have h1 : 0 ≤ p * T * p := by positivity
  have h2 : 0 ≤ 4 * c * (p * T) := by positivity
  calc β ^ 2 * p ^ 2 * T = β ^ 2 * (p * T * p) := by ring
    _ ≤ 4 * c * γ * (p * T * p) := mul_le_mul_of_nonneg_right hβ h1
    _ = 4 * c * (p * T) * (p * γ) := by ring
    _ ≤ 4 * c * (p * T) * Z := mul_le_mul_of_nonneg_left hZp h2

/-- `K J/Z ≤ c` when `K ≤ c L` and `L J ≤ Z` (so `β² s² T/(4yZ) = β² J/(4Z) ≤ β²/(4L)`, and
`(H + β/2)² J/Z ≤ (H + β/2)²/L`). -/
theorem sq_J_div_le {K c L J Z : ℝ} (hc : 0 ≤ c) (hZ : 0 < Z) (hJ0 : 0 ≤ J) (hZL : L * J ≤ Z)
    (hK : K ≤ c * L) : K * J / Z ≤ c := by
  rw [div_le_iff₀ hZ]
  calc K * J ≤ c * L * J := mul_le_mul_of_nonneg_right hK hJ0
    _ = c * (L * J) := by ring
    _ ≤ c * Z := mul_le_mul_of_nonneg_left hZL hc

/-- The `s`-part of the CC cost: `β² s² T/(4 y Z) = (β²/4) J/Z`. -/
theorem cost_s_eq {β s T y J Z : ℝ} (hy : 0 < y) (hZ : 0 < Z) (hJ : J = s ^ 2 * T / y) :
    β ^ 2 * s ^ 2 * T / (4 * y * Z) = β ^ 2 / 4 * J / Z := by
  rw [hJ]
  field_simp

/-- The BC square with its exact negative cross term:
`(T/y)(H s + β δ/2)²/Z ≤ (H + β/2)² J/Z + β² p² T/(4 y Z)`. -/
theorem bc_square_cross {β s p T y H J Z : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hs : 0 ≤ s) (hp : 0 ≤ p)
    (hT : 0 ≤ T) (hy : 0 < y) (hZ : 0 < Z) (hJ : J = s ^ 2 * T / y) :
    T / y * (H * s + β * (s - p) / 2) ^ 2 / Z ≤
      (H + β / 2) ^ 2 * J / Z + β ^ 2 * p ^ 2 * T / (4 * y * Z) := by
  have hsq : (H * s + β * (s - p) / 2) ^ 2 ≤ (H + β / 2) ^ 2 * s ^ 2 + β ^ 2 * p ^ 2 / 4 := by
    have h : 0 ≤ (H + β / 2) * s * (β * p) := by positivity
    nlinarith [h]
  calc T / y * (H * s + β * (s - p) / 2) ^ 2 / Z ≤
        T / y * ((H + β / 2) ^ 2 * s ^ 2 + β ^ 2 * p ^ 2 / 4) / Z := by
        apply div_le_div_of_nonneg_right _ hZ.le
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (H + β / 2) ^ 2 * J / Z + β ^ 2 * p ^ 2 * T / (4 * y * Z) := by
        rw [hJ]
        field_simp

/-- The BC square by `(a + b)² ≤ 2a² + 2b²`:
`(T/y)(H s + β δ/2)²/Z ≤ 2 H² J/Z + 2 β² δ² T/(4 y Z)`. -/
theorem bc_square_two {β s p T y H J Z : ℝ} (hT : 0 ≤ T) (hy : 0 < y) (hZ : 0 < Z)
    (hJ : J = s ^ 2 * T / y) :
    T / y * (H * s + β * (s - p) / 2) ^ 2 / Z ≤
      2 * H ^ 2 * J / Z + 2 * (β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z)) := by
  have hsq : (H * s + β * (s - p) / 2) ^ 2 ≤ 2 * H ^ 2 * s ^ 2 + β ^ 2 * (s - p) ^ 2 / 2 := by
    nlinarith [sq_nonneg (H * s - β * (s - p) / 2)]
  calc T / y * (H * s + β * (s - p) / 2) ^ 2 / Z ≤
        T / y * (2 * H ^ 2 * s ^ 2 + β ^ 2 * (s - p) ^ 2 / 2) / Z := by
        apply div_le_div_of_nonneg_right _ hZ.le
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * H ^ 2 * J / Z + 2 * (β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z)) := by
        rw [hJ]
        field_simp
        ring

/-! ### The parent tail `Y ≥ 4` as a statement about reals -/

/-- On the parent tail `α E ≥ (4/13)(113/120) + (4/13) p T/y` (`E = e₀ + p T/y`, `e₀ ≥ 113/120`). -/
theorem parent_alphaE {α p T y y0 Y E : ℝ} (hα : 4 / 13 ≤ α) (hp : 0 ≤ p) (hp1 : p ≤ 7 / 150)
    (hT : 0 ≤ T) (hy : 0 < y) (hY : 4 ≤ Y) (hy01 : y0 ≤ 7 / 150)
    (hE : E = 1 - p + p * T / y - y0 / Y) :
    4 / 13 * (113 / 120) + 4 / 13 * (p * T / y) ≤ α * E := by
  have hY0 : 0 < Y := by linarith
  have hw0 : 0 ≤ p * T / y := by positivity
  have he0 : y0 / Y ≤ 7 / 600 := by
    rw [div_le_iff₀ hY0]
    nlinarith
  have h1 : 113 / 120 + p * T / y ≤ E := by rw [hE]; linarith
  have h2 : 0 ≤ 113 / 120 + p * T / y := by linarith
  have h3 : 4 / 13 * (113 / 120 + p * T / y) ≤ α * (113 / 120 + p * T / y) :=
    mul_le_mul_of_nonneg_right hα h2
  have h4 : α * (113 / 120 + p * T / y) ≤ α * E := mul_le_mul_of_nonneg_left h1 (by linarith)
  linarith

/-- On the parent tail `((A − β) p − H)/Y ≥ −1/100` (`(A − β) p − H ≥ −(β + γ) p ≥ −1/25`, `Y ≥ 4`). -/
theorem parent_lin {A β γ p H Y : ℝ} (hA : 1 ≤ A) (hp : 0 ≤ p) (hH : H ≤ (1 + γ) * p)
    (hY : 4 ≤ Y) (hc : (β + γ) * p ≤ 1 / 25) : -(1 / 100) ≤ ((A - β) * p - H) / Y := by
  have hY0 : 0 < Y := by linarith
  rw [le_div_iff₀ hY0]
  have h1 : -((β + γ) * p) ≤ (A - β) * p - H := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ A - 1) hp]
  linarith

/-- **The parent tail of the upper band, over the reals**: from the tail bounds on the messages and the
coefficient profile, `Z > 0`, `CC ≥ 0`, `CB ≥ 0`, `BC ≥ 0`. -/
theorem parent_alg {α β γ A p s y y0 Y T H L J Z E : ℝ}
    (hα : 4 / 13 ≤ α) (hβ0 : 0 ≤ β) (hβ : β ≤ 4 / 81) (hγ0 : 62 / 125 ≤ γ) (hγ : γ ≤ 217 / 300)
    (hA : 1 ≤ A) (hp : 0 < p) (hp1 : p ≤ 7 / 150) (hs : 0 < s) (hy : 0 < y) (hT : 0 ≤ T)
    (hY : 4 ≤ Y) (hy01 : y0 ≤ 7 / 150) (hH0 : 0 ≤ H) (hH : H ≤ (1 + γ) * p)
    (hL : γ / 2 ≤ L) (hJ : J = s ^ 2 * T / y) (hZ : Z = p * γ + L * J)
    (hE : E = 1 - p + p * T / y - y0 / Y) :
    0 < Z ∧ 0 ≤ α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) ∧
    0 ≤ α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) + p * γ * L * (s / y) ^ 2 / Z +
      β * p * (γ * s + L * J) / (y * Z) ∧
    0 ≤ α * E + ((A - β) * p - H) / Y - T / y * (H * s + β * (s - p) / 2) ^ 2 / Z := by
  have hγp : 0 < γ := by linarith
  have hL0 : 0 < L := by linarith
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have hpγ : 0 < p * γ := mul_pos hp hγp
  have hLJ : 0 ≤ L * J := mul_nonneg hL0.le hJ0
  have hZp : p * γ ≤ Z := by rw [hZ]; linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le hpγ hZp
  have hZL : L * J ≤ Z := by rw [hZ]; linarith
  have hαE := parent_alphaE hα hp.le hp1 hT hy hY hy01 hE
  have hβ2 : β ^ 2 ≤ 16 / 6561 := by nlinarith
  have hR2 : β ^ 2 * p ^ 2 * T / (4 * y * Z) ≤ 1 / 800 * (p * T / y) :=
    cost_p (by norm_num) hγp hp hT hy hZp (by linarith)
  have hR1 : β ^ 2 * s ^ 2 * T / (4 * y * Z) ≤ 1 / 400 := by
    rw [cost_s_eq hy hZ0 hJ]
    exact sq_J_div_le (by norm_num) hZ0 hJ0 hZL (by linarith)
  have hsplit := cost_split (β := β) hs.le hp.le hT hy hZ0
  have hw0 : 0 ≤ p * T / y := by positivity
  have hCC : 0 ≤ α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) := by
    linarith only [hαE, hR1, hR2, hsplit, hw0]
  refine ⟨hZ0, hCC, ?_, ?_⟩
  · -- CB: both additional terms are nonnegative (`L > 0`)
    have hx1 : 0 ≤ p * γ * L * (s / y) ^ 2 / Z :=
      div_nonneg (mul_nonneg (mul_nonneg hpγ.le hL0.le) (sq_nonneg _)) hZ0.le
    have hx2 : 0 ≤ β * p * (γ * s + L * J) / (y * Z) :=
      div_nonneg (mul_nonneg (mul_nonneg hβ0 hp.le)
        (add_nonneg (mul_pos hγp hs).le hLJ)) (mul_pos hy hZ0).le
    linarith only [hCC, hx1, hx2]
  · -- BC
    have hBsq := bc_square_cross (β := β) hH0 hβ0 hs.le hp.le hT hy hZ0 hJ
    have hHp : (1 + γ) * p ≤ 517 / 300 * (7 / 150) :=
      mul_le_mul (by linarith) hp1 hp.le (by norm_num)
    have hHb0 : 0 ≤ H + β / 2 := by linarith
    have hHb : H + β / 2 ≤ 517 / 300 * (7 / 150) + 2 / 81 := by linarith
    have hHb2 : (H + β / 2) ^ 2 ≤ (517 / 300 * (7 / 150) + 2 / 81) ^ 2 := pow_le_pow_left₀ hHb0 hHb 2
    have hHJ : (H + β / 2) ^ 2 * J / Z ≤ 1 / 20 :=
      sq_J_div_le (by norm_num) hZ0 hJ0 hZL (by nlinarith)
    have hc : (β + γ) * p ≤ 1 / 25 := by
      have : (β + γ) * p ≤ (4 / 81 + 217 / 300) * (7 / 150) :=
        mul_le_mul (by linarith) hp1 hp.le (by norm_num)
      linarith
    have hX := parent_lin (β := β) hA hp.le hH hY hc
    linarith only [hαE, hX, hBsq, hHJ, hR2, hw0]

/-! ### The child tail `T ≥ 6`, `Y ≤ 4` as a statement about reals -/

/-- On the child tail `Z ≥ (13/20) p γ` (`L J ≥ −4 (1 + γ) p J`, `J ≤ (3/62) γ`, `1 + γ ≤ 517/300`). -/
theorem child_Z {γ p L J Z : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 217 / 300) (hp : 0 < p) (hJ0 : 0 ≤ J)
    (hJle : J ≤ 3 / 62 * γ) (hL4 : -(4 * ((1 + γ) * p)) ≤ L) (hZ : Z = p * γ + L * J) :
    13 / 20 * (p * γ) ≤ Z := by
  have hγJ : (1 + γ) * J ≤ 517 / 300 * (3 / 62 * γ) :=
    mul_le_mul (by linarith) hJle hJ0 (by norm_num)
  have hLJ : -(4 * ((1 + γ) * p)) * J ≤ L * J := mul_le_mul_of_nonneg_right hL4 hJ0
  have hpγJ : p * ((1 + γ) * J) ≤ p * (517 / 300 * (3 / 62 * γ)) :=
    mul_le_mul_of_nonneg_left hγJ hp.le
  have hpγ : 0 ≤ p * γ := mul_nonneg hp.le hγ0
  rw [hZ]
  linarith only [hLJ, hpγJ, hpγ]

/-- On the child tail the CC cost is `≤ (1/400) T p/y`
(`T δ² ≤ T p² + (3/20) p² ≤ (41/40) T p²`, `Z ≥ (13/20) p γ`). -/
theorem child_cost {β γ p s y T Z : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 4 / 81) (hγ0 : 62 / 125 ≤ γ)
    (hp : 0 < p) (hs : 0 < s) (hy : 0 < y) (hT : 6 ≤ T) (hZ13 : 13 / 20 * (p * γ) ≤ Z)
    (hTs : T * s ^ 2 ≤ 3 / 20 * p ^ 2) :
    β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) ≤ 1 / 400 * (T * (p / y)) := by
  have hγp : 0 < γ := by linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ13
  rw [div_le_iff₀ (by positivity)]
  have e : 1 / 400 * (T * (p / y)) * (4 * y * Z) = 1 / 100 * (T * p) * Z := by
    field_simp
    ring
  rw [e]
  have hβ2 : β ^ 2 ≤ 16 / 6561 := by nlinarith
  have h1 : (s - p) ^ 2 * T ≤ 41 / 40 * (T * p ^ 2) := by
    have := mul_pos hs hp
    nlinarith
  have h2 : β ^ 2 * ((s - p) ^ 2 * T) ≤ 16 / 6561 * (41 / 40 * (T * p ^ 2)) :=
    mul_le_mul hβ2 h1 (by positivity) (by norm_num)
  have h3 : 1 / 100 * (T * p) * (13 / 20 * (p * γ)) ≤ 1 / 100 * (T * p) * Z :=
    mul_le_mul_of_nonneg_left hZ13 (by positivity)
  have h4 : 16 / 6561 * (41 / 40 * (T * p ^ 2)) ≤ 1 / 100 * (T * p) * (13 / 20 * (p * γ)) := by
    have h5 : 0 ≤ T * p ^ 2 := by positivity
    have h6 : T * p ^ 2 * (62 / 125) ≤ T * p ^ 2 * γ := mul_le_mul_of_nonneg_left hγ0 h5
    have e2 : 1 / 100 * (T * p) * (13 / 20 * (p * γ)) = 13 / 2000 * (T * p ^ 2 * γ) := by ring
    rw [e2]
    linarith only [h5, h6]
  calc β ^ 2 * (s - p) ^ 2 * T = β ^ 2 * ((s - p) ^ 2 * T) := by ring
    _ ≤ 1 / 100 * (T * p) * Z := by linarith only [h2, h3, h4]

/-- On the child tail `(q/2) E ≥ (16/117) T p/y` (`E ≥ (T − 10/3) p/y ≥ (4/9) T p/y`, `q ≥ 8/13`). -/
theorem child_alphaE {q p y T E : ℝ} (hq : 8 / 13 ≤ q) (hp : 0 < p) (hy : 0 < y) (hT : 6 ≤ T)
    (hE : (T - 10 / 3) * (p / y) ≤ E) : 16 / 117 * (T * (p / y)) ≤ q / 2 * E := by
  have hv0 : 0 ≤ p / y := by positivity
  have h1 : 4 / 9 * (T * (p / y)) ≤ (T - 10 / 3) * (p / y) := by nlinarith
  have h2 : 0 ≤ (T - 10 / 3) * (p / y) := by nlinarith
  calc 16 / 117 * (T * (p / y)) = 4 / 13 * (4 / 9 * (T * (p / y))) := by ring
    _ ≤ 4 / 13 * ((T - 10 / 3) * (p / y)) := by linarith
    _ ≤ q / 2 * ((T - 10 / 3) * (p / y)) := mul_le_mul_of_nonneg_right (by linarith) h2
    _ ≤ q / 2 * E := mul_le_mul_of_nonneg_left hE (by linarith)

/-- On the child tail with `L < 0`: `p γ L (s/y)²/Z ≥ −11 p` (`L (s/y)² ≥ L ≥ −4 (1 + γ) p`). -/
theorem child_cb1 {γ p s y L Z : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 217 / 300) (hp : 0 < p) (hs : 0 < s)
    (hsy : s ≤ y) (hL : L < 0) (hL4 : -(4 * ((1 + γ) * p)) ≤ L) (hZ13 : 13 / 20 * (p * γ) ≤ Z) :
    -(11 * p) ≤ p * γ * L * (s / y) ^ 2 / Z := by
  have hy : 0 < y := lt_of_lt_of_le hs hsy
  have hpγ : 0 < p * γ := mul_pos hp hγ0
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ13
  rw [le_div_iff₀ hZ0]
  have hsy2 : (s / y) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ s / y := by positivity
    have h1 : s / y ≤ 1 := by rw [div_le_one hy]; exact hsy
    nlinarith
  have h1 : L ≤ L * (s / y) ^ 2 := by nlinarith
  have h2 : p * γ * L ≤ p * γ * (L * (s / y) ^ 2) := mul_le_mul_of_nonneg_left h1 hpγ.le
  have h3 : p * γ * (-(4 * ((1 + γ) * p))) ≤ p * γ * L := mul_le_mul_of_nonneg_left hL4 hpγ.le
  have h4 : -(11 * p) * Z ≤ -(11 * p) * (13 / 20 * (p * γ)) :=
    mul_le_mul_of_nonpos_left hZ13 (by linarith)
  have h5 : -(11 * p) * (13 / 20 * (p * γ)) ≤ p * γ * (-(4 * ((1 + γ) * p))) := by
    have h6 : 0 ≤ p * γ * p := by positivity
    have h7 : p * γ * p * γ ≤ p * γ * p * (217 / 300) := mul_le_mul_of_nonneg_left hγ h6
    nlinarith
  have e : p * γ * L * (s / y) ^ 2 = p * γ * (L * (s / y) ^ 2) := by ring
  rw [e]
  linarith only [h2, h3, h4, h5]

/-- On the child tail: `β p (γ s + L J)/(y Z) ≥ −(1/20) p/y`
(`β p L J ≥ −4 β (1 + γ) p² J ≥ −4 (4/81)(517/300)(3/62) p² γ`, `Z ≥ (13/20) p γ`). -/
theorem child_cb2 {β γ p s y L J Z : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 4 / 81) (hγ0 : 0 < γ)
    (hγ : γ ≤ 217 / 300) (hp : 0 < p) (hs : 0 < s) (hy : 0 < y) (hJ0 : 0 ≤ J)
    (hJle : J ≤ 3 / 62 * γ) (hL4 : -(4 * ((1 + γ) * p)) ≤ L) (hZ13 : 13 / 20 * (p * γ) ≤ Z) :
    -(1 / 20 * (p / y)) ≤ β * p * (γ * s + L * J) / (y * Z) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ13
  rw [le_div_iff₀ (mul_pos hy hZ0)]
  have e : -(1 / 20 * (p / y)) * (y * Z) = -(1 / 20 * p * Z) := by
    field_simp
  rw [e]
  have hγJ : (1 + γ) * J ≤ 517 / 300 * (3 / 62 * γ) :=
    mul_le_mul (by linarith) hJle hJ0 (by norm_num)
  have hLJ : -(4 * ((1 + γ) * p)) * J ≤ L * J := mul_le_mul_of_nonneg_right hL4 hJ0
  have h1 : 0 ≤ β * p * (γ * s) := by positivity
  have h2 : β * p * (-(4 * ((1 + γ) * p)) * J) ≤ β * p * (L * J) :=
    mul_le_mul_of_nonneg_left hLJ (by positivity)
  have h3 : β * p * (-(4 * ((1 + γ) * p)) * J) = -(4 * β * (p * p) * ((1 + γ) * J)) := by ring
  have h4 : 4 * β * (p * p) * ((1 + γ) * J) ≤ 4 * (4 / 81) * (p * p) * (517 / 300 * (3 / 62 * γ)) := by
    have hb : 4 * β * (p * p) ≤ 4 * (4 / 81) * (p * p) := by
      have : 0 ≤ p * p := by positivity
      nlinarith
    exact mul_le_mul hb hγJ (by positivity) (by positivity)
  have h5 : 1 / 20 * p * (13 / 20 * (p * γ)) ≤ 1 / 20 * p * Z :=
    mul_le_mul_of_nonneg_left hZ13 (by positivity)
  have h6 : 4 * (4 / 81) * (p * p) * (517 / 300 * (3 / 62 * γ)) ≤ 1 / 20 * p * (13 / 20 * (p * γ)) := by
    have : 0 ≤ p * p * γ := by positivity
    nlinarith
  have e2 : β * p * (γ * s + L * J) = β * p * (γ * s) + β * p * (L * J) := by ring
  rw [e2]
  linarith only [h1, h2, h3, h4, h5, h6]

/-- On the child tail the sign-aware linear BC term:
`((1 + 3q/5 − β) p − H)/Y ≥ −(β + γ − 3q/5) p/y` (`H ≤ (1 + γ) p`, `β + γ ≥ 3q/5`, `y ≤ Y`). -/
theorem child_bc_lin {β γ q p y Y H : ℝ} (hk : 3 / 5 * q ≤ β + γ) (hp : 0 < p) (hy : 0 < y)
    (hyY : y ≤ Y) (hH : H ≤ (1 + γ) * p) :
    -((β + γ - 3 / 5 * q) * (p / y)) ≤ ((1 + 3 / 5 * q - β) * p - H) / Y := by
  have hY0 : 0 < Y := lt_of_lt_of_le hy hyY
  have hk0 : 0 ≤ β + γ - 3 / 5 * q := by linarith
  have hX : -((β + γ - 3 / 5 * q) * p) ≤ (1 + 3 / 5 * q - β) * p - H := by nlinarith
  have h1 : -((β + γ - 3 / 5 * q) * p) / Y ≤ ((1 + 3 / 5 * q - β) * p - H) / Y :=
    div_le_div_of_nonneg_right hX hY0.le
  have h2 : (β + γ - 3 / 5 * q) * p / Y ≤ (β + γ - 3 / 5 * q) * p / y :=
    div_le_div_of_nonneg_left (by positivity) hy hyY
  have e1 : -((β + γ - 3 / 5 * q) * p) / Y = -((β + γ - 3 / 5 * q) * p / Y) := by ring
  have e2 : (β + γ - 3 / 5 * q) * p / y = (β + γ - 3 / 5 * q) * (p / y) := by ring
  linarith only [h1, h2, e1, e2]

/-- On the child tail `2 H² J/Z ≤ p/2` (`H ≤ (517/300) p`, `J ≤ (3/62) γ`, `Z ≥ (13/20) p γ`). -/
theorem child_bc_sq {γ p H J Z : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 217 / 300) (hp : 0 < p) (hH0 : 0 ≤ H)
    (hH : H ≤ (1 + γ) * p) (hJ0 : 0 ≤ J) (hJle : J ≤ 3 / 62 * γ) (hZ13 : 13 / 20 * (p * γ) ≤ Z) :
    2 * H ^ 2 * J / Z ≤ p / 2 := by
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ13
  rw [div_le_iff₀ hZ0]
  have h1 : H ≤ 517 / 300 * p := by nlinarith
  have hH2 : H ^ 2 ≤ (517 / 300 * p) ^ 2 := pow_le_pow_left₀ hH0 h1 2
  have h2 : 2 * H ^ 2 * J ≤ 2 * (517 / 300 * p) ^ 2 * (3 / 62 * γ) :=
    mul_le_mul (by linarith) hJle hJ0 (by positivity)
  have h3 : p / 2 * (13 / 20 * (p * γ)) ≤ p / 2 * Z := mul_le_mul_of_nonneg_left hZ13 (by positivity)
  have h4 : 2 * (517 / 300 * p) ^ 2 * (3 / 62 * γ) ≤ p / 2 * (13 / 20 * (p * γ)) := by
    have : 0 ≤ p ^ 2 * γ := by positivity
    nlinarith
  linarith only [h2, h3, h4]

/-- **The child tail of the upper band, over the reals**: from the tail bounds on the messages and the
coefficient profile, `Z > 0`, `CC ≥ 0`, `CB ≥ 0`, `BC ≥ 0`. -/
theorem child_alg {α β γ A q p s y Y T H L J Z E : ℝ}
    (hq : 8 / 13 ≤ q) (hα : α = q / 2) (hβ0 : 0 ≤ β) (hβ : β ≤ 4 / 81) (hγ0 : 62 / 125 ≤ γ)
    (hγ : γ ≤ 217 / 300) (hA : A = 1 + 3 / 5 * q) (hk : 3 / 5 * q ≤ β + γ) (hp : 0 < p)
    (hs : 0 < s) (hsy : s ≤ y) (hy1 : y ≤ 7 / 1200) (hT : 6 ≤ T) (hyY : y ≤ Y) (hY4 : Y ≤ 4)
    (hH0 : 0 ≤ H) (hH : H ≤ (1 + γ) * p) (hLge : -(H * Y) ≤ L) (hJ : J = s ^ 2 * T / y)
    (hJle : J ≤ 3 / 62 * γ) (hZ : Z = p * γ + L * J) (hEy : p * (T - 10 / 3) ≤ E * y)
    (hTs : T * s ^ 2 ≤ 3 / 20 * p ^ 2) :
    0 < Z ∧ 0 ≤ α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) ∧
    0 ≤ α * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) + p * γ * L * (s / y) ^ 2 / Z +
      β * p * (γ * s + L * J) / (y * Z) ∧
    0 ≤ α * E + ((A - β) * p - H) / Y - T / y * (H * s + β * (s - p) / 2) ^ 2 / Z := by
  subst hα hA
  have hy : 0 < y := lt_of_lt_of_le hs hsy
  have hY0 : 0 < Y := lt_of_lt_of_le hy hyY
  have hγp : 0 < γ := by linarith
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have hpγ : 0 < p * γ := mul_pos hp hγp
  have hL4 : -(4 * ((1 + γ) * p)) ≤ L := by
    have : H * Y ≤ (1 + γ) * p * 4 := mul_le_mul hH hY4 hY0.le (by positivity)
    linarith
  have hZ13 := child_Z hγp.le hγ hp hJ0 hJle hL4 hZ
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ13
  have hv0 : 0 ≤ p / y := by positivity
  have hv : 1200 / 7 * p ≤ p / y := by
    rw [le_div_iff₀ hy]
    nlinarith
  have hE : (T - 10 / 3) * (p / y) ≤ E := by
    rw [← mul_div_assoc, div_le_iff₀ hy]
    linarith
  have hTv : 6 * (p / y) ≤ T * (p / y) := mul_le_mul_of_nonneg_right hT hv0
  have hR := child_cost hβ0 hβ hγ0 hp hs hy hT hZ13 hTs
  have hαE := child_alphaE hq hp hy hT hE
  have hCC : 0 ≤ q / 2 * E - β ^ 2 * (s - p) ^ 2 * T / (4 * y * Z) := by
    linarith only [hR, hαE, hTv, hv0]
  refine ⟨hZ0, hCC, ?_, ?_⟩
  · -- CB
    by_cases hL : 0 ≤ L
    · have hx1 : 0 ≤ p * γ * L * (s / y) ^ 2 / Z :=
        div_nonneg (mul_nonneg (mul_nonneg hpγ.le hL) (sq_nonneg _)) hZ0.le
      have hx2 : 0 ≤ β * p * (γ * s + L * J) / (y * Z) :=
        div_nonneg (mul_nonneg (mul_nonneg hβ0 hp.le)
          (add_nonneg (mul_pos hγp hs).le (mul_nonneg hL hJ0))) (mul_pos hy hZ0).le
      linarith only [hCC, hx1, hx2]
    · push_neg at hL
      have hT1 := child_cb1 hγp hγ hp hs hsy hL hL4 hZ13
      have hT2 := child_cb2 hβ0 hβ hγp hγ hp hs hy hJ0 hJle hL4 hZ13
      linarith only [hR, hαE, hTv, hv, hT1, hT2, hp]
  · -- BC
    have hXY := child_bc_lin hk hp hy hyY hH
    have hBsq := bc_square_two (β := β) (p := p) (H := H) (by linarith : (0 : ℝ) ≤ T) hy hZ0 hJ
    have hHJ := child_bc_sq hγp hγ hp hH0 hH hJ0 hJle hZ13
    have hαE' : q / 2 * ((T - 10 / 3) * (p / y)) ≤ q / 2 * E :=
      mul_le_mul_of_nonneg_left hE (by linarith)
    have hc1 : 0 ≤ (q / 2 - 1 / 200) * (T * (p / y) - 6 * (p / y)) :=
      mul_nonneg (by linarith) (by linarith)
    have hc2 : 0 ≤ (29 / 15 * q - β - γ - 3 / 100 - 387 / 1000) * (p / y) :=
      mul_nonneg (by linarith) hv0
    linarith only [hXY, hBsq, hHJ, hαE', hc1, hc2, hR, hp, hv]

end Upper

open Upper in
/-- **The analytic tails of the upper band** (Astra's "Complete parent tail Y>=4" and "Complete child
tail T>=6, Y<=4"): for `λ ∈ [8/5, 7/3]`, `T ≥ 0`, `Y ≥ lmass λ T` and `Y ≥ 4` or `T ≥ 6`, the comparisons
of the signed reserve `α y + β u + γ u²/y` (`α = q/2`, `β = (λ − 1)/27`, `γ = 31λ/100`, `A = 1 + 3q/5`) hold:
`Z > 0`, `CC ≥ 0`, `CB ≥ 0`, `BC ≥ 0`. -/
theorem upperTailOK : UpperTailOK := by
  intro lam T Y hlo hhi hT hTY hcase
  have hlam : 0 < lam := by linarith
  have hγ0 := uGamma_ge hlo
  have hγ1 := uGamma_le hhi
  have hγ : 0 ≤ uGamma lam := by linarith
  have hp := msg_pos hlam Y
  have hs := msg_pos hlam T
  have hy := lmass_pos hlam T
  have hH0 := cH_nonneg hlam hγ Y
  have hH := cH_le hlam hγ Y
  rcases le_or_gt 4 Y with hY | hY
  · -- the parent tail `Y ≥ 4`
    obtain ⟨hp50, -, hy50⟩ := Tails.parent_small hlam hY
    exact parent_alg (uAlpha_ge hlo) (uBeta_nonneg hlo) (uBeta_le hhi) hγ0 hγ1 (uCapA_ge hlo) hp
      (by linarith) hs hy hT hY (by linarith) hH0 hH (parent_cL_ge hlo hhi hY) rfl rfl rfl
  · -- the child tail `T ≥ 6`, `Y < 4`
    have hT6 : 6 ≤ T := by
      rcases hcase with h | h
      · exact absurd h (not_le.mpr hY)
      · exact h
    obtain ⟨hy400, hJ3⟩ := Tails.child_small hlam hT6
    have hsy := Tails.msg_le_lmass hlam T
    have hJle : coefJ lam T ≤ 3 / 62 * uGamma lam := by
      unfold uGamma
      linarith
    have hEy : msg lam Y * (T - 10 / 3) ≤ coefE lam T Y * lmass lam T := by
      have h1 := Tails.coefE_mul_ge_child hlam hTY
      have h2 := Tails.lmass_le_one_add_mul_msg hlam (show 0 ≤ Y by linarith)
      have h3 : (1 + lam) * msg lam Y ≤ 10 / 3 * msg lam Y := by nlinarith
      linarith
    exact child_alg (actQ_ge hlo) rfl (uBeta_nonneg hlo) (uBeta_le hhi) hγ0 hγ1 rfl
      (capA_sub_le hlo hhi) hp hs hsy (by linarith) hT6 hTY hY.le hH0 hH (cL_ge hlam hγ Y) rfl hJle
      rfl hEy (child_ratio hlam hhi hT6 hY.le)

end Erdos993Lean.Analytic.Reserve
