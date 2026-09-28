import Erdos993Lean.Analytic.Defs

/-!
# The certified profile of the analytic route: 30 activity bands

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  The concrete `Profile` the final proof
uses, shared by the lanes that discharge O1–O5:

* the 31 band edges `λ_0 = 1/3 < λ_1 < ⋯ < λ_30 = 7/3` (`edges`);
* per band, the targets `D` of O1 (`Dt`) and `θ` of O2 (`θt`): `D = 8/5, θ = 1` on `[1/3, 3/5]` and
  `[8/5, 7/3]`; `D = 7/5, θ = 7/10` on `[3/5, 4/5]` and `[13/10, 8/5]`; `D = 6/5, θ = 3/5` on `[4/5, 13/10]`
  (T1's band targets, `ProofRuns/2026-09-27_zhang_review/reports/T1.md` §0);
* per band and per Laplace parameter `t_j ∈ {0, 1/20, 1/10, 1/5, 3/10}` (`tvals`), the certified O3 rate
  `ℓ` (`rates`; Soul's repaired potential, `SOUL/O3/H3_RATES_TABLE.md`);
* per band, the floor of the expected free count at `n ≥ 61` (`mmin`; Soul's O5 floors,
  `SOUL/O4/atlas_50/band_XX/SOURCE.json`: `17/(2 q_hi)` on bands 1–15, `k_min/(2 q_hi)` with
  `k_min ∈ {18, …, 21}` from the certified density records on bands 16–30).

The data are copied from Soul's atlas sources `SOUL/O4/atlas_50/band_XX/SOURCE.json` (which the O4
atlas consumes).  The lower-tail function is the one the atlas prices:
`T(λ, m, r) = min(1, min_j e^{−ℓ_j m} ((1 + h)/(1 + h t_j))^r)` with `h` the band's upper edge
(`tailFn`).  The tail cutoff is `M1(λ, m) = ⌈m⌉ + 1` (every tail index the consumers use lies below it).

An activity `t` belongs to band `bandOf t` (0-based): the number of interior edges strictly below `t`,
so band `i` is `(λ_i, λ_{i+1}]` (band 0 also contains `1/3`).
-/

namespace Erdos993Lean.Analytic.Profile30

/-- The band edges `λ_0 = 1/3 < ⋯ < λ_30 = 7/3`. -/
def edges : List ℚ :=
  [1/3, 9/25, 2/5, 9/20, 1/2, 11/20, 3/5, 13/20, 7/10, 3/4, 4/5, 21/25, 22/25, 23/25, 24/25, 1,
    26/25, 27/25, 28/25, 29/25, 6/5, 5/4, 13/10, 7/5, 3/2, 8/5, 7/4, 19/10, 41/20, 9/4, 7/3]

/-- The Laplace parameters `t_j` of O3. -/
def tvals : List ℚ := [0, 1/20, 1/10, 1/5, 3/10]

/-- The certified O3 rates `ℓ(band i, t_j)` (rows: bands 0..29; columns: `t_j`). -/
def rates : List (List ℚ) :=
  [ [619/2500, 2353/10000, 551/2500, 489/2500, 169/1000],
    [1309/5000, 613/2500, 2327/10000, 509/2500, 439/2500],
    [2793/10000, 2617/10000, 2451/10000, 271/1250, 467/2500],
    [751/2500, 563/2000, 1333/5000, 291/1250, 1001/5000],
    [643/2000, 3013/10000, 2821/10000, 1231/5000, 1067/5000],
    [339/1000, 1589/5000, 119/400, 1297/5000, 139/625],
    [3531/10000, 3343/10000, 3129/10000, 1363/5000, 146/625],
    [459/1250, 139/400, 3253/10000, 177/625, 97/400],
    [953/2500, 1787/5000, 669/2000, 182/625, 623/2500],
    [1959/5000, 3673/10000, 3437/10000, 187/625, 2559/10000],
    [4059/10000, 761/2000, 3561/10000, 192/625, 1313/5000],
    [4129/10000, 3871/10000, 3623/10000, 5/16, 267/1000],
    [4199/10000, 3937/10000, 921/2500, 1589/5000, 679/2500],
    [4269/10000, 4003/10000, 743/2000, 202/625, 1369/5000],
    [269/625, 1009/2500, 236/625, 1629/5000, 1391/5000],
    [7/16, 4069/10000, 3807/10000, 657/2000, 701/2500],
    [441/1000, 827/2000, 1919/5000, 207/625, 1413/5000],
    [2223/5000, 521/1250, 3869/10000, 1669/5000, 178/625],
    [4481/10000, 4201/10000, 39/100, 841/2500, 178/625],
    [1129/2500, 2117/5000, 3931/10000, 3391/10000, 2871/10000],
    [1129/2500, 2117/5000, 3931/10000, 841/2500, 2871/10000],
    [4551/10000, 2117/5000, 1981/5000, 3391/10000, 2871/10000],
    [2223/5000, 827/2000, 1919/5000, 207/625, 701/2500],
    [4481/10000, 521/1250, 3869/10000, 207/625, 701/2500],
    [1129/2500, 4201/10000, 39/100, 1669/5000, 701/2500],
    [441/1000, 2051/5000, 3807/10000, 202/625, 679/2500],
    [2223/5000, 2051/5000, 3807/10000, 202/625, 679/2500],
    [2223/5000, 2051/5000, 3807/10000, 641/2000, 2693/10000],
    [269/625, 397/1000, 921/2500, 1549/5000, 651/2500],
    [1129/2500, 521/1250, 3869/10000, 657/2000, 1369/5000] ]

/-- The O1 target `D` per band. -/
def Dt : List ℚ :=
  [8/5, 8/5, 8/5, 8/5, 8/5, 8/5, 7/5, 7/5, 7/5, 7/5, 6/5, 6/5, 6/5, 6/5, 6/5, 6/5, 6/5, 6/5,
    6/5, 6/5, 6/5, 6/5, 7/5, 7/5, 7/5, 8/5, 8/5, 8/5, 8/5, 8/5]

/-- The O2 target `θ` per band. -/
def θt : List ℚ :=
  [1, 1, 1, 1, 1, 1, 7/10, 7/10, 7/10, 7/10, 3/5, 3/5, 3/5, 3/5, 3/5, 3/5, 3/5, 3/5, 3/5, 3/5,
    3/5, 3/5, 7/10, 7/10, 7/10, 1, 1, 1, 1, 1]

/-- The O5 floor of `m` per band (`n ≥ 61`, interior ranks). -/
def mmin : List ℚ :=
  [289/9, 119/4, 493/18, 51/2, 527/22, 68/3, 561/26, 289/14, 119/6, 153/8, 391/21, 799/44,
    408/23, 833/48, 17, 459/26, 52/3, 477/28, 486/29, 33/2, 81/5, 437/26, 114/7, 95/6, 247/16,
    110/7, 290/19, 610/41, 130/9, 15]

/-- The band (0-based) of an activity: the number of interior edges `λ_1, …, λ_29` strictly below
`t`; band `i` is `(λ_i, λ_{i+1}]`, and band 0 also contains `λ_0 = 1/3`. -/
noncomputable def bandOf (t : ℝ) : ℕ := by
  classical
  exact ((List.range 29).filter fun i => (((edges.getD (i + 1) 0 : ℚ)) : ℝ) < t).length

/-- The upper edge `h = λ_{i+1}` of the band of `t`. -/
noncomputable def hiEdge (t : ℝ) : ℝ := ((edges.getD (bandOf t + 1) 0 : ℚ) : ℝ)

/-- The certified rate `ℓ(band of t, t_j)`. -/
noncomputable def ell (t : ℝ) (j : ℕ) : ℝ := (((rates.getD (bandOf t) []).getD j 0 : ℚ) : ℝ)

/-- One Laplace tail term `e^{−ℓ_j m} ((1 + h)/(1 + h t_j))^r`. -/
noncomputable def tailTerm (t m : ℝ) (r j : ℕ) : ℝ :=
  Real.exp (-(ell t j * m)) * ((1 + hiEdge t) / (1 + hiEdge t * ((tvals.getD j 0 : ℚ) : ℝ))) ^ r

/-- The lower-tail function the atlas prices: `min(1, min_j e^{−ℓ_j m} ((1 + h)/(1 + h t_j))^r)`. -/
noncomputable def tailFn (t m : ℝ) (r : ℕ) : ℝ :=
  min 1 (min (tailTerm t m r 0) (min (tailTerm t m r 1) (min (tailTerm t m r 2)
    (min (tailTerm t m r 3) (tailTerm t m r 4)))))

/-- **The certified profile** of the route. -/
noncomputable def P : Profile where
  θb := fun t => ((θt.getD (bandOf t) 1 : ℚ) : ℝ)
  Db := fun t => ((Dt.getD (bandOf t) (8/5) : ℚ) : ℝ)
  Tb := tailFn
  M1b := fun _ m => ⌈m⌉₊ + 1
  mfloor := fun t => ((mmin.getD (bandOf t) 0 : ℚ) : ℝ)

/-- Sanity checks on the data (sizes). -/
theorem edges_length : edges.length = 31 := by decide
theorem rates_length : rates.length = 30 ∧ ∀ r ∈ rates, r.length = 5 := by decide
theorem Dt_length : Dt.length = 30 := by decide
theorem θt_length : θt.length = 30 := by decide
theorem mmin_length : mmin.length = 30 := by decide

end Erdos993Lean.Analytic.Profile30
