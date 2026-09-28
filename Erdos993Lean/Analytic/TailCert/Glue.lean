import Mathlib
import Erdos993Lean.Analytic.Profile30
import Erdos993Lean.Analytic.Tail
import Erdos993Lean.Analytic.HardCore.Leaves
import Erdos993Lean.Analytic.HardCore.Mixture

/-!
# O3 for the certified profile from the band certificates (lane A10, the glue)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  Sources: `SOUL/O3/repaired_potential_proof.md`
(the repaired T3 potential and its H3 handoff), `SOUL/O3/repaired_band_XX_t_Y.json` (Soul's certified
parameters `a` and rates `ℓ` per band and Laplace parameter), T. Zhang, *Exact Certificates for
Unimodality of Forest Independence Polynomials*, v1.1, Lemma 4.1 (leaves of maximum-weight sets).

The tail function of `Profile30.P` is `T(λ, m, r) = min(1, min_j e^{−ℓ_j m} ((1 + h)/(1 + h t_j))^r)`
with `h` the upper edge of the band of `λ`.  Lane A3's `Tail.tail_t3` gives, for every forest, every
independent `B` with the leaf condition, `0 < λ ≤ 6`, `z = t_j`, `a ≥ 0`,
`ℓ ≤ log((1 + λ)/(1 + λ z))` and the reduced unit inequality `Tail.T3UNonneg λ z a ℓ`:
`P(M ≤ r) ≤ e^{−ℓ m} ((1 + λ)/(1 + λ z))^r`.

* `aTab`: Soul's coefficients `a(band i, t_j)`; the rates are `Profile30.rates` (all 150 values of
  field `"ell"` of the JSON files equal them; checked when this file was written).
* `BandCert i j`, `BandCertificates`: the named numerical input — `T3UNonneg λ t_j a(i, j) ℓ(i, j)`
  for every `λ` in the closed band `[λ_i, λ_{i+1}]`, for the 30 bands and five parameters.  It is
  discharged by the verified cell checker (`TailCert/Compute/Checker.lean`, sound by
  `TailCert.checkBand_sound` in `TailCert/Sound.lean`), evaluated band by band in the optional
  library `Erdos993LeanTailCert` (`TailCert.bandCertificates`, `TailCert/Main.lean`).
* `band_facts`: `0 ≤ a`, `0 ≤ t_j ≤ 1` and the isolated-vertex condition
  `ℓ(i, j) ≤ log((1 + λ)/(1 + λ t_j))` on the whole band (the right side increases with `λ`; at
  `λ_i` it is a rational check through `Real.exp_bound'`, evaluated by the kernel, `isoCheck_all`).
* `bandOf_spec`: an activity in range lies in the closed band `bandOf t`.
* `leafCondition_of_isMaxWeight`: a maximum-weight independent set at `t > 0` satisfies
  `Tail.LeafCondition` (from lane A1's `IsMaxWeight.leaf_mem`, `IsMaxWeight.edge_mem`).
* **`tailBound_profile30_of_certificates : BandCertificates → TailBound Profile30.P`.**

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound` (the data checks use
`decide +kernel`).

Scalarity check: `ℓ(i, j)` summarizes the Laplace transform of the free count `M` at `z = t_j` (T3-2,
lane A3 / Soul), `a(i, j)` is the coefficient of the potential in the certificate (consumed only by
`T3UNonneg`), the band edges delimit the activity domain of each certificate; the consumer is O3
(`TailBound`), i.e. T1's (H3).
-/

namespace Erdos993Lean.Analytic.TailCert

open Profile30

/-! ## The band data -/

/-- Soul's potential coefficient `a(band i, t_j)` of the repaired T3 potential (rows: bands
`0..29`; columns: `t_j ∈ {0, 1/20, 1/10, 1/5, 3/10}`), copied from the field `"a"` of
`SOUL/O3/repaired_band_XX_t_Y.json` (`XX = i + 1`). -/
def aTab : List (List ℚ) :=
  [ [51/2000, 121/5000, 23/1000, 51/2500, 89/5000],
    [67/2500, 127/5000, 241/10000, 107/5000, 187/10000],
    [71/2500, 27/1000, 16/625, 57/2500, 199/10000],
    [303/10000, 18/625, 273/10000, 121/5000, 53/2500],
    [161/5000, 153/5000, 29/1000, 129/5000, 9/400],
    [341/10000, 81/2500, 307/10000, 17/625, 119/5000],
    [359/10000, 341/10000, 323/10000, 18/625, 63/2500],
    [189/5000, 359/10000, 17/500, 151/5000, 53/2000],
    [397/10000, 377/10000, 357/10000, 159/5000, 139/5000],
    [26/625, 79/2000, 187/5000, 83/2500, 291/10000],
    [27/625, 411/10000, 389/10000, 173/5000, 303/10000],
    [28/625, 17/400, 403/10000, 179/5000, 313/10000],
    [231/5000, 439/10000, 26/625, 37/1000, 81/2500],
    [239/5000, 227/5000, 43/1000, 191/5000, 167/5000],
    [123/2500, 117/2500, 443/10000, 197/5000, 69/2000],
    [517/10000, 491/10000, 93/2000, 413/10000, 181/5000],
    [11/200, 261/5000, 99/2000, 11/250, 77/2000],
    [583/10000, 277/5000, 21/400, 467/10000, 51/1250],
    [617/10000, 293/5000, 111/2000, 493/10000, 27/625],
    [13/200, 309/5000, 117/2000, 13/250, 91/2000],
    [43/625, 653/10000, 619/10000, 11/200, 481/10000],
    [729/10000, 693/10000, 41/625, 583/10000, 51/1000],
    [387/5000, 147/2000, 697/10000, 619/10000, 271/5000],
    [823/10000, 781/10000, 37/500, 329/5000, 36/625],
    [871/10000, 827/10000, 49/625, 697/10000, 61/1000],
    [931/10000, 177/2000, 419/5000, 149/2000, 163/2500],
    [251/2500, 477/5000, 113/1250, 803/10000, 703/10000],
    [1077/10000, 1023/10000, 969/10000, 861/10000, 377/5000],
    [1161/10000, 1103/10000, 209/2000, 929/10000, 813/10000],
    [123/1000, 73/625, 1107/10000, 123/1250, 861/10000] ]

theorem aTab_length : aTab.length = 30 ∧ ∀ r ∈ aTab, r.length = 5 := by decide

/-- The band edge `λ_i` as a real number. -/
noncomputable def edgeR (i : ℕ) : ℝ := ((edges.getD i 0 : ℚ) : ℝ)

/-- The Laplace parameter `t_j` as a real number. -/
noncomputable def tR (j : ℕ) : ℝ := ((tvals.getD j 0 : ℚ) : ℝ)

/-- Soul's coefficient `a(band i, t_j)` as a real number. -/
noncomputable def aR (i j : ℕ) : ℝ := (((aTab.getD i []).getD j 0 : ℚ) : ℝ)

/-- The certified rate `ℓ(band i, t_j)` (`Profile30.rates`) as a real number. -/
noncomputable def ellR (i j : ℕ) : ℝ := (((rates.getD i []).getD j 0 : ℚ) : ℝ)

/-- **The certificate of band `i` at the Laplace parameter `t_j`**: the reduced unit inequality of
Theorem T3-2 (repaired), `Tail.T3UNonneg λ t_j a ℓ`, at every activity `λ` of the closed band
`[λ_i, λ_{i+1}]`, with Soul's `a = a(i, j)` and the certified rate `ℓ = ℓ(i, j)`. -/
def BandCert (i j : ℕ) : Prop :=
  ∀ lam : ℝ, edgeR i ≤ lam → lam ≤ edgeR (i + 1) →
    Tail.T3UNonneg lam (tR j) (aR i j) (ellR i j)

/-- **The band certificates** (the numerical input of O3 for `Profile30.P`): `BandCert i j` for
the 30 bands and the five Laplace parameters. -/
def BandCertificates : Prop := ∀ i < 30, ∀ j < 5, BandCert i j

/-! ## Numerical facts about the data (kernel `decide`) -/

theorem edges_lt_succ : ∀ i < 30, (edges.getD i 0 : ℚ) < edges.getD (i + 1) 0 := by
  decide +kernel

theorem edges_zero : (edges.getD 0 0 : ℚ) = 1 / 3 := by decide +kernel

theorem edges_thirty : (edges.getD 30 0 : ℚ) = 7 / 3 := by decide +kernel

theorem edges_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 30) :
    (edges.getD i 0 : ℚ) ≤ edges.getD j 0 := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (edges_lt_succ k (by omega)).le

theorem edgeR_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 30) : edgeR i ≤ edgeR j := by
  unfold edgeR
  exact_mod_cast edges_mono hij hj

/-- A fifth-order upper bound for `exp x` on `[0, 1]` (`Real.exp_bound'` with `n = 5`). -/
def expUp5 (x : ℚ) : ℚ := 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 * 6 / 600

/-- The isolated-vertex condition of one band and parameter, as a rational check at the lower
edge: `0 ≤ ℓ ≤ 1`, `0 ≤ a` and `expUp5 ℓ ≤ (1 + λ_i)/(1 + λ_i t_j)`. -/
def isoCheck (i j : ℕ) : Bool :=
  let l := (rates.getD i []).getD j 0
  let e := edges.getD i 0
  let t := tvals.getD j 0
  decide (0 ≤ l) && decide (l ≤ 1) && decide (0 ≤ (aTab.getD i []).getD j 0) &&
    decide (0 ≤ t) && decide (t ≤ 1) && decide (expUp5 l ≤ (1 + e) / (1 + e * t))

theorem isoCheck_all : ∀ i < 30, ∀ j < 5, isoCheck i j = true := by decide +kernel

theorem edges_pos (i : ℕ) (hi : i ≤ 30) : (1 / 3 : ℚ) ≤ edges.getD i 0 := by
  rw [← edges_zero]
  exact edges_mono (Nat.zero_le i) hi

theorem exp_le_expUp5 {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp (x : ℝ) ≤ ((expUp5 x : ℚ) : ℝ) := by
  have h := Real.exp_bound' (x := (x : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1)
    (n := 5) (by norm_num)
  refine h.trans (le_of_eq ?_)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, expUp5]
  push_cast
  ring

/-- The facts about one band and parameter that the glue uses: `0 ≤ a`, `0 ≤ t_j ≤ 1`, and the
isolated-vertex condition `ℓ ≤ log((1 + λ)/(1 + λ t_j))` on the whole band (the right side
increases with `λ`, so the check at `λ_i` suffices). -/
theorem band_facts {i j : ℕ} (hi : i < 30) (hj : j < 5) :
    0 ≤ aR i j ∧ 0 ≤ tR j ∧ tR j ≤ 1 ∧
      ∀ lam : ℝ, edgeR i ≤ lam → ellR i j ≤ Real.log ((1 + lam) / (1 + lam * tR j)) := by
  have hc := isoCheck_all i hi j hj
  simp only [isoCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hl0, hl1⟩, ha⟩, ht0⟩, ht1⟩, hexp⟩ := hc
  have he : (1 / 3 : ℚ) ≤ edges.getD i 0 := edges_pos i (by omega)
  refine ⟨by unfold aR; exact_mod_cast ha, by unfold tR; exact_mod_cast ht0,
    by unfold tR; exact_mod_cast ht1, ?_⟩
  intro lam hlam
  have heR : (1 / 3 : ℝ) ≤ edgeR i := by
    have h := (Rat.cast_le (K := ℝ)).mpr he
    unfold edgeR
    simpa using h
  have ht0' : (0 : ℝ) ≤ tR j := by unfold tR; exact_mod_cast ht0
  have ht1' : tR j ≤ 1 := by unfold tR; exact_mod_cast ht1
  -- `exp ℓ ≤ (1 + λ_i)/(1 + λ_i t) ≤ (1 + λ)/(1 + λ t)`
  have h1 : Real.exp (ellR i j) ≤ (1 + edgeR i) / (1 + edgeR i * tR j) := by
    have := exp_le_expUp5 hl0 hl1
    unfold ellR edgeR tR
    refine this.trans ?_
    have hq : ((expUp5 ((rates.getD i []).getD j 0) : ℚ) : ℝ) ≤
        (((1 + edges.getD i 0) / (1 + edges.getD i 0 * tvals.getD j 0) : ℚ) : ℝ) := by
      exact_mod_cast hexp
    refine hq.trans (le_of_eq ?_)
    push_cast
    ring
  have hlam0 : 0 ≤ lam := by linarith
  have h2 : (1 + edgeR i) / (1 + edgeR i * tR j) ≤ (1 + lam) / (1 + lam * tR j) := by
    have hd1 : 0 < 1 + edgeR i * tR j := by positivity
    have hd2 : 0 < 1 + lam * tR j := by positivity
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr ht1')]
  have hpos : 0 < (1 + lam) / (1 + lam * tR j) := by positivity
  rw [Real.le_log_iff_exp_le hpos]
  exact h1.trans h2

/-! ## The band of an activity -/

/-- For a predicate on `ℕ` that is closed downwards below `n`, the filter of `range n` is an
initial segment: `p j ↔ j < #(filter p (range n))` for `j < n`. -/
theorem mem_iff_lt_length_filter {p : ℕ → Bool} (n : ℕ)
    (hp : ∀ i j, i ≤ j → j < n → p j = true → p i = true) :
    ∀ j, j < n → (p j = true ↔ j < ((List.range n).filter p).length) := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hpn : p n = true
    · have hall : (List.range n).filter p = List.range n := by
        rw [List.filter_eq_self]
        intro a ha
        exact hp a n (by rw [List.mem_range] at ha; omega) (by omega) hpn
      rw [hall, List.length_range, List.filter_cons_of_pos hpn, List.filter_nil,
        List.length_singleton]
      constructor
      · intro _; omega
      · intro _; exact hp j n (by omega) (by omega) hpn
    · have hpn' : p n = false := by simpa using hpn
      rw [List.filter_cons_of_neg (by simp [hpn']), List.filter_nil, List.length_nil,
        Nat.add_zero]
      rcases Nat.lt_or_ge j n with hjn | hjn
      · exact ih (fun i j hij hjn' hj => hp i j hij (by omega) hj) j hjn
      · have hjn' : j = n := by omega
        subst hjn'
        constructor
        · intro h; exact absurd h hpn
        · intro h
          have := List.length_filter_le p (List.range j)
          rw [List.length_range] at this
          omega

/-- **The band of an activity in range**: `bandOf t < 30` and
`λ_{bandOf t} ≤ t ≤ λ_{bandOf t + 1}`. -/
theorem bandOf_spec {t : ℝ} (ht : InRange t) :
    bandOf t < 30 ∧ edgeR (bandOf t) ≤ t ∧ t ≤ edgeR (bandOf t + 1) := by
  classical
  set p : ℕ → Bool := fun i => decide ((((edges.getD (i + 1) 0 : ℚ)) : ℝ) < t) with hpdef
  have hb : bandOf t = ((List.range 29).filter p).length := by
    unfold bandOf
    rfl
  have hp : ∀ i j, i ≤ j → j < 29 → p j = true → p i = true := by
    intro i j hij hj29 hj
    simp only [hpdef, decide_eq_true_eq] at hj ⊢
    have := edgeR_mono (i := i + 1) (j := j + 1) (by omega) (by omega)
    unfold edgeR at this
    linarith
  have hiff := mem_iff_lt_length_filter 29 hp
  rw [← hb] at hiff
  have hk : bandOf t ≤ 29 := by
    rw [hb]
    have := List.length_filter_le p (List.range 29)
    rwa [List.length_range] at this
  refine ⟨by omega, ?_, ?_⟩
  · -- lower edge
    rcases Nat.eq_zero_or_pos (bandOf t) with h0 | hpos
    · rw [h0]
      unfold edgeR
      rw [edges_zero]
      have := ht.1
      push_cast
      linarith
    · have h := (hiff (bandOf t - 1) (by omega)).mpr (by omega)
      simp only [hpdef, decide_eq_true_eq] at h
      rw [show bandOf t - 1 + 1 = bandOf t by omega] at h
      exact h.le
  · -- upper edge
    rcases Nat.lt_or_ge (bandOf t) 29 with hlt | hge
    · have h : ¬ p (bandOf t) = true := fun h => absurd ((hiff _ hlt).mp h) (lt_irrefl _)
      simp only [hpdef, decide_eq_true_eq, not_lt] at h
      exact h
    · have h29 : bandOf t = 29 := by omega
      rw [h29]
      unfold edgeR
      rw [edges_thirty]
      have := ht.2
      push_cast
      linarith

/-! ## The leaf condition for maximum-weight sets -/

/-- **The bridge to T3's structural hypothesis** (Zhang, Lemma 4.1): a maximum-weight independent
set at `t > 0` satisfies T3's leaf condition `Tail.LeafCondition` (every C-vertex with a neighbour
`x` has a second neighbour, or `x ∈ B` and `x` has no other neighbour). -/
theorem leafCondition_of_isMaxWeight {F : FiniteForest} {t : ℝ} (ht : 0 < t)
    {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) : Tail.LeafCondition F.graph B := by
  intro c x hcB hcx
  by_cases h : ∃ y, y ≠ x ∧ F.graph.Adj c y
  · exact Or.inl h
  · right
    have hleaf : ∀ y, F.graph.Adj c y → y = x := fun y hy =>
      by_contra fun hne => h ⟨y, hne, hy⟩
    rcases hB.edge_mem ht hcx hleaf with ⟨hc, _⟩ | ⟨_, hx⟩
    · exact absurd hc hcB
    · refine ⟨hx, fun y hxy => ?_⟩
      by_contra hyc
      exact hcB (hB.leaf_mem ht hcx hleaf ⟨y, hxy, hyc⟩).2

/-! ## The tail bound -/

/-- `P(M ≤ M') ≤ 1` for the forest mixture of an independent set. -/
theorem cdfM_le_one (F : FiniteForest) {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) {t : ℝ} (ht : 0 < t) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤ 1 := by
  have hP := HardCore.forestMixture_isProb F hB ht
  unfold Mixture.cdfM
  rw [← hP.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun σ hσ _ => hP.1 σ hσ)

/-- The Laplace base increases with the activity: `(1 + λ)/(1 + λ z) ≤ (1 + h)/(1 + h z)` for
`0 ≤ λ ≤ h` and `0 ≤ z ≤ 1`. -/
theorem laplaceBase_mono {lam h z : ℝ} (hlam : 0 ≤ lam) (hh : lam ≤ h) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) : (1 + lam) / (1 + lam * z) ≤ (1 + h) / (1 + h * z) := by
  have hd1 : 0 < 1 + lam * z := by positivity
  have hd2 : 0 < 1 + h * z := by
    have : 0 ≤ h := hlam.trans hh
    positivity
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hz1)]

/-- **O3 for the certified profile, from the band certificates.**  If the reduced unit inequality
of Theorem T3-2 (repaired) holds on each of the 30 bands for the five Laplace parameters
(`BandCertificates`), then the lower tail of the free count obeys the profile's tail function:
`P(M ≤ r) ≤ min(1, min_j e^{−ℓ_j m} ((1 + h)/(1 + h t_j))^r)` (`TailBound Profile30.P`).

Proof: for an activity `t` in range, of band `i = bandOf t` (so `λ_i ≤ t ≤ λ_{i+1} = h`), and a
maximum-weight `B` (which satisfies the leaf condition, `leafCondition_of_isMaxWeight`), lane A3's
`Tail.tail_t3` with `(a, ℓ) = (a(i, j), ℓ(i, j))` gives `e^{−ℓ m} ((1 + t)/(1 + t t_j))^r`; the base
increases with the activity (`laplaceBase_mono`); the isolated-vertex condition is `band_facts`;
and `P(M ≤ r) ≤ 1` (`cdfM_le_one`). -/
theorem tailBound_profile30_of_certificates (hcert : BandCertificates) :
    TailBound Profile30.P := by
  intro F _ t ht _ B hB M' _
  obtain ⟨hi30, hlo, hhi⟩ := bandOf_spec ht
  have ht0 : 0 < t := by have := ht.1; linarith
  have hleaf := leafCondition_of_isMaxWeight ht0 hB
  have hBi := hB.1
  have hterm : ∀ j < 5, (forestMixture F B t).cdfM M' ≤
      tailTerm t (forestMixture F B t).meanM M' j := by
    intro j hj
    obtain ⟨ha, hz0, hz1, hiso⟩ := band_facts hi30 hj
    have h := Tail.tail_t3 F B hBi hleaf ht0 (by have := ht.2; linarith) hz0 hz1 ha
      (hiso t hlo) (hcert (bandOf t) hi30 j hj t hlo hhi) M'
    refine h.trans ?_
    unfold tailTerm
    have hbase := laplaceBase_mono ht0.le hhi hz0 hz1
    have hpow : ((1 + t) / (1 + t * tR j)) ^ M' ≤
        ((1 + edgeR (bandOf t + 1)) / (1 + edgeR (bandOf t + 1) * tR j)) ^ M' :=
      pow_le_pow_left₀ (by positivity) hbase M'
    have he : Real.exp (-ellR (bandOf t) j * (forestMixture F B t).meanM) =
        Real.exp (-(ell t j * (forestMixture F B t).meanM)) := by
      rw [neg_mul]
      rfl
    rw [← he]
    exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
  have h1 := cdfM_le_one F hBi ht0 M'
  show (forestMixture F B t).cdfM M' ≤ tailFn t (forestMixture F B t).meanM M'
  unfold tailFn
  exact le_min h1 (le_min (hterm 0 (by norm_num)) (le_min (hterm 1 (by norm_num))
    (le_min (hterm 2 (by norm_num)) (le_min (hterm 3 (by norm_num)) (hterm 4 (by norm_num))))))

end Erdos993Lean.Analytic.TailCert
