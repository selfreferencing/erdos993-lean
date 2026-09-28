import Erdos993Lean.Analytic.Profile30
import Erdos993Lean.Analytic.Density

/-!
# The 30 activity bands of `Profile30` and the floor of `m` from an integer rank

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Sources: Soul's
`SOUL/RESULTS/O5.md` §1 and §4 (adjudicated CORRECT, `LEAN/referee/REVIEW_SOUL_ROUND1.md`), and the
band data of `Profile30.lean` (Soul's `SOUL/O4/atlas_50/band_XX/SOURCE.json`).

* `bandOf_spec`: an activity `t ∈ [1/3, 7/3]` lies in its band, `λ_i ≤ t ≤ λ_{i+1}` for
  `i = bandOf t < 30` (strictly `λ_i < t` when `i > 0`).
* `mmin_eq`: the floor of band `i` is `mmin_i = k_i / (2 q(λ_{i+1}))` with the integer ranks
  `k_i = kmin_i ∈ {17, 18, 19, 20, 21}` (`kmin`; kernel `decide`).
* **`densityBound_of_rank`**: the O5 input `DensityBound Profile30.P` follows from the rank bound
  `kmin_{band(t)} ≤ k` at every interior-rank activity `μ_F(t) = k` of every forest with `n ≥ 61`,
  because `k = μ ≤ 2W = 2qm` (`two_mul_actQ_mul_meanM_ge`) and `q(t) ≤ q(λ_{i+1})`.
* **Bands 1–15** (0-based `i < 15`): `kmin_i = 17`; `mfloor_le_mfloorElem` compares the floor with
  the elementary floor of `Density.lean` and `densityBound_low` concludes (`meanM_ge_mfloorElem`);
  equivalently `kmin_le_of_low` gives the rank bound (`k > ⌈61/4⌉ = 16`).

Scalarity: the band edges `λ_i` and ranks `k_i` are rational data attached to the activity `λ`; the
object summarized is the expected free count `m = E M` (produced here from the integer rank
`k = μ_F(λ)`, consumed by the no-valley numerics O4 through `Profile.mfloor`).
-/

namespace Erdos993Lean.Analytic.Density

open Profile30

/-! ## The band edges -/

/-- The band edge `λ_i` as a real number. -/
noncomputable def edgeR (i : ℕ) : ℝ := ((edges.getD i 0 : ℚ) : ℝ)

theorem edges_lt_succ : ∀ i < 30, edges.getD i 0 < edges.getD (i + 1) 0 := by decide +kernel

theorem edges_zero : edges.getD 0 0 = 1 / 3 := by decide +kernel

theorem edges_thirty : edges.getD 30 0 = 7 / 3 := by decide +kernel

theorem edgesQ_lt {i j : ℕ} (hij : i < j) (hj : j ≤ 30) : edges.getD i 0 < edges.getD j 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := edges_lt_succ j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact (ih h (by omega)).trans h1
    · subst h
      exact h1

theorem edgeR_lt {i j : ℕ} (hij : i < j) (hj : j ≤ 30) : edgeR i < edgeR j := by
  unfold edgeR
  exact_mod_cast edgesQ_lt hij hj

theorem edgeR_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 30) : edgeR i ≤ edgeR j := by
  rcases hij.lt_or_eq with h | h
  · exact (edgeR_lt h hj).le
  · rw [h]

theorem edgeR_zero : edgeR 0 = 1 / 3 := by
  unfold edgeR
  rw [edges_zero]
  norm_num

theorem edgeR_thirty : edgeR 30 = 7 / 3 := by
  unfold edgeR
  rw [edges_thirty]
  norm_num

/-! ## Locating an activity in its band -/

/-- Counting a down-closed set of indices: if `f j` holds exactly for `j < b` (`b ≤ N`), then the
filter of `range N` by `f` has `b` elements. -/
theorem length_filter_range (f : ℕ → Bool) :
    ∀ {N b : ℕ}, b ≤ N → (∀ j < N, (f j = true ↔ j < b)) → ((List.range N).filter f).length = b
  | 0, b, hb, _ => by simp; omega
  | N + 1, b, hb, h => by
    rw [List.range_succ, List.filter_append, List.length_append]
    rcases Nat.lt_or_ge N b with hNb | hNb
    · have hb' : b = N + 1 := by omega
      have h1 := length_filter_range f (N := N) (b := N) le_rfl
        (fun j hj => by rw [h j (by omega)]; omega)
      have h2 : f N = true := (h N (by omega)).mpr hNb
      simp [h1, h2, hb']
    · have h1 := length_filter_range f (N := N) (b := b) hNb (fun j hj => h j (by omega))
      have h2 : f N = false := by
        rcases Bool.eq_false_or_eq_true (f N) with h3 | h3
        · have := (h N (by omega)).mp h3
          omega
        · exact h3
      simp [h1, h2]

/-- If `λ_i < t ≤ λ_{i+1}` (or `i = 0` and `t ≤ λ_1`), then `bandOf t = i`. -/
theorem bandOf_eq {t : ℝ} {i : ℕ} (hi : i < 30) (hlo : i = 0 ∨ edgeR i < t)
    (hhi : t ≤ edgeR (i + 1)) : bandOf t = i := by
  classical
  unfold bandOf
  apply length_filter_range _ (by omega)
  intro j hj
  rw [decide_eq_true_iff]
  change edgeR (j + 1) < t ↔ j < i
  constructor
  · intro h
    by_contra hji
    push_neg at hji
    have := edgeR_le (show i + 1 ≤ j + 1 by omega) (by omega)
    linarith
  · intro hji
    rcases hlo with h0 | hlo
    · omega
    · exact lt_of_le_of_lt (edgeR_le (show j + 1 ≤ i by omega) (by omega)) hlo

/-- Every activity `t ≤ 7/3` lies in some band `i < 30`: `λ_i < t ≤ λ_{i+1}` (or `i = 0`). -/
theorem exists_band {t : ℝ} (ht : t ≤ 7 / 3) :
    ∃ i < 30, (i = 0 ∨ edgeR i < t) ∧ t ≤ edgeR (i + 1) := by
  classical
  have hex : ∃ i, t ≤ edgeR (i + 1) := ⟨29, by rw [edgeR_thirty]; exact ht⟩
  have hi : t ≤ edgeR (Nat.find hex + 1) := Nat.find_spec hex
  have hi29 : Nat.find hex ≤ 29 := Nat.find_min' hex (by rw [edgeR_thirty]; exact ht)
  refine ⟨Nat.find hex, by omega, ?_, hi⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · exact Or.inl h
  · right
    have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at h1
    rwa [Nat.sub_add_cancel h] at h1

/-- **The band of an activity.**  For `t ∈ [1/3, 7/3]` and `i = bandOf t`: `i < 30`,
`λ_i ≤ t ≤ λ_{i+1}`, and `λ_i < t` unless `i = 0`. -/
theorem bandOf_spec {t : ℝ} (hR : InRange t) :
    bandOf t < 30 ∧ (bandOf t = 0 ∨ edgeR (bandOf t) < t) ∧ edgeR (bandOf t) ≤ t ∧
      t ≤ edgeR (bandOf t + 1) := by
  obtain ⟨i, hi, hlo, hhi⟩ := exists_band hR.2
  have hb := bandOf_eq hi hlo hhi
  rw [hb]
  refine ⟨hi, hlo, ?_, hhi⟩
  rcases hlo with h0 | h
  · rw [h0, edgeR_zero]
    exact hR.1
  · exact h.le

/-! ## The floors as integer ranks -/

/-- The integer rank `k_i` behind the floor of band `i`: `17` on bands 1–15 (`k > ⌈61/4⌉`), and
the ranks from the certified density records on bands 16–30. -/
def kmin : List ℕ :=
  [17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
    18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20, 20, 21]

/-- `mmin_i = k_i / (2 q(λ_{i+1}))` on every band (kernel `decide`). -/
theorem mmin_eq : ∀ i < 30, mmin.getD i 0 =
    (kmin.getD i 0 : ℚ) / (2 * (edges.getD (i + 1) 0 / (1 + edges.getD (i + 1) 0))) := by
  decide +kernel

theorem kmin_low : ∀ i < 15, kmin.getD i 0 = 17 := by decide +kernel

/-- `q = t/(1 + t)` is monotone on `t ≥ 0`. -/
theorem actQ_le_actQ {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : actQ a ≤ actQ b := by
  unfold actQ
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The floor of the band of `t` as a real number: `k_i / (2 q(λ_{i+1}))`. -/
theorem mfloor_eq {t : ℝ} (hR : InRange t) :
    Profile30.P.mfloor t = (kmin.getD (bandOf t) 0 : ℝ) / (2 * actQ (edgeR (bandOf t + 1))) := by
  have hb := (bandOf_spec hR).1
  have h := mmin_eq (bandOf t) hb
  change ((mmin.getD (bandOf t) 0 : ℚ) : ℝ) = _
  rw [h]
  unfold actQ edgeR
  push_cast
  ring

/-- **The O5 floor from an integer rank.**  If at every interior rank `μ_F(t) = k` of a forest with
`n ≥ 61` and `t ∈ [1/3, 7/3]` the rank satisfies `k_{band(t)} ≤ k`, then `DensityBound Profile30.P`
holds: `m ≥ k/(2q(t)) ≥ k_i/(2 q(λ_{i+1}))`. -/
theorem densityBound_of_rank
    (hrank : ∀ F : FiniteForest, 61 ≤ F.n → ∀ t : ℝ, InRange t → ∀ k : ℕ, (F.n + 3) / 4 < k →
      hardCoreMean F t = k → kmin.getD (bandOf t) 0 ≤ k) :
    DensityBound Profile30.P := by
  intro F hn t hR hI B hB
  obtain ⟨k, hk1, -, hμ⟩ := hI
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  obtain ⟨-, -, -, hhi⟩ := bandOf_spec hR
  have hkr : (kmin.getD (bandOf t) 0 : ℝ) ≤ k := by exact_mod_cast hrank F hn t hR k hk1 hμ
  have h2 := two_mul_actQ_mul_meanM_ge F ht hB
  rw [hμ] at h2
  have hq : 0 < actQ t := HardCore.actQ_pos ht
  have hqle : actQ t ≤ actQ (edgeR (bandOf t + 1)) := actQ_le_actQ ht.le hhi
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set m := (forestMixture F B t).meanM with hm
  have hm0 : 0 ≤ m := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  rw [mfloor_eq hR, div_le_iff₀ (by linarith)]
  nlinarith

/-- On bands 1–15 the rank bound is the interior-rank condition: `k > ⌈61/4⌉ = 16`. -/
theorem kmin_le_of_low {F : FiniteForest} (hn : 61 ≤ F.n) {t : ℝ} (hb : bandOf t < 15) {k : ℕ}
    (hk : (F.n + 3) / 4 < k) : kmin.getD (bandOf t) 0 ≤ k := by
  rw [kmin_low _ hb]
  omega

/-! ## Bands 1–15: the elementary floor -/

/-- On bands 1–15 the profile's floor `17/(2 q(λ_{i+1}))` lies below the elementary floor
`max (17/(2q), 61/(2(1 + 2q)))` of `Density.lean` (`q(t) ≤ q(λ_{i+1})`). -/
theorem mfloor_le_mfloorElem {t : ℝ} (hR : InRange t) (hb : bandOf t < 15) :
    Profile30.P.mfloor t ≤ mfloorElem t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  obtain ⟨-, -, -, hhi⟩ := bandOf_spec hR
  have hq : 0 < actQ t := HardCore.actQ_pos ht
  have hqle : actQ t ≤ actQ (edgeR (bandOf t + 1)) := actQ_le_actQ ht.le hhi
  rw [mfloor_eq hR, kmin_low _ hb]
  refine le_trans ?_ (le_max_left _ _)
  push_cast
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-- **O5 on bands 1–15.**  For a forest with `n ≥ 61`, an activity `t ∈ [1/3, 7/3]` in one of the
bands 1–15 at an interior rank, and a maximum-weight independent set `B`,
`Profile30.P.mfloor t ≤ m`. -/
theorem densityBound_low (F : FiniteForest) (hn : 61 ≤ F.n) {t : ℝ} (hR : InRange t)
    (hb : bandOf t < 15) (hI : AtInteriorRank F t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) : Profile30.P.mfloor t ≤ (forestMixture F B t).meanM :=
  le_trans (mfloor_le_mfloorElem hR hb)
    (meanM_ge_mfloorElem F hn (lt_of_lt_of_le (by norm_num) hR.1) hI hB)

end Erdos993Lean.Analytic.Density
