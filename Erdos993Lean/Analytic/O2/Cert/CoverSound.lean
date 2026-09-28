import Mathlib
import Erdos993Lean.Analytic.O2.Cert.CellSound

/-!
# O2 certificate checker (lane A18): soundness of the cover

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The fallback bisection (`boxFB`, **`boxFB_sound`**), the
token walk over a root box (`walk`, **`walk_sound`**: `'l'`/`'x'` split, `'r'` a leaf) and the root-box check
(`checkRoot`, **`checkRoot_sound`**) certify every point of their boxes (`BoxGood`); the twelve root boxes cover
`x ∈ [2⁻¹⁶, 1]` (`edges_cover`), so twelve passing root checks certify the band (**`band_good`**).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The cover: fallback bisection, the token walk, the root boxes -/

/-- Every point of the box `[l0, l1] × [x0, x1]` is certified. -/
def BoxGood (sd : SegData) (l0 l1 x0 x1 : ℚ) : Prop :=
  ∀ l x : ℝ, (l0 : ℝ) ≤ l → l ≤ l1 → (x0 : ℝ) ≤ x → x ≤ x1 → PointGood sd l x

theorem boxGood_split_l {sd : SegData} {l0 m l1 x0 x1 : ℚ} (h1 : BoxGood sd l0 m x0 x1)
    (h2 : BoxGood sd m l1 x0 x1) : BoxGood sd l0 l1 x0 x1 := fun l x hl0 hl1 hx0 hx1 => by
  rcases le_total l m with h | h
  · exact h1 l x hl0 h hx0 hx1
  · exact h2 l x h hl1 hx0 hx1

theorem boxGood_split_x {sd : SegData} {l0 l1 x0 m x1 : ℚ} (h1 : BoxGood sd l0 l1 x0 m)
    (h2 : BoxGood sd l0 l1 m x1) : BoxGood sd l0 l1 x0 x1 := fun l x hl0 hl1 hx0 hx1 => by
  rcases le_total x m with h | h
  · exact h1 l x hl0 hl1 hx0 h
  · exact h2 l x hl0 hl1 h hx1

/-- **Soundness of the fallback bisection.** -/
theorem boxFB_sound {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) :
    ∀ (f : ℕ) (l0 l1 x0 x1 : ℚ), boxFB sd f l0 l1 x0 x1 = true → BoxGood sd l0 l1 x0 x1
  | 0, l0, l1, x0, x1, h => fun l x h1 h2 h3 h4 => boxOK_sound hγ (by simpa [boxFB] using h) h1 h2 h3 h4
  | f + 1, l0, l1, x0, x1, h => by
    simp only [boxFB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact fun l x h1 h2 h3 h4 => boxOK_sound hγ h h1 h2 h3 h4
    · split_ifs at h
      · simp only [Bool.and_eq_true] at h
        exact boxGood_split_l (boxFB_sound hγ f _ _ _ _ h.1) (boxFB_sound hγ f _ _ _ _ h.2)
      · simp only [Bool.and_eq_true] at h
        exact boxGood_split_x (boxFB_sound hγ f _ _ _ _ h.1) (boxFB_sound hγ f _ _ _ _ h.2)

/-- **Soundness of the token walk**: a successful walk certifies its box. -/
theorem walk_sound {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) (s : String) :
    ∀ (f i : ℕ) (l0 l1 x0 x1 : ℚ), (walk sd s f i l0 l1 x0 x1).1 = true → BoxGood sd l0 l1 x0 x1
  | 0, i, l0, l1, x0, x1, h => by simp [walk] at h
  | f + 1, i, l0, l1, x0, x1, h => by
    simp only [walk] at h
    split_ifs at h
    all_goals first
      | exact boxFB_sound hγ fallbackDepth l0 l1 x0 x1 h
      | exact boxGood_split_l (walk_sound hγ s f _ _ _ _ _ (by assumption)) (walk_sound hγ s f _ _ _ _ _ h)
      | exact boxGood_split_x (walk_sound hγ s f _ _ _ _ _ (by assumption)) (walk_sound hγ s f _ _ _ _ _ h)
      | simp at h

/-- **Soundness of a root-box check.** -/
theorem checkRoot_sound {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) {i : ℕ} {s : String}
    (h : checkRoot sd i s = true) : BoxGood sd sd.lo sd.hi (edges.getD i 0) (edges.getD (i + 1) 0) := by
  unfold checkRoot rootOK at h
  simp only [Bool.and_eq_true] at h
  exact walk_sound hγ s 64 0 _ _ _ _ h.1

/-- The twelve root boxes cover `x ∈ [2⁻¹⁶, 1]`. -/
theorem edges_cover {x : ℝ} (h0 : (1 / 65536 : ℝ) ≤ x) (h1 : x ≤ 1) :
    ∃ i < 12, ((edges.getD i 0 : ℚ) : ℝ) ≤ x ∧ x ≤ ((edges.getD (i + 1) 0 : ℚ) : ℝ) := by
  have e : ∀ i, i < 13 → ∃ q : ℚ, edges.getD i 0 = q := fun i _ => ⟨_, rfl⟩
  by_cases c1 : x ≤ 1 / 4096
  · exact ⟨0, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c2 : x ≤ 1 / 1024
  · exact ⟨1, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c3 : x ≤ 1 / 256
  · exact ⟨2, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c4 : x ≤ 1 / 64
  · exact ⟨3, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c5 : x ≤ 1 / 8
  · exact ⟨4, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c6 : x ≤ 2 / 8
  · exact ⟨5, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c7 : x ≤ 3 / 8
  · exact ⟨6, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c8 : x ≤ 4 / 8
  · exact ⟨7, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c9 : x ≤ 5 / 8
  · exact ⟨8, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c10 : x ≤ 6 / 8
  · exact ⟨9, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  by_cases c11 : x ≤ 7 / 8
  · exact ⟨10, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩
  · exact ⟨11, by norm_num, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith, by simp only [edges, List.getD_cons_zero, List.getD_cons_succ]; push_cast; linarith⟩

/-- **A band is certified** by its twelve root-box checks: every `λ ∈ [lo, hi]` and `x ∈ [2⁻¹⁶, 1]`. -/
theorem band_good {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) {toks : List String}
    (h : ∀ i < 12, checkRoot sd i (toks.getD i "") = true) {l x : ℝ} (hl0 : (sd.lo : ℝ) ≤ l) (hl1 : l ≤ sd.hi)
    (hx0 : (1 / 65536 : ℝ) ≤ x) (hx1 : x ≤ 1) : PointGood sd l x := by
  obtain ⟨i, hi, h1, h2⟩ := edges_cover hx0 hx1
  exact checkRoot_sound hγ (h i hi) l x hl0 hl1 h1 h2

end Erdos993Lean.Analytic.O2.Cert
