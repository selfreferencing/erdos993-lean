import Mathlib
import Erdos993Lean.Analytic.Reserve.UpperCert.CellSound
import Erdos993Lean.Analytic.Reserve.Cert.Sound

/-!
# Soundness of the checker of O1's upper finite box (lane A15)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  The computable checker is
`Erdos993Lean/Analytic/Reserve/UpperCert/Compute/Cell.lean`; the cell soundness is `cellOKU_sound`
(`Erdos993Lean/Analytic/Reserve/UpperCert/CellSound.lean`).  Lane A12's `inCell_halves`
(`Erdos993Lean/Analytic/Reserve/Cert/Sound.lean`) gives the cover of a cell by its halves.

**Theorems.**
* `Covered cell`: the four comparisons hold at every point of the cell; `covered_split`: a cell is covered when both
  halves along some axis are;
* `bisectOKU_sound`, `walkU_sound`: a passing adaptive bisection, and a passing trie walk (for **any** string, the
  data only steer the splits), cover the cell; **`covered_of_checkAt`**: `checkAt cell s = true` gives `Covered cell`
  (the form used for the pieces of the trie, one `native_decide` each);
* **`upperBoxOK_of_covered`**: `Covered rootU` gives `UpperBoxOK` (a point `(λ, T, Y)` of the box is the point
  `(λ, T, r)`, `r = (Y − y)/(4 − y) ∈ [0, 1]`, of the root cell `[8/5, 7/3] × [0, 6] × [0, 1]`);
* **`upperBoxOK_of_check`**: `checkUpper s = true` gives `UpperBoxOK`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound` (the floor of `E` is lane A13's
`entropyOK`, standard axioms).
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert

open Real Erdos993Lean.Analytic Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.Reserve.Cert
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.Reserve.Cert.Compute Erdos993Lean.Analytic.Reserve.UpperCert.Compute

/-! ## The cover -/

/-- Every point of the cell satisfies the four comparisons (at `Y = y + (4 − y) r`). -/
def Covered (cell : Cell) : Prop :=
  ∀ lam T r : ℝ, InCell cell lam T r → UGoal lam T (yF (lmass lam T) r)

/-- A cell is covered when both of its halves along some axis are. -/
theorem covered_split (cell : Cell) (j : ℕ) (h1 : Covered (lowHalf cell j))
    (h2 : Covered (highHalf cell j)) : Covered cell := by
  intro lam T r hin
  rcases inCell_halves hin j with hl | hh
  · exact h1 lam T r hl
  · exact h2 lam T r hh

/-- **The adaptive fallback is sound.** -/
theorem bisectOKU_sound : ∀ (f j : ℕ) (cell : Cell), bisectOKU f j cell = true → Covered cell := by
  intro f
  induction f with
  | zero =>
    intro j cell h lam T r hin
    exact cellOKU_sound h hin
  | succ f ih =>
    intro j cell h
    simp only [bisectOKU, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact fun lam T r hin => cellOKU_sound h hin
    · exact covered_split cell j (ih _ _ h1) (ih _ _ h2)

/-- **The trie walk is sound** (for any string `s`: the data only steer the splits). -/
theorem walkU_sound (s : String) : ∀ (f i : ℕ) (cell : Cell), (walkU s f i cell).1 = true → Covered cell := by
  intro f
  induction f with
  | zero =>
    intro i cell h
    simp [walkU] at h
  | succ f ih =>
    intro i cell h
    by_cases hch : String.Pos.Raw.get s ⟨i⟩ = 'L'
    · simp only [walkU, hch, if_true] at h
      exact bisectOKU_sound _ _ _ h
    · simp only [walkU, hch, if_false] at h
      set j := (String.Pos.Raw.get s ⟨i⟩).toNat - 48
      by_cases h1 : (walkU s f (i + 1) (lowHalf cell j)).1 = true
      · rw [if_pos h1] at h
        exact covered_split cell j (ih _ _ h1) (ih _ _ h)
      · rw [if_neg h1] at h
        simp at h

/-- **A passing check of a sub-box covers it.** -/
theorem covered_of_checkAt {cell : Cell} {s : String} (h : checkAt cell s = true) : Covered cell :=
  walkU_sound s walkFuel 0 cell h

/-- **The finite box of the upper band from its covered root box.** -/
theorem upperBoxOK_of_covered (h : Covered rootU) : UpperBoxOK := by
  intro lam T Y hl0 hl1 hT0 hT6 hyY hY4
  have hlam0 : 0 < lam := by linarith
  set y := lmass lam T with hydef
  have hy4 : y < 4 := (Cert.lmass_le hlam0.le hT0).trans_lt (by linarith)
  have h4y : 0 < 4 - y := by linarith
  set r := (Y - y) / (4 - y) with hrdef
  have hr0 : 0 ≤ r := div_nonneg (by linarith) h4y.le
  have hr1 : r ≤ 1 := (div_le_one h4y).mpr (by linarith)
  have hYeq : yF y r = Y := by
    rw [hrdef]; unfold yF; field_simp; ring
  have hin : InCell rootU lam T r := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show toR (ofRat (8 / 5)).lo ≤ lam
      have := (mem_ofRat (8 / 5)).1; push_cast at this; linarith
    · show lam ≤ toR (ofRat (7 / 3)).hi
      have := (mem_ofRat (7 / 3)).2; push_cast at this; linarith
    · show toR 0 ≤ T; rw [toR_zero]; exact hT0
    · show T ≤ toR (6 * one); rw [toR_int_mul_one]; exact_mod_cast hT6
    · show toR 0 ≤ r; rw [toR_zero]; exact hr0
    · show r ≤ toR one; rw [toR_one]; exact hr1
  have := h lam T r hin
  rw [hYeq] at this
  exact this

/-- **The finite box of the upper band from a passing check** (standard axioms; uses `entropyOK`). -/
theorem upperBoxOK_of_check (s : String) (h : checkUpper s = true) : UpperBoxOK :=
  upperBoxOK_of_covered (covered_of_checkAt h)

end Erdos993Lean.Analytic.Reserve.UpperCert
