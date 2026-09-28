import Mathlib
import Erdos993Lean.Analytic.Reserve.Cert.CellSound

/-!
# Soundness of the box checker and of the leaf-base checker (lane A12)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A12.  The computable checkers are in
`Erdos993Lean/Analytic/Reserve/Cert/Compute/Cell.lean`; the cell soundness is `cellOK_sound`
(`Erdos993Lean/Analytic/Reserve/Cert/CellSound.lean`).

**Theorems.**
* `bisectOK_sound`, `walk_sound`: a passing adaptive bisection, and a passing trie walk (for **any** string, the
  data only steer the splits), give `CompOK` at every point of the cell (each split covers the cell:
  `inCell_halves`);
* **`boxOK_of_check`**: `checkBand c.lo c.hi c.D c.aCoef c.gDen s = true` gives `BoxOK c` (no hypothesis on
  the band, no `EntropyOK`): a point `(λ, T, Y)` of the box is the point `(λ, T, r)`, `r = (Y − y)/(4 − y) ∈ [0, 1]`,
  of the root cell `[lo, hi] × [0, 6] × [0, 1]`;
* `leafCellOK_sound`, `leafCover_sound`, **`leafOK_of_check`**: `checkLeaf c.lo c.hi c.D c.aCoef c.gDen = true`
  gives `LeafOK c` (`α ℓ + γ q²/ℓ = q² (aCoef ℓ/q + γ/ℓ)`, `ℓ = log(1 + λ)`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.Reserve.Cert

open Real Erdos993Lean.Analytic Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.Reserve.Cert.Compute

/-! ## The cover -/

/-- A point of a cell lies in one of its two halves along any axis. -/
theorem inCell_halves {cell : Cell} {lam T r : ℝ} (hin : InCell cell lam T r) (j : ℕ) :
    InCell (lowHalf cell j) lam T r ∨ InCell (highHalf cell j) lam T r := by
  match j with
  | 0 =>
    rcases le_total lam (toR (midI cell.a0 cell.a1)) with h | h
    · exact Or.inl ⟨hin.a0, h, hin.t0, hin.t1, hin.r0, hin.r1⟩
    · exact Or.inr ⟨h, hin.a1, hin.t0, hin.t1, hin.r0, hin.r1⟩
  | 1 =>
    rcases le_total T (toR (midI cell.t0 cell.t1)) with h | h
    · exact Or.inl ⟨hin.a0, hin.a1, hin.t0, h, hin.r0, hin.r1⟩
    · exact Or.inr ⟨hin.a0, hin.a1, h, hin.t1, hin.r0, hin.r1⟩
  | _ + 2 =>
    rcases le_total r (toR (midI cell.r0 cell.r1)) with h | h
    · exact Or.inl ⟨hin.a0, hin.a1, hin.t0, hin.t1, hin.r0, h⟩
    · exact Or.inr ⟨hin.a0, hin.a1, hin.t0, hin.t1, h, hin.r1⟩

section Cover

variable (c : Band)

/-- **The adaptive fallback is sound.** -/
theorem bisectOK_sound : ∀ (f j : ℕ) (cell : Cell),
    bisectOK (mkConsts c.D c.aCoef c.gDen) f j cell = true →
    ∀ lam T r, InCell cell lam T r → CompOK c lam T (yF (lmass lam T) r) := by
  intro f
  induction f with
  | zero =>
    intro j cell h lam T r hin
    exact cellOK_sound c h hin
  | succ f ih =>
    intro j cell h lam T r hin
    simp only [bisectOK, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact cellOK_sound c h hin
    · rcases inCell_halves hin j with hl | hh
      · exact ih _ _ h1 lam T r hl
      · exact ih _ _ h2 lam T r hh

/-- **The trie walk is sound** (for any string `s`: the data only steer the splits). -/
theorem walk_sound (s : String) : ∀ (f i : ℕ) (cell : Cell),
    (walk (mkConsts c.D c.aCoef c.gDen) s f i cell).1 = true →
    ∀ lam T r, InCell cell lam T r → CompOK c lam T (yF (lmass lam T) r) := by
  intro f
  induction f with
  | zero =>
    intro i cell h
    simp [walk] at h
  | succ f ih =>
    intro i cell h lam T r hin
    by_cases hch : String.Pos.Raw.get s ⟨i⟩ = 'L'
    · simp only [walk, hch, if_true] at h
      exact bisectOK_sound c _ _ _ h lam T r hin
    · simp only [walk, hch, if_false] at h
      set j := (String.Pos.Raw.get s ⟨i⟩).toNat - 48
      by_cases h1 : (walk (mkConsts c.D c.aCoef c.gDen) s f (i + 1) (lowHalf cell j)).1 = true
      · rw [if_pos h1] at h
        rcases inCell_halves hin j with hl | hh
        · exact ih _ _ h1 lam T r hl
        · exact ih _ _ h lam T r hh
      · rw [if_neg h1] at h
        simp at h

end Cover

/-- **The finite box from a passing band check**: `checkBand c.lo c.hi c.D c.aCoef c.gDen s = true` gives
`BoxOK c`. -/
theorem boxOK_of_check (c : Band) (s : String)
    (h : checkBand c.lo c.hi c.D c.aCoef c.gDen s = true) : BoxOK c := by
  simp only [checkBand, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlo, hhi⟩, hw⟩ := h
  have hlo' : (0 : ℝ) < c.lo := by exact_mod_cast hlo
  have hhi' : (c.hi : ℝ) < 4 := by exact_mod_cast hhi
  intro lam T Y hl0 hl1 hT0 hT6 hyY hY4
  have hlam0 : 0 < lam := hlo'.trans_le hl0
  set y := lmass lam T with hydef
  have hy4 : y < 4 := (lmass_le hlam0.le hT0).trans_lt (hl1.trans_lt hhi')
  have h4y : 0 < 4 - y := by linarith
  set r := (Y - y) / (4 - y) with hrdef
  have hr0 : 0 ≤ r := div_nonneg (by linarith) h4y.le
  have hr1 : r ≤ 1 := (div_le_one h4y).mpr (by linarith)
  have hYeq : yF y r = Y := by
    rw [hrdef]; unfold yF; field_simp; ring
  have hin : InCell (rootCell c.lo c.hi) lam T r := by
    refine ⟨(mem_ofRat c.lo).1.trans hl0, hl1.trans (mem_ofRat c.hi).2, ?_, ?_, ?_, ?_⟩
    · show toR 0 ≤ T; rw [toR_zero]; exact hT0
    · show T ≤ toR (6 * one); rw [toR_int_mul_one]; exact_mod_cast hT6
    · show toR 0 ≤ r; rw [toR_zero]; exact hr0
    · show r ≤ toR one; rw [toR_one]; exact hr1
  have := walk_sound c s walkFuel 0 _ hw lam T r hin
  rwa [hYeq] at this

/-! ## The selected-leaf base -/

/-- A passing leaf cell `[a0, a1]`: the leaf base at every `λ ∈ [a0, a1]`. -/
theorem leafCellOK_sound (c : Band) {a0 a1 : ℤ} (h : leafCellOK c.D c.aCoef c.gDen a0 a1 = true)
    {lam : ℝ} (h0 : toR a0 ≤ lam) (h1 : lam ≤ toR a1) :
    alpha c lam * log (1 + lam) + gamma c lam * actQ lam ^ 2 / log (1 + lam) ≤
      (c.D : ℝ) * actQ lam ^ 2 := by
  simp only [leafCellOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha0, hq⟩, hell⟩, hlhs⟩ := h
  have one0 := one_pos'
  have hlam0 : 0 < lam := (toR_pos.mpr ha0).trans_le h0
  have mL : (⟨a0, a1⟩ : Ival).Mem lam := ⟨h0, h1⟩
  have p1L : 0 < (add oneI (⟨a0, a1⟩ : Ival)).lo := by
    show 0 < one + a0; omega
  have mq : (sub oneI (div oneI (add oneI (⟨a0, a1⟩ : Ival)))).Mem (actQ lam) := by
    rw [actQ_eq hlam0.le]
    exact mem_sub mem_oneI (mem_div mem_oneI (mem_add mem_oneI mL) p1L)
  have mgam : (mul (mul (⟨a0, a1⟩ : Ival) (add threeI ⟨a0, a1⟩)) (ofRat (1 / c.gDen))).Mem
      (gamma c lam) := by
    have h := mem_mul (mem_mul mL (mem_add mem_threeI mL)) (mem_ofRat (1 / c.gDen))
    have e : lam * (3 + lam) * (((1 / c.gDen : ℚ)) : ℝ) = gamma c lam := by
      unfold gamma; push_cast; ring
    rw [e] at h; exact h
  have mell : (logI (add oneI (⟨a0, a1⟩ : Ival))).Mem (log (1 + lam)) :=
    mem_logI (mem_add mem_oneI mL) p1L
  have mlhs := mem_add (mem_mul (mem_ofRat c.aCoef) (mem_div mell mq hq)) (mem_div mgam mell hell)
  have hle : (c.aCoef : ℝ) * (log (1 + lam) / actQ lam) + gamma c lam / log (1 + lam) ≤ c.D :=
    mlhs.2.trans ((toR_le_toR.mpr hlhs).trans (mem_ofRat c.D).1)
  have hq0 : 0 < actQ lam := by unfold actQ; positivity
  have hl0 : 0 < log (1 + lam) := log_pos (by linarith)
  have e : alpha c lam * log (1 + lam) + gamma c lam * actQ lam ^ 2 / log (1 + lam) =
      actQ lam ^ 2 * ((c.aCoef : ℝ) * (log (1 + lam) / actQ lam) + gamma c lam / log (1 + lam)) := by
    unfold alpha; field_simp
  rw [e, mul_comm (c.D : ℝ)]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- The leaf-base bisection is sound. -/
theorem leafCover_sound (c : Band) : ∀ (f : ℕ) (a0 a1 : ℤ),
    leafCover c.D c.aCoef c.gDen f a0 a1 = true → ∀ lam : ℝ, toR a0 ≤ lam → lam ≤ toR a1 →
      alpha c lam * log (1 + lam) + gamma c lam * actQ lam ^ 2 / log (1 + lam) ≤
        (c.D : ℝ) * actQ lam ^ 2 := by
  intro f
  induction f with
  | zero =>
    intro a0 a1 h lam h0 h1
    exact leafCellOK_sound c h h0 h1
  | succ f ih =>
    intro a0 a1 h lam h0 h1
    simp only [leafCover, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h2, h3⟩
    · exact leafCellOK_sound c h h0 h1
    · rcases le_total lam (toR (midI a0 a1)) with hm | hm
      · exact ih _ _ h2 lam h0 hm
      · exact ih _ _ h3 lam hm h1

/-- **The leaf base from a passing check**: `checkLeaf c.lo c.hi c.D c.aCoef c.gDen = true` gives `LeafOK c`. -/
theorem leafOK_of_check (c : Band) (h : checkLeaf c.lo c.hi c.D c.aCoef c.gDen = true) : LeafOK c := by
  intro lam hl0 hl1
  exact leafCover_sound c 30 _ _ h lam ((mem_ofRat c.lo).1.trans hl0) (hl1.trans (mem_ofRat c.hi).2)

end Erdos993Lean.Analytic.Reserve.Cert
