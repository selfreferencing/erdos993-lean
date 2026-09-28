import Mathlib
import Erdos993Lean.Analytic.TailCert.ExpLog
import Erdos993Lean.Analytic.TailCert.Mono
import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# The inner table of the cell checker: soundness (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  Soundness of the inner table of
`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`: a lower bound of
`ψ_c(x) = (a T_λ(x) + [x < q] k That_+(T_λ(x)) − k L(x) − c x)/L(x)` (`psiF`; `T3phi/L = psiF` at
`c = T3c`, `T3phi_div_Lf`) uniform over the band.

* `aloAt_le`: on grid cell `[x_m, x_{m+1}]`, `alo m ≤ (a T + [x < q] k That_+(T))/L − k` (with
  `T_λ(x) ≥ T_{l0}(x_{m+1})`, and the That credit `k0 max(V, 0)/L(x_{m+1})` when `x_{m+1} < q(l0)`,
  `V ≤ That(T_λ(x))` by `That_Tf_ge`); `le_bhiAt`: `x/L(x) ≤ bhi m` (`div_Lf_anti`);
* `tget_spec`: the table entry `tbl j n` is at most `0` and at most `alo m − C_j bhi m` for `m < n`
  (running minima, `pmins_getD`);
* `psiF_nonneg_tiny`: `ψ_c ≥ 0` below `x_0 = 2^-46` (`tinyOK`);
* **`query_sound`**: `queryVal pm cf ≤ ψ_c(x)` for `0 ≤ c ≤ cf`, `0 < x ≤ pm`, `λ` in
  the band: `x` lies in a grid cell `m < n` below `pm` (`exists_cell`) or in the tiny region, and
  `alo m − cf bhi m` is the convex combination of the two neighbouring c-grid values
  (interpolation is exact for affine functions of `c`);  `queryVal_nonpos`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.TailCert

open Compute Tail

/-! ## Arrays and lists -/

theorem getD_map_range {α : Type*} (f : ℕ → α) {n i : ℕ} (d : α) (hi : i < n) :
    ((List.range n).toArray.map f).getD i d = f i := by
  simp [Array.getD, hi]

theorem array_getD_toArray {α : Type*} (l : List α) (i : ℕ) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  simp only [Array.getD, List.size_toArray, List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [List.getElem?_eq_none (not_lt.mp h)]

theorem allLt_iff (n : ℕ) (f : ℕ → Bool) : allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h1 i h
      · exact h ▸ h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- The running minima: entry `i ≤ k` of `pmins f k m acc` is at most `acc` and at most `f (m + j)`
for every `j < i`. -/
theorem pmins_getD (f : ℕ → ℤ) : ∀ (k m : ℕ) (acc : ℤ) (i : ℕ), i ≤ k →
    (pmins f k m acc).getD i 0 ≤ acc ∧ ∀ j < i, (pmins f k m acc).getD i 0 ≤ f (m + j) := by
  intro k
  induction k with
  | zero =>
    intro m acc i hi
    have : i = 0 := by omega
    subst this
    simp [pmins]
  | succ k ih =>
    intro m acc i hi
    rcases i with _ | i
    · simp [pmins]
    · have h := ih (m + 1) (min acc (f m)) i (by omega)
      simp only [pmins, List.getD_cons_succ]
      refine ⟨h.1.trans (min_le_left _ _), ?_⟩
      intro j hj
      rcases j with _ | j
      · simpa using h.1.trans (min_le_right _ _)
      · have := h.2 j (by omega)
        rwa [show m + 1 + j = m + (j + 1) by omega] at this

/-! ## The grid -/

theorem xg_pos (i : ℕ) : 0 < xg i := by
  unfold xg
  split_ifs
  · simp only [Nat.one_shiftLeft]; positivity
  · simp only [Nat.shiftLeft_eq]
    have : 0 < i - 32 := by omega
    positivity

/-- A point of `(f 0, f n]` lies in some grid cell `(f m, f (m+1)]` with `m < n`. -/
theorem exists_cell {f : ℕ → ℝ} {x : ℝ} (h0 : f 0 < x) :
    ∀ n, x ≤ f n → ∃ m < n, f m < x ∧ x ≤ f (m + 1) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (not_le.mpr h0)
  | succ n ih =>
    intro h
    by_cases hn : x ≤ f n
    · obtain ⟨m, hm, h1, h2⟩ := ih hn
      exact ⟨m, by omega, h1, h2⟩
    · exact ⟨n, by omega, not_le.mp hn, h⟩

/-! ## The function `ψ_c` -/

/-- `ψ_c(x) = (a T_λ(x) + [x < q] k That_+(T_λ(x)) − k L(x) − c x)/L(x)` with `k = a r(λ)`. -/
noncomputable def psiF (lam a c x : ℝ) : ℝ :=
  (a * Tf lam x + (if x < actQ lam then kK lam a * ThatPlus lam (Tf lam x) else 0) -
    kK lam a * Lf x - c * x) / Lf x

theorem T3phi_div_Lf (lam a ell s x : ℝ) :
    T3phi lam a ell s x / Lf x = psiF lam a (T3c lam ell s) x := rfl

/-- `ψ_c = (a T + [x < q] k That_+(T))/L − k − c x/L`. -/
theorem psiF_eq {lam a c x : ℝ} (hL : 0 < Lf x) :
    psiF lam a c x = (a * Tf lam x + (if x < actQ lam then kK lam a * ThatPlus lam (Tf lam x) else 0)) /
      Lf x - kK lam a - c * (x / Lf x) := by
  unfold psiF
  field_simp

end Erdos993Lean.Analytic.TailCert

namespace Erdos993Lean.Analytic.TailCert

open Compute Tail

/-! ## Enclosures of the grid quantities -/

/-- `λ` lies in the band `[l0, l1]` of the setup. -/
def InBand (S : Setup) (lam : ℝ) : Prop := (S.l0 : ℝ) ≤ lam ∧ lam ≤ (S.l1 : ℝ)

theorem toR_xg_pos (i : ℕ) : 0 < toR (xg i) := toR_pos.mpr (xg_pos i)

theorem toR_lt_one {n : ℤ} (h : n < one) : toR n < 1 := by
  rw [← toR_one]; exact toR_lt_toR.mpr h

/-- `L(x_i) ∈ LxAt i` for `x_i < 1`. -/
theorem LxAt_mem {i : ℕ} (h : xg i < one) : (LxAt i).Mem (Lf (toR (xg i))) := by
  have hsub := mem_sub (mem_pt one) (mem_pt (xg i))
  rw [toR_one] at hsub
  have hpos : 0 < (sub (pt one) (pt (xg i))).lo := by
    show 0 < one - xg i
    omega
  exact mem_neg (mem_logI hsub hpos)

/-- `l0 (1 − x)/x ∈ TArg L0 x` for `x > 0`. -/
theorem TArg_mem {L0 : Ival} {l0 : ℝ} (hL0 : L0.Mem l0) {x : ℤ} (hx : 0 < x) :
    (TArg L0 x).Mem (l0 * (1 - toR x) / toR x) := by
  have h := mem_div (mem_mul hL0 (mem_sub (mem_pt one) (mem_pt x))) (mem_pt x) hx
  rwa [toR_one] at h

/-- The lower bound `TloAt L0 x ≤ T_{l0}(x)`. -/
theorem TloAt_le {L0 : Ival} {l0 : ℝ} (hL0 : L0.Mem l0) {x : ℤ} (hx : 0 < x)
    (hpos : 0 < (TArg L0 x).lo) : toR (TloAt L0 x) ≤ Tf l0 (toR x) :=
  logI_lo_le (TArg_mem hL0 hx) hpos

/-- `l1 (1 − x) − x ∈ denAt L1 x`. -/
theorem denAt_mem {L1 : Ival} {l1 : ℝ} (hL1 : L1.Mem l1) (x : ℤ) :
    (denAt L1 x).Mem (l1 * (1 - toR x) - toR x) := by
  have h := mem_sub (mem_mul hL1 (mem_sub (mem_pt one) (mem_pt x))) (mem_pt x)
  rwa [toR_one] at h

/-! ## The grid cells -/

section Cells

variable {S : Setup}

/-- The facts about the band constants that the grid cells use. -/
structure ConstOK (S : Setup) : Prop where
  l0pos : (0 : ℝ) < S.l0
  a0 : (0 : ℝ) ≤ S.a
  memA : S.A.Mem S.a
  memL0 : S.L0.Mem S.l0
  memL1 : S.L1.Mem S.l1
  k0le : ∀ lam, InBand S lam → toR S.k0 ≤ kK lam S.a
  lek1 : ∀ lam, InBand S lam → kK lam S.a ≤ toR S.k1
  k0nn : 0 ≤ toR S.k0
  q0 : ∀ lam, InBand S lam → toR S.q0lo ≤ actQ lam

/-- **The lower bound of grid cell `m`**: `alo m ≤ (a T + [x < q] k That_+(T))/L − k` on
`[x_m, x_{m+1}]`. -/
theorem aloAt_le (hS : ConstOK S) {m : ℕ} (hLxm : S.Lx.getD m default = LxAt m)
    (hLxm1 : S.Lx.getD (m + 1) default = LxAt (m + 1)) (hc : pcellOK S m = true) {lam x : ℝ}
    (hlam : InBand S lam) (hx1 : toR (xg m) ≤ x) (hx2 : x ≤ toR (xg (m + 1))) :
    toR (aloAt S.L0 S.L1 S.A S.q0lo S.k0 S.k1 S.Lx m) ≤
      (S.a * Tf lam x + (if x < actQ lam then kK lam S.a * ThatPlus lam (Tf lam x) else 0)) /
        Lf x - kK lam S.a := by
  simp only [pcellOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hxm, hxm1⟩, hLpos⟩, hTpos⟩, hk⟩ := hc
  have hxm0 : 0 < toR (xg m) := toR_xg_pos m
  have hxm1' : toR (xg (m + 1)) < 1 := toR_lt_one hxm1
  have hx0 : 0 < x := hxm0.trans_le hx1
  have hxlt1 : x < 1 := hx2.trans_lt hxm1'
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hLx0 : 0 < Lf x := Lf_pos hx0 hxlt1
  have hmemLm := LxAt_mem hxm
  have hmemLm1 := LxAt_mem hxm1
  have hLr : (⟨(S.Lx.getD m default).lo, (S.Lx.getD (m + 1) default).hi⟩ : Ival).Mem (Lf x) := by
    rw [hLxm, hLxm1]
    exact ⟨hmemLm.1.trans (Lf_mono hx1 hxlt1), (Lf_mono hx2 hxm1').trans hmemLm1.2⟩
  have hT : toR (TloAt S.L0 (xg (m + 1))) ≤ Tf lam x :=
    (TloAt_le hS.memL0 (xg_pos _) hTpos).trans (Tf_mono hS.l0pos hlam.1 hx0 hx2 hxm1')
  -- the term `a T/L`
  have h1 : toR (div (mul S.A (pt (TloAt S.L0 (xg (m + 1)))))
      ⟨(S.Lx.getD m default).lo, (S.Lx.getD (m + 1) default).hi⟩).lo ≤ S.a * Tf lam x / Lf x := by
    have hmem := mem_div (mem_mul hS.memA (mem_pt (TloAt S.L0 (xg (m + 1))))) hLr hLpos
    refine hmem.1.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT hS.a0) hLx0.le
  -- the That credit
  have hk0 : 0 ≤ kK lam S.a := kK_nonneg hlam0 hS.a0
  have hind0 : 0 ≤ (if x < actQ lam then kK lam S.a * ThatPlus lam (Tf lam x) else 0) := by
    split_ifs
    · exact mul_nonneg hk0 (ThatPlus_nonneg _ _)
    · exact le_rfl
  have h2 : toR (kthAt S.L1 S.q0lo S.k0 S.Lx m) ≤
      (if x < actQ lam then kK lam S.a * ThatPlus lam (Tf lam x) else 0) / Lf x := by
    unfold kthAt
    by_cases hq : xg (m + 1) < S.q0lo
    · rw [if_pos hq]
      by_cases hV : 0 < VAt S.L1 (xg m)
      swap
      · rw [if_neg hV, toR_zero]; exact div_nonneg hind0 hLx0.le
      rw [if_pos hV]
      -- the credit is used: `x < q` and `V ≤ That(T_λ(x))`
      have hxq' : x < actQ lam := by
        have : toR (xg (m + 1)) < toR S.q0lo := toR_lt_toR.mpr hq
        linarith [hS.q0 lam hlam]
      rw [if_pos hxq']
      have hk' := hk.resolve_left (not_le.mpr hq)
      have hden := hk'.1
      have hVpos := hk'.2
      have hdenR : 0 < S.l1 * (1 - toR (xg m)) - toR (xg m) :=
        (toR_pos.mpr hden).trans_le (denAt_mem hS.memL1 (xg m)).1
      have hVmem : (VArg S.L1 (xg m)).Mem (S.l1 * toR (xg m) / (S.l1 * (1 - toR (xg m)) - toR (xg m))) :=
        mem_div (mem_mul hS.memL1 (mem_pt (xg m))) (denAt_mem hS.memL1 (xg m)) hden
      have hVle : toR (VAt S.L1 (xg m)) ≤ That lam (Tf lam x) :=
        (logI_lo_le hVmem hVpos).trans (That_Tf_ge hlam0 hlam.2 hxm0 hx1 hxq' hdenR)
      have hLhi : 0 < (S.Lx.getD (m + 1) default).hi := by
        rw [hLxm1]
        exact toR_pos.mp ((Lf_pos (toR_xg_pos _) hxm1').trans_le hmemLm1.2)
      have hmem := mem_div (mem_mul (mem_pt S.k0) (mem_pt (VAt S.L1 (xg m))))
        (mem_pt (S.Lx.getD (m + 1) default).hi) hLhi
      refine hmem.1.trans ?_
      have hVR : 0 < toR (VAt S.L1 (xg m)) := toR_pos.mpr hV
      have hLxhi : Lf x ≤ toR (S.Lx.getD (m + 1) default).hi := by
        rw [hLxm1]; exact (Lf_mono hx2 hxm1').trans hmemLm1.2
      calc toR S.k0 * toR (VAt S.L1 (xg m)) / toR (S.Lx.getD (m + 1) default).hi
          ≤ kK lam S.a * ThatPlus lam (Tf lam x) / toR (S.Lx.getD (m + 1) default).hi := by
            apply div_le_div_of_nonneg_right _ (hLx0.le.trans hLxhi)
            exact mul_le_mul (hS.k0le lam hlam) (hVle.trans (That_le_ThatPlus _ _)) hVR.le hk0
        _ ≤ kK lam S.a * ThatPlus lam (Tf lam x) / Lf x :=
            div_le_div_of_nonneg_left (mul_nonneg hk0 (ThatPlus_nonneg _ _)) hLx0 hLxhi
    · rw [if_neg hq, toR_zero]; exact div_nonneg hind0 hLx0.le
  have h3 : kK lam S.a ≤ toR S.k1 := hS.lek1 lam hlam
  unfold aloAt
  rw [toR_sub, toR_add, add_div]
  linarith

/-- **The upper bound of `x/L(x)` on grid cell `m`**. -/
theorem le_bhiAt {m : ℕ} (hLxm : S.Lx.getD m default = LxAt m) (hc : pcellOK S m = true)
    {x : ℝ} (hx1 : toR (xg m) ≤ x) (hx2 : x ≤ toR (xg (m + 1))) :
    x / Lf x ≤ toR (bhiAt S.Lx m) := by
  simp only [pcellOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hxm, hxm1⟩, hLpos⟩, _⟩, _⟩ := hc
  have hxm0 : 0 < toR (xg m) := toR_xg_pos m
  have hxlt1 : x < 1 := hx2.trans_lt (toR_lt_one hxm1)
  have hmemL : (S.Lx.getD m default).Mem (Lf (toR (xg m))) := by rw [hLxm]; exact LxAt_mem hxm
  have hmem := mem_div (mem_pt (xg m)) hmemL hLpos
  exact (div_Lf_anti hxm0 hx1 hxlt1).trans hmem.2

end Cells

end Erdos993Lean.Analytic.TailCert

namespace Erdos993Lean.Analytic.TailCert

open Compute Tail

section Query

variable {S : Setup}

/-- The arrays of a setup are the tabulated functions. -/
structure ArrOK (S : Setup) : Prop where
  Lx : ∀ i ≤ S.N, S.Lx.getD i default = LxAt i
  alo : ∀ m < S.N, S.alo.getD m 0 = aloAt S.L0 S.L1 S.A S.q0lo S.k0 S.k1 S.Lx m
  bhi : ∀ m < S.N, S.bhi.getD m 0 = bhiAt S.Lx m
  tbl : ∀ j ≤ jC, S.tbl.getD j #[] = tblRow S.alo S.bhi S.N ((j : ℤ) * S.dC)

theorem arrOK_mkSetup (l0 l1 a ell z : ℚ) : ArrOK (mkSetup l0 l1 a ell z) where
  Lx := fun _ hi => getD_map_range _ _ (Nat.lt_succ_of_le hi)
  alo := fun _ hm => getD_map_range _ _ hm
  bhi := fun _ hm => getD_map_range _ _ hm
  tbl := fun _ hj => getD_map_range (fun (j : ℕ) => tblRow _ _ _ ((j : ℤ) * _)) _
    (Nat.lt_succ_of_le hj)

/-- On grid cell `m`: `ψ_c(x) ≥ alo m − c' bhi m` for `0 ≤ c ≤ c'`. -/
theorem psiF_ge_cell (hS : ConstOK S) (hA : ArrOK S) {m : ℕ} (hm : m < S.N)
    (hc : pcellOK S m = true) {lam c c' x : ℝ} (hlam : InBand S lam) (hc0 : 0 ≤ c)
    (hcc : c ≤ c') (hx1 : toR (xg m) ≤ x) (hx2 : x ≤ toR (xg (m + 1))) :
    toR (S.alo.getD m 0) - c' * toR (S.bhi.getD m 0) ≤ psiF lam S.a c x := by
  have hc' := hc
  simp only [pcellOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc'
  have hx0 : 0 < x := (toR_xg_pos m).trans_le hx1
  have hxlt1 : x < 1 := hx2.trans_lt (toR_lt_one hc'.1.1.1.2)
  have hL : 0 < Lf x := Lf_pos hx0 hxlt1
  have h1 := aloAt_le hS (hA.Lx m hm.le) (hA.Lx (m + 1) hm) hc hlam hx1 hx2
  have h2 := le_bhiAt (hA.Lx m hm.le) hc hx1 hx2
  rw [psiF_eq hL, hA.alo m hm, hA.bhi m hm]
  have hxL : 0 ≤ x / Lf x := div_nonneg hx0.le hL.le
  have h4 : c * (x / Lf x) ≤ c' * toR (bhiAt S.Lx m) :=
    mul_le_mul hcc h2 hxL (hc0.trans hcc)
  linarith

/-- The rounded table entry: `cellV C m ≤ alo m − C bhi m`. -/
theorem toR_cellV_le (C : ℤ) (m : ℕ) :
    toR (cellV S.alo S.bhi C m) ≤ toR (S.alo.getD m 0) - toR C * toR (S.bhi.getD m 0) := by
  unfold cellV
  rw [toR_sub]
  have h := le_toR_cdivP (C * S.bhi.getD m 0)
  rw [← toR_mul_toR] at h
  linarith

/-- The table: `tbl j n ≤ 0` and `tbl j n ≤ cellV (j dC) m` for `m < n`. -/
theorem tget_spec (hA : ArrOK S) {j n : ℕ} (hj : j ≤ jC) (hn : n ≤ S.N) :
    tget S.tbl j n ≤ 0 ∧ ∀ m < n, tget S.tbl j n ≤ cellV S.alo S.bhi ((j : ℤ) * S.dC) m := by
  unfold tget
  rw [hA.tbl j hj]
  unfold tblRow
  rw [array_getD_toArray]
  have := pmins_getD (cellV S.alo S.bhi ((j : ℤ) * S.dC)) S.N 0 0 n hn
  simpa using this

theorem xg_zero_lt_one : xg 0 < one := by decide

/-- **The tiny region**: `ψ_c(x) ≥ 0` for `0 < x ≤ x_0 = 2^-46`, `0 ≤ c ≤ C_64`. -/
theorem psiF_nonneg_tiny (hS : ConstOK S) (hA : ArrOK S) (htiny : tinyOK S = true) {lam c x : ℝ}
    (hlam : InBand S lam) (hc0 : 0 ≤ c) (hc : c ≤ toR ((jC : ℤ) * S.dC)) (hx0 : 0 < x)
    (hx : x ≤ toR (xg 0)) : 0 ≤ psiF lam S.a c x := by
  simp only [tinyOK, Bool.and_eq_true, decide_eq_true_eq] at htiny
  obtain ⟨hTpos, hsub⟩ := htiny
  have hx0lt1 : toR (xg 0) < 1 := toR_lt_one xg_zero_lt_one
  have hxlt1 : x < 1 := hx.trans_lt hx0lt1
  have hL : 0 < Lf x := Lf_pos hx0 hxlt1
  have hlam0 : 0 < lam := hS.l0pos.trans_le hlam.1
  have hLx0 : (S.Lx.getD 0 default).Mem (Lf (toR (xg 0))) := by
    rw [hA.Lx 0 (Nat.zero_le _)]; exact LxAt_mem xg_zero_lt_one
  have hmem := mem_sub (mem_mul hS.memA (mem_pt (TloAt S.L0 (xg 0))))
    (mem_mul (mem_pt (S.k1 + (jC : ℤ) * S.dC)) (mem_pt (S.Lx.getD 0 default).hi))
  have hval : 0 ≤ S.a * toR (TloAt S.L0 (xg 0)) -
      toR (S.k1 + (jC : ℤ) * S.dC) * toR (S.Lx.getD 0 default).hi :=
    (toR_nonneg.mpr hsub).trans hmem.1
  rw [toR_add] at hval
  have hT : toR (TloAt S.L0 (xg 0)) ≤ Tf lam x :=
    (TloAt_le hS.memL0 (xg_pos 0) hTpos).trans (Tf_mono hS.l0pos hlam.1 hx0 hx hx0lt1)
  have hLle : Lf x ≤ toR (S.Lx.getD 0 default).hi := (Lf_mono hx hx0lt1).trans hLx0.2
  have hLhi0 : 0 ≤ toR (S.Lx.getD 0 default).hi := hL.le.trans hLle
  have hk0 : 0 ≤ kK lam S.a := kK_nonneg hlam0 hS.a0
  have hk1 := hS.lek1 lam hlam
  have hind0 : 0 ≤ (if x < actQ lam then kK lam S.a * ThatPlus lam (Tf lam x) else 0) := by
    split_ifs
    · exact mul_nonneg hk0 (ThatPlus_nonneg _ _)
    · exact le_rfl
  have hkL : kK lam S.a * Lf x ≤ toR S.k1 * toR (S.Lx.getD 0 default).hi :=
    mul_le_mul hk1 hLle hL.le (hk0.trans hk1)
  have hxL : x ≤ Lf x := le_Lf hxlt1
  have hcx : c * x ≤ toR ((jC : ℤ) * S.dC) * toR (S.Lx.getD 0 default).hi :=
    mul_le_mul hc (hxL.trans hLle) hx0.le (hc0.trans hc)
  have haT : S.a * toR (TloAt S.L0 (xg 0)) ≤ S.a * Tf lam x := mul_le_mul_of_nonneg_left hT hS.a0
  unfold psiF
  apply div_nonneg _ hL.le
  nlinarith

/-- **The query of the inner table**: for `0 ≤ c ≤ cf` and `0 < x ≤ pm`:
`queryVal pm cf ≤ ψ_c(x)` (concave interpolation between the c-grid values `C_j ≤ cf ≤ C_{j+1}`). -/
theorem query_sound (hS : ConstOK S) (hA : ArrOK S) (hall : allLt S.N (pcellOK S) = true)
    (htiny : tinyOK S = true) (hdC : 0 < S.dC) {pm cf : ℤ} (hq : queryChk S pm cf = true)
    {lam c x : ℝ} (hlam : InBand S lam) (hc0 : 0 ≤ c) (hc : c ≤ toR cf) (hx0 : 0 < x)
    (hxp : x ≤ toR pm) :
    toR (queryVal S pm cf) ≤ psiF lam S.a c x := by
  simp only [queryChk, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨⟨hn, hpm⟩, hrem0⟩, hrem1⟩ := hq
  set n := nIdx pm with hndef
  set j := qJ S.dC cf with hjdef
  set rem := qRem S.dC cf with hremdef
  have hj : j + 1 ≤ jC := by
    have : j ≤ jC - 1 := by rw [hjdef]; unfold qJ; exact min_le_right _ _
    unfold jC at this ⊢; omega
  obtain ⟨ht0n, ht0⟩ := tget_spec hA (j := j) (by omega) hn
  obtain ⟨ht1n, ht1⟩ := tget_spec hA (j := j + 1) hj hn
  set t0 := tget S.tbl j n
  set t1 := tget S.tbl (j + 1) n
  have hdCR : 0 < toR S.dC := toR_pos.mpr hdC
  set θ := toR rem / toR S.dC with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (toR_nonneg.mpr hrem0) hdCR.le
  have hθ1 : θ ≤ 1 := (div_le_one hdCR).mpr (toR_le_toR.mpr hrem1)
  have hcf : cf = (j : ℤ) * S.dC + rem := by rw [hremdef]; unfold qRem; ring
  have hcfR : toR cf = toR ((j : ℤ) * S.dC) + θ * toR S.dC := by
    rw [hcf, toR_add, hθ]; field_simp
  have hCj1 : toR (((j + 1 : ℕ) : ℤ) * S.dC) = toR ((j : ℤ) * S.dC) + toR S.dC := by
    rw [← toR_add]; congr 1; push_cast; ring
  -- the value is at most the interpolation
  have hval : toR (queryVal S pm cf) ≤ (1 - θ) * toR t0 + θ * toR t1 := by
    unfold queryVal
    rw [← hndef, ← hjdef, ← hremdef, toR_add]
    have hf := fdiv_le (rem * (t1 - t0)) hdC
    have : toR (fdiv (rem * (t1 - t0)) S.dC) ≤ θ * (toR t1 - toR t0) := by
      unfold toR at hf ⊢
      rw [hθ]
      unfold toR
      have h2 : (0 : ℝ) < 2 ^ prec := two_pow_prec_pos
      calc (fdiv (rem * (t1 - t0)) S.dC : ℝ) / 2 ^ prec
          ≤ ((rem * (t1 - t0) : ℤ) : ℝ) / S.dC / 2 ^ prec :=
            div_le_div_of_nonneg_right hf h2.le
        _ = (rem : ℝ) / 2 ^ prec / ((S.dC : ℝ) / 2 ^ prec) * ((t1 : ℝ) / 2 ^ prec - (t0 : ℝ) / 2 ^ prec) := by
            have : (S.dC : ℝ) ≠ 0 := by exact_mod_cast hdC.ne'
            push_cast
            field_simp
    linarith
  refine hval.trans ?_
  have hcC : c ≤ toR (((j + 1 : ℕ) : ℤ) * S.dC) := by
    rw [hCj1]; nlinarith
  by_cases hx0' : x ≤ toR (xg 0)
  · -- the tiny region
    have hcJ : c ≤ toR ((jC : ℤ) * S.dC) := by
      refine hcC.trans (toR_le_toR.mpr ?_)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hdC.le
    have := psiF_nonneg_tiny hS hA htiny hlam hc0 hcJ hx0 hx0'
    have ht0R : toR t0 ≤ 0 := by rw [← toR_zero]; exact toR_le_toR.mpr ht0n
    have ht1R : toR t1 ≤ 0 := by rw [← toR_zero]; exact toR_le_toR.mpr ht1n
    nlinarith
  · -- a grid cell `m < n`
    obtain ⟨m, hmn, hm1, hm2⟩ := exists_cell (f := fun i => toR (xg i)) (not_le.mp hx0') n
      (hxp.trans (toR_le_toR.mpr hpm))
    have hmN : m < S.N := lt_of_lt_of_le hmn hn
    have hcm := (allLt_iff _ _).mp hall m hmN
    have hge := psiF_ge_cell hS hA hmN hcm hlam hc0 hc hm1.le hm2
    have hc0' := toR_cellV_le (S := S) ((j : ℤ) * S.dC) m
    have hc1' := toR_cellV_le (S := S) (((j + 1 : ℕ) : ℤ) * S.dC) m
    have h0 : toR t0 ≤ toR (cellV S.alo S.bhi ((j : ℤ) * S.dC) m) := toR_le_toR.mpr (ht0 m hmn)
    have h1 : toR t1 ≤ toR (cellV S.alo S.bhi (((j + 1 : ℕ) : ℤ) * S.dC) m) :=
      toR_le_toR.mpr (ht1 m hmn)
    rw [hCj1] at hc1'
    rw [hcfR] at hge
    nlinarith

theorem queryVal_nonpos (hA : ArrOK S) {pm cf : ℤ} (hq : queryChk S pm cf = true)
    (hdC : 0 < S.dC) : queryVal S pm cf ≤ 0 := by
  simp only [queryChk, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨⟨hn, _⟩, hrem0⟩, hrem1⟩ := hq
  have hj : qJ S.dC cf + 1 ≤ jC := by
    have : qJ S.dC cf ≤ jC - 1 := by unfold qJ; exact min_le_right _ _
    unfold jC at this ⊢; omega
  have ht0 := (tget_spec hA (j := qJ S.dC cf) (by omega) hn).1
  have ht1 := (tget_spec hA (j := qJ S.dC cf + 1) hj hn).1
  unfold queryVal
  have hf : fdiv (qRem S.dC cf * (tget S.tbl (qJ S.dC cf + 1) (nIdx pm) - tget S.tbl (qJ S.dC cf) (nIdx pm)))
      S.dC ≤ -tget S.tbl (qJ S.dC cf) (nIdx pm) := by
    unfold fdiv
    rw [Int.ediv_le_iff_le_mul hdC]
    nlinarith
  linarith

end Query

end Erdos993Lean.Analytic.TailCert
