import Mathlib
import Erdos993Lean.Analytic.O2.Cert.PieceFind

/-!
# O2 certificate checker (lane A18): soundness of the cell check

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  **`boxOK_sound`**: a passing cell
`[l0, l1] × [x0, x1]` (`Compute/Engine.lean`, `boxOK`) certifies every point `(λ, x)` of it (`PointGood`): for the
cell's branch of the own coefficients (the kernel branch only for `x ≥ 7/8`), for every `Y = (1 − r)/q ∈ [0, P]`,
every parent case `τ = t/q ∈ {Y, P} ∪ {j/8 : Y ≤ j/8 ≤ P}` (`ParentCase`, the cases of A16's
`phi_nonneg_of_knots`) and every response `z`, the payment `payK` (eq. (11) with A16's source) is nonnegative.
The parent cases are covered by the labels of the cell (`cell_good`): `Y` by its segment, `P` by the segment of
`⌊8P⌋`, the knots by the knot labels; the enclosure of `P` is available because the first piece of the case
`t/q = Y` passes.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The certified statement of a cell -/

/-- The parent cases of the knot reduction (`phi_nonneg_of_knots`), in `τ = t/q`: the lower end `τ = Y`
(`Y = (1 − r)/q`), the upper end `τ = P`, and the knots `τ = j/8` with `Y ≤ j/8 ≤ P`. -/
def ParentCase (P Y τ : ℝ) : Prop :=
  τ = Y ∨ τ = P ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ 7 ∧ Y ≤ (j : ℝ) / 8 ∧ (j : ℝ) / 8 ≤ P ∧ τ = (j : ℝ) / 8

/-- The payment in the real functions of a band at `(λ, x)`, `r = 1 − qY`, parent point `τ = t/q`, response
`z`, with A16's source `g` (the own coefficients by the branch `kern`). -/
noncomputable def payK (sd : SegData) (kern : Bool) (l x Y τ z : ℝ) : ℝ :=
  payE (1 / (l + 1) * (sd.gamma : ℝ)) (1 - qR l * Y) (src l (pR l x) (1 - qR l * Y)) (pR l x) z
    (auR sd kern l x) (avR sd kern l x) (soR sd kern l x)
    (fieldR sd sd.Lu sd.Ru l τ) (fieldR sd sd.Lv sd.Rv l τ) (fieldR sd sd.Ls sd.Rs l τ)
    (fieldR sd sd.Ltau sd.Rtau l x) (fieldR sd sd.Ltau sd.Rtau l τ) (lerpR sd.lo sd.hi sd.Lw sd.Rw l)
    (phiR kern l x) (lerpR sd.lo sd.hi sd.Lell sd.Rell l) (Real.log ((l + 1) * x / (le1R l x * le1R l x)))
    (pR l x / -Real.log (1 - pR l x))

theorem upR_lt_one {l x : ℝ} (hl : 0 < l) (hx : 0 < x) (hx1 : x ≤ 1) : upR l x < 1 := by
  have hq0 := qR_pos hl; have hq1 := qR_lt_one hl
  have hp1 : pR l x < 1 := by unfold pR; nlinarith
  have hp0 : 0 < pR l x := by unfold pR; positivity
  unfold upR
  rw [div_lt_one (by nlinarith)]
  nlinarith

theorem upR_pos {l x : ℝ} (hl : 0 < l) (hx : 0 < x) (hx1 : x ≤ 1) : 0 < upR l x := by
  have hq0 := qR_pos hl; have hq1 := qR_lt_one hl
  have hp1 : pR l x < 1 := by unfold pR; nlinarith
  unfold upR
  exact div_pos (by linarith) (by nlinarith)

theorem toR_eight_mul (u : ℤ) : toR (8 * u) = 8 * toR u := by
  unfold toR; push_cast; ring

/-- **The certified statement of a passing cell**: at every point of the box, every `Y ∈ [0, P]`, every parent
case and every response, the payment is nonnegative. -/
theorem cell_good {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) {bx : BoxCtx} {fl : Flags} (hb : BoxOK bx)
    (hL : 0 < bx.lamI.lo) (hX : 0 < bx.xI.lo) (hX1 : bx.xI.hi ≤ one) (hk1 : fl.kern = false → bx.xI.hi < one)
    (hy : fl.y0b = (context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩).y0b)
    (hall : ∀ lab ∈ labelsOf (context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩),
      ∀ sLn ∈ (listsOf (context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩) lab
        (recipeOf (context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩) lab)).zipIdx,
      ∀ k < sLn.1.2.length - 1,
        pieceOK sd bx fl (ancArr sd bx fl) lab
          (recipeOf (context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩) lab)
          (alArr sd bx fl lab (recipeOf (context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩) lab)) sLn.2 k
          (triples (context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩) lab sLn.1.1
            (pieceAt sLn.1.2 k).1 (pieceAt sLn.1.2 k).2) = true)
    {l x : ℝ} (hl : bx.lamI.Mem l) (hx : bx.xI.Mem x) :
    ∀ Y τ z : ℝ, 0 ≤ Y → Y ≤ upR l x → ParentCase (upR l x) Y τ → 0 ≤ payK sd fl.kern l x Y τ z := by
  intro Y τ z hY0 hYP hcase
  set c := context sd (lamDN bx.lamI) (xDN bx.xI) ⟨fl.kern, fl.low, 3⟩ with hcdef
  have hLL := hb.hL
  have hXX := hb.hX
  have hl0 : 0 < l := (toR_pos.mpr hL).trans_le hl.1
  have hx0 : 0 < x := (toR_pos.mpr hX).trans_le hx.1
  have hx1 : x ≤ 1 := by have := hx.2.trans (toR_le_toR.mpr hX1); rwa [toR_one] at this
  have hc0 : CtxE bx.lamI bx.xI sd ⟨fl.kern, fl.low, 3⟩ c := context_enc sd _ hL hX hk1
  have hc : CtxE bx.lamI bx.xI sd fl c := ctxE_flags hc0 hy
  have hA := anchor_enc (sd := sd) (fl := fl) hb hL hX hk1
  have hAy := anchor_y0b (sd := sd) (bx := bx) (fl := fl) hy (ctx_y0b_le _ _ _ _)
  have hpass : ∀ lab ∈ labelsOf c, ∀ n < (listsOf c lab (recipeOf c lab)).length,
      ∀ k < ((listsOf c lab (recipeOf c lab)).getD n (0, [])).2.length - 1,
      pieceOK sd bx fl (ancArr sd bx fl) lab (recipeOf c lab) (alArr sd bx fl lab (recipeOf c lab)) n k
        (triples c lab ((listsOf c lab (recipeOf c lab)).getD n (0, [])).1
          (pieceAt ((listsOf c lab (recipeOf c lab)).getD n (0, [])).2 k).1
          (pieceAt ((listsOf c lab (recipeOf c lab)).getD n (0, [])).2 k).2) = true :=
    fun lab hlab n hn k hk => hall lab hlab _ (mem_zipIdx_getD _ _ hn) k hk
  -- the first piece of the parent case `Y`: `P` and `p > 0` are enclosed
  have hup := cell_upper_hi_pos hc0 hL hLL hX hXX hX1
  have hsegs0 : 0 ∈ segsOf c := by simp [segsOf]; exact hup
  have hn0 : 0 < (segsOf c).length := List.length_pos_of_mem hsegs0
  have hCL0 : (listsOf c (0, 0) (recipeOf c (0, 0))).getD 0 (0, []) =
      ((segsOf c)[0], insertCuts (portion c (segsOf c)[0]).1 (portion c (segsOf c)[0]).2
        (((segsOf c).map (fun s => usedCuts (portion c s).1 (portion c s).2 c.cuts 0)).getD 0 []) c.cuts 0
        [(portion c (segsOf c)[0]).1, (portion c (segsOf c)[0]).2]) := by
    rw [recipe_low]; exact listsOf_low_getD c _ _ hn0
  obtain ⟨hhd, hlen⟩ := insertCuts_head_length (portion c (segsOf c)[0]).1 (portion c (segsOf c)[0]).2
    (((segsOf c).map (fun s => usedCuts (portion c s).1 (portion c s).2 c.cuts 0)).getD 0 []) c.cuts 0
    [(portion c (segsOf c)[0]).1, (portion c (segsOf c)[0]).2] (by simp)
  have hp0 := hpass (0, 0) (mem_labels_low c) 0
    (by rw [recipe_low, listsOf_low_length]; exact hn0) 0 (by rw [hCL0]; simp at hlen ⊢; omega)
  obtain ⟨hya, hpok, hplo⟩ := pieceOK_ok hp0
  have hupok : c.upper.ok = true := by
    rw [hCL0] at hya
    simp only [pieceAt] at hya
    rw [hhd] at hya
    simp only [List.getD_cons_zero, portion, mn_ok, DN.cst, Bool.true_and] at hya
    exact hya
  have hupE := (hc.upper hupok).val l x hl hx
  have hcut0 : fl.low = false → (c.cuts.getD 0 zeroDN).ok = true ∧ ∃ z0 rest, c.cuts = z0 :: rest := by
    intro hlow
    refine ⟨cell_cut0_ok (fl := ⟨fl.kern, fl.low, 3⟩) hL hLL hlow hplo, ?_⟩
    have := hc.cuts.1
    rw [hlow] at this
    simp only [Bool.false_eq_true, if_false] at this
    rcases hcs : c.cuts with _ | ⟨z0, rest⟩
    · rw [hcs] at this; simp at this
    · exact ⟨z0, rest, rfl⟩
  have hP0 := upR_pos hl0 hx0 hx1
  have hP1 := upR_lt_one hl0 hx0 hx1
  -- the three parent cases
  rcases hcase with rfl | rfl | ⟨j, hj1, hj7, hYj, hjP, rfl⟩
  · -- `τ = Y`: the segment of `Y`
    obtain ⟨s', hs'8, hs'1, hs'2, hs'up⟩ : ∃ s' : ℕ, s' < 8 ∧ (s' : ℝ) / 8 ≤ τ ∧ τ ≤ ((s' : ℝ) + 1) / 8 ∧
        (s' : ℤ) * eighth < c.upper.v.hi := by
      rcases hY0.lt_or_eq with hpos | hzero
      · refine ⟨⌈8 * τ⌉₊ - 1, ?_, ?_, ?_, ?_⟩
        · have : ⌈8 * τ⌉₊ ≤ 8 := Nat.ceil_le.mpr (by push_cast; linarith)
          omega
        · have h1 : 1 ≤ ⌈8 * τ⌉₊ := Nat.one_le_iff_ne_zero.mpr (by simp; positivity)
          have h2 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 * τ by positivity)
          rw [Nat.cast_sub h1]; push_cast; linarith
        · have h1 : 1 ≤ ⌈8 * τ⌉₊ := Nat.one_le_iff_ne_zero.mpr (by simp; positivity)
          have h2 := Nat.le_ceil (8 * τ)
          rw [Nat.cast_sub h1]; push_cast; linarith
        · have h1 : 1 ≤ ⌈8 * τ⌉₊ := Nat.one_le_iff_ne_zero.mpr (by simp; positivity)
          have h2 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 * τ by positivity)
          apply toR_lt_toR.mp
          rw [show (((⌈8 * τ⌉₊ - 1 : ℕ) : ℤ)) * eighth = ((((⌈8 * τ⌉₊ - 1 : ℕ) : ℕ) : ℤ)) * eighth from rfl,
            toR_eighth_mul]
          push_cast [Nat.cast_sub h1]
          linarith [hupE.2]
      · refine ⟨0, by norm_num, by simp [← hzero], by rw [← hzero]; norm_num, by simpa using hup⟩
    have hs'mem : s' ∈ segsOf c := by
      simp only [segsOf, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨hs'8, hs'up⟩
    obtain ⟨n, hn, hsn⟩ := List.getElem_of_mem hs'mem
    have hFR : (listsR upR (cutsR fl.low c.y0b) (0, 0) (recipeOf c (0, 0))).getD n (0, []) =
        (s', rinsertCuts (fun l x => min ((s' : ℝ) / 8) (upR l x)) (fun l x => min (((s' + 1 : ℕ) : ℝ) / 8) (upR l x))
          (usedCuts (portion c s').1 (portion c s').2 c.cuts 0) (cutsR fl.low c.y0b) 0
          [fun l x => min ((s' : ℝ) / 8) (upR l x), fun l x => min (((s' + 1 : ℕ) : ℝ) / 8) (upR l x)]) := by
      rw [recipe_low, listsR_low_getD _ _ _ hn]
      have e : ((segsOf c).map (fun s => usedCuts (portion c s).1 (portion c s).2 c.cuts 0)).getD n [] =
          usedCuts (portion c s').1 (portion c s').2 c.cuts 0 := by
        rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getElem_map, hsn]
      rw [e, hsn]
    have hAe : DE bx.lamI bx.xI (fun l x => min ((s' : ℝ) / 8) (upR l x)) (portion c s').1 :=
      de_mn (de_cst (mem_knotI _)) hc.upper
    have hBe : DE bx.lamI bx.xI (fun l x => min (((s' + 1 : ℕ) : ℝ) / 8) (upR l x)) (portion c s').2 :=
      de_mn (de_cst (mem_knotI _)) hc.upper
    have hAok : (portion c s').1.ok = true := by simp [portion, mn_ok, DN.cst, hupok]
    have hBok : (portion c s').2.ok = true := by simp [portion, mn_ok, DN.cst, hupok]
    have ha : min ((s' : ℝ) / 8) (upR l x) = (s' : ℝ) / 8 := min_eq_left (hs'1.trans hYP)
    have hbY : τ ≤ min (((s' + 1 : ℕ) : ℝ) / 8) (upR l x) := le_min (by push_cast; exact hs'2) hYP
    obtain ⟨η, FA, FB, h0, h1, haF, hle, hbF, hYη, hpay⟩ := pay_at_list hγ hb hc hA hAy hcut0 (lab := (0, 0))
      (by norm_num) n (hpass (0, 0) (mem_labels_low c) n (by rw [recipe_low, listsOf_low_length]; exact hn)) _ _ _ _
      s' hFR hAe hBe hAok hBok hl hx hl0 hx0 hx1 (by beta_reduce; rw [ha]; exact hs'1.trans hbY)
      (by beta_reduce; rw [ha]; positivity) (min_le_right _ _) (Y := τ) (by beta_reduce; rw [ha]; exact hs'1) hbY z
    beta_reduce at haF hbF
    rw [ha] at haF
    have hb8 : FB l x ≤ ((s' : ℝ) + 1) / 8 := hbF.trans ((min_le_left _ _).trans (by push_cast; rfl))
    rw [parAt_low _ sd sd.Lu sd.Ru (ctxR sd fl).u rfl s' hs'8 FA FB l x η h0 h1 haF hle hb8,
      parAt_low _ sd sd.Lv sd.Rv (ctxR sd fl).v rfl s' hs'8 FA FB l x η h0 h1 haF hle hb8,
      parAt_low _ sd sd.Ls sd.Rs (ctxR sd fl).s rfl s' hs'8 FA FB l x η h0 h1 haF hle hb8,
      parAt_low _ sd sd.Ltau sd.Rtau (ctxR sd fl).t rfl s' hs'8 FA FB l x η h0 h1 haF hle hb8, ← hYη] at hpay
    exact hpay
  · -- `τ = P`: the segment of `P`
    set j := ⌊8 * upR l x⌋₊ with hj
    have hj1 : (j : ℝ) ≤ 8 * upR l x := Nat.floor_le (by positivity)
    have hj2 : 8 * upR l x < j + 1 := Nat.lt_floor_add_one _
    have hj7 : j ≤ 7 := by
      have : j < 8 := by
        have : (j : ℝ) < 8 := by linarith
        exact_mod_cast this
      omega
    have hjm : ((2, j) : ℕ × ℕ) ∈ labelsOf c := by
      apply mem_labels_high c hj7
      · apply fdivP_le_of_lt
        apply toR_lt_toR.mp
        rw [toR_eight_mul, show ((j : ℤ) + 1) * one = (((j + 1 : ℕ) : ℤ)) * one by push_cast; ring,
          toR_int_mul_one]
        push_cast; linarith [hupE.1]
      · apply le_fdivP_of_le
        apply toR_le_toR.mp
        rw [toR_eight_mul, toR_int_mul_one]
        push_cast
        linarith [hupE.2]
    have hrcp := recipe_other c (lab := (2, j)) (by norm_num)
    have hFR : (listsR upR (cutsR fl.low c.y0b) (2, j) (recipeOf c (2, j))).getD 0 (0, []) =
        (0, rinsertCuts 0 (fun l x => min (upR l x) (((j + 1 : ℕ) : ℝ) / 8))
          (usedCuts zeroDN (highOf c (2, j)) c.cuts 0) (cutsR fl.low c.y0b) 0
          [0, fun l x => min (upR l x) (((j + 1 : ℕ) : ℝ) / 8)]) := by
      rw [hrcp]; simp [listsR]
    have hBe : DE bx.lamI bx.xI (fun l x => min (upR l x) (((j + 1 : ℕ) : ℝ) / 8)) (highOf c (2, j)) := by
      simp only [highOf, show ((2, j) : ℕ × ℕ).1 = 2 from rfl, OfNat.ofNat_ne_one, if_false]
      exact de_mn hc.upper (de_cst (mem_knotI _))
    have hBok : (highOf c (2, j)).ok = true := by
      simp [highOf, mn_ok, DN.cst, hupok]
    have hbv : min (upR l x) (((j + 1 : ℕ) : ℝ) / 8) = upR l x := min_eq_left (by push_cast; linarith)
    obtain ⟨η, FA, FB, h0, h1, haF, hle, hbF, hYη, hpay⟩ := pay_at_list hγ hb hc hA hAy hcut0 (lab := (2, j))
      (by simpa using hj7) 0 (hpass (2, j) hjm 0 (by rw [hrcp]; simp [listsOf])) _ _ zeroDN _ 0 hFR de_zero hBe rfl
      hBok hl hx hl0 hx0 hx1 (by beta_reduce; rw [hbv]; exact hP0.le) (by simp)
      (min_le_left _ _) (Y := Y) (by simpa using hY0) (by beta_reduce; rw [hbv]; exact hYP) z
    have hP8 : (j : ℝ) / 8 ≤ (ctxR sd fl).upper l x := by show (j : ℝ) / 8 ≤ upR l x; linarith
    have hP8' : (ctxR sd fl).upper l x ≤ ((j : ℝ) + 1) / 8 := by show upR l x ≤ ((j : ℝ) + 1) / 8; linarith
    have hj8 : j < 8 := by omega
    rw [parAt_high _ sd sd.Lu sd.Ru (ctxR sd fl).u rfl j hj8 0 FA FB l x η hP8 hP8',
      parAt_high _ sd sd.Lv sd.Rv (ctxR sd fl).v rfl j hj8 0 FA FB l x η hP8 hP8',
      parAt_high _ sd sd.Ls sd.Rs (ctxR sd fl).s rfl j hj8 0 FA FB l x η hP8 hP8',
      parAt_high _ sd sd.Ltau sd.Rtau (ctxR sd fl).t rfl j hj8 0 FA FB l x η hP8 hP8'] at hpay
    exact hpay
  · -- `τ = j/8`
    have hjm : ((1, j) : ℕ × ℕ) ∈ labelsOf c := by
      apply mem_labels_knot c hj1 hj7
      apply toR_le_toR.mp
      rw [toR_eighth_mul]
      push_cast
      linarith [hupE.2]
    have hrcp := recipe_other c (lab := (1, j)) (by norm_num)
    have hFR : (listsR upR (cutsR fl.low c.y0b) (1, j) (recipeOf c (1, j))).getD 0 (0, []) =
        (0, rinsertCuts 0 (fun l x => min (upR l x) ((j : ℝ) / 8))
          (usedCuts zeroDN (highOf c (1, j)) c.cuts 0) (cutsR fl.low c.y0b) 0
          [0, fun l x => min (upR l x) ((j : ℝ) / 8)]) := by
      rw [hrcp]; simp [listsR]
    have hBe : DE bx.lamI bx.xI (fun l x => min (upR l x) ((j : ℝ) / 8)) (highOf c (1, j)) := by
      simp only [highOf, show ((1, j) : ℕ × ℕ).1 = 1 from rfl, show ((1, j) : ℕ × ℕ).2 = j from rfl, if_true]
      exact de_mn hc.upper (de_cst (mem_knotI _))
    have hBok : (highOf c (1, j)).ok = true := by
      simp [highOf, mn_ok, DN.cst, hupok]
    have hbv : min (upR l x) ((j : ℝ) / 8) = (j : ℝ) / 8 := min_eq_right hjP
    obtain ⟨η, FA, FB, h0, h1, haF, hle, hbF, hYη, hpay⟩ := pay_at_list hγ hb hc hA hAy hcut0 (lab := (1, j))
      (by simpa using hj7) 0 (hpass (1, j) hjm 0 (by rw [hrcp]; simp [listsOf])) _ _ zeroDN _ 0 hFR de_zero hBe rfl
      hBok hl hx hl0 hx0 hx1 (by beta_reduce; rw [hbv]; positivity) (by simp)
      (by beta_reduce; rw [hbv]; exact hjP) (Y := Y) (by simpa using hY0) (by beta_reduce; rw [hbv]; exact hYj) z
    rw [parAt_knot _ sd sd.Lu sd.Ru (ctxR sd fl).u rfl j (by omega) 0 FA FB l x η,
      parAt_knot _ sd sd.Lv sd.Rv (ctxR sd fl).v rfl j (by omega) 0 FA FB l x η,
      parAt_knot _ sd sd.Ls sd.Rs (ctxR sd fl).s rfl j (by omega) 0 FA FB l x η,
      parAt_knot _ sd sd.Ltau sd.Rtau (ctxR sd fl).t rfl j (by omega) 0 FA FB l x η] at hpay
    exact hpay

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- **The certified statement at one point** `(λ, x)`: for one branch of the own coefficients (the kernel branch
only if `x ≥ 7/8`), the payment is nonnegative for every `Y ∈ [0, P]`, every parent case and every response. -/
def PointGood (sd : SegData) (l x : ℝ) : Prop :=
  ∃ kern : Bool, (kern = true → 7 / 8 ≤ x) ∧
    ∀ Y τ z : ℝ, 0 ≤ Y → Y ≤ upR l x → ParentCase (upR l x) Y τ → 0 ≤ payK sd kern l x Y τ z

/-- **Soundness of the cell check**: a passing cell `[l0, l1] × [x0, x1]` certifies every point of it. -/
theorem boxOK_sound {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) {l0 l1 x0 x1 : ℚ} (h : boxOK sd l0 l1 x0 x1 = true)
    {l x : ℝ} (hl0 : (l0 : ℝ) ≤ l) (hl1 : l ≤ l1) (hx0 : (x0 : ℝ) ≤ x) (hx1 : x ≤ x1) : PointGood sd l x := by
  unfold boxOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hL, hLL⟩, hX⟩, hXX⟩, hX1⟩, hkern⟩, hall⟩ := h
  have hlm : (⟨(ofRat l0).lo, (ofRat l1).hi⟩ : Ival).Mem l :=
    ⟨(mem_ofRat l0).1.trans hl0, hl1.trans (mem_ofRat l1).2⟩
  have hxm : (⟨(ofRat x0).lo, (ofRat x1).hi⟩ : Ival).Mem x :=
    ⟨(mem_ofRat x0).1.trans hx0, hx1.trans (mem_ofRat x1).2⟩
  refine ⟨decide (7 * eighth ≤ (ofRat x0).lo), fun hk => ?_, ?_⟩
  · have h7 : 7 * eighth ≤ (ofRat x0).lo := by simpa using hk
    have := (toR_le_toR.mpr h7).trans hxm.1
    rw [show (7 : ℤ) * eighth = ((7 : ℕ) : ℤ) * eighth from rfl, toR_eighth_mul] at this
    push_cast at this
    exact this
  · set lamI : Ival := ⟨(ofRat l0).lo, (ofRat l1).hi⟩ with hlamI
    set xI : Ival := ⟨(ofRat x0).lo, (ofRat x1).hi⟩ with hxI
    set kern := decide (7 * eighth ≤ xI.lo) with hkd
    set low := decide (xI.hi ≤ (div (add oneI lamI) (add oneI (mul twoI lamI))).lo) with hlowd
    refine cell_good hγ (bx := ⟨lamI, xI, (lamI.hi - lamI.lo + 1) / 2, (xI.hi - xI.lo + 1) / 2⟩)
      (fl := ⟨kern, low, (context sd (lamDN lamI) (xDN xI) ⟨kern, low, 3⟩).y0b⟩) ⟨hLL, hXX, rfl, rfl⟩ hL hX hX1 ?_
      rfl ?_ hlm hxm
    · intro hk; rcases hkern with h | h
      · have : kern = true := by rw [hkd]; simpa using h
        simp only at hk
        rw [hk] at this; exact absurd this (by simp)
      · exact h
    · intro lab hlab sLn hsLn k hk
      exact hall lab hlab sLn hsLn k hk

end Erdos993Lean.Analytic.O2.Cert
