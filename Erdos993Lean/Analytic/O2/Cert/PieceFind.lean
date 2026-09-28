import Mathlib
import Erdos993Lean.Analytic.O2.Cert.PieceSound

/-!
# O2 certificate checker (lane A18): finding the piece of a parent marginal

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  Every `Y` of the range of a list of a parent case lies in
a piece whose ends are consecutive list values, with the first source cut not strictly inside (`find_piece_vals`:
used cuts are list values, unused ones lie outside the range, `not_inside_of_not_overlaps`); the labels, recipes
and lists of a cell (`mem_labels_low`, `mem_labels_high`, `mem_labels_knot`, `recipe_low`, `recipe_other`,
`listsOf_low_getD`); and the payment on the list of a parent case (**`pay_at_list`**).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

theorem chain_pair {a b : ℝ} (h : a ≤ b) : List.IsChain (· ≤ ·) [a, b] :=
  List.IsChain.cons_cons h (List.isChain_singleton b)

theorem head_le_of_chain : ∀ {F : List ℝ}, List.IsChain (· ≤ ·) F → ∀ y ∈ F, F.headD 0 ≤ y
  | [], _, y, hy => absurd hy List.not_mem_nil
  | a :: rest, h, y, hy => by
    simp only [List.headD_cons]
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact le_rfl
    · exact List.rel_of_pairwise_cons (List.isChain_iff_pairwise.mp h) hy'

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## Finding the piece of a `Y` -/

theorem getD_map_ev (Ls : List RF) (k : ℕ) (l x : ℝ) : (Ls.map (fun f => f l x)).getD k 0 = (Ls.getD k 0) l x := by
  have := List.getD_map (l := Ls) (d := (0 : RF)) (n := k) (fun f => f l x)
  simpa using this

theorem getD_mem_of_lt {Ls : List ℝ} {k : ℕ} (hk : k < Ls.length) : Ls.getD k 0 ∈ Ls := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-- **The piece of `Y`** in the sorted list of a parent case: its ends lie in `[a, b]`, `Y` is their
interpolation at some `η ∈ [0, 1]`, and the first source cut is not strictly inside. -/
theorem find_piece_vals (a b : ℝ) (hab : a ≤ b) (used : List ℕ) (zs : List ℝ) {Y : ℝ} (hY1 : a ≤ Y) (hY2 : Y ≤ b)
    (zf : ℝ) (hzf : (0 < zs.length ∧ zs.getD 0 0 = zf ∧ used.contains 0 = true) ∨ ¬ (a < zf ∧ zf < b)) :
    ∃ k η, k + 1 < (insertCutsV a b used zs 0 [a, b]).length ∧ 0 ≤ η ∧ η ≤ 1 ∧
      a ≤ (insertCutsV a b used zs 0 [a, b]).getD k 0 ∧
      (insertCutsV a b used zs 0 [a, b]).getD k 0 ≤ (insertCutsV a b used zs 0 [a, b]).getD (k + 1) 0 ∧
      (insertCutsV a b used zs 0 [a, b]).getD (k + 1) 0 ≤ b ∧
      Y = lin2 ((insertCutsV a b used zs 0 [a, b]).getD k 0) ((insertCutsV a b used zs 0 [a, b]).getD (k + 1) 0) η ∧
      ¬ ((insertCutsV a b used zs 0 [a, b]).getD k 0 < zf ∧ zf < (insertCutsV a b used zs 0 [a, b]).getD (k + 1) 0) := by
  set F := insertCutsV a b used zs 0 [a, b] with hF
  have hG0 : Good [a, b] a b [] := ⟨chain_pair hab, rfl, rfl, le_refl _, fun s hs => absurd hs List.not_mem_nil⟩
  obtain ⟨hG, hmem⟩ := good_insertCuts a b hab used zs 0 [a, b] [] hG0
  rw [← hF] at hG hmem
  have hhead : F.headD 0 = a := by
    have := hG.head; rcases F with _ | ⟨f0, rest⟩
    · simp at this
    · simpa using this
  obtain ⟨k, hk, hk1, hk2, hno⟩ := piece_exists F hG.chain hG.len Y (by rw [hhead]; exact hY1)
    (by rw [hG.last]; exact hY2)
  have hFk : F.getD k 0 ∈ F := getD_mem_of_lt (by omega)
  have hFk1 : F.getD (k + 1) 0 ∈ F := getD_mem_of_lt hk
  have ha : a ≤ F.getD k 0 := by
    have := head_le_of_chain hG.chain _ hFk; rwa [hhead] at this
  have hb : F.getD (k + 1) 0 ≤ b := by
    have := le_lastV_of_chain hG.chain _ hFk1; rwa [hG.last] at this
  have hle : F.getD k 0 ≤ F.getD (k + 1) 0 := hk1.trans hk2
  -- the interpolation parameter
  obtain ⟨η, h0, h1, hY⟩ : ∃ η : ℝ, 0 ≤ η ∧ η ≤ 1 ∧ Y = lin2 (F.getD k 0) (F.getD (k + 1) 0) η := by
    rcases hle.lt_or_eq with hlt | heq
    · have hne : F.getD (k + 1) 0 - F.getD k 0 ≠ 0 := by linarith
      refine ⟨(Y - F.getD k 0) / (F.getD (k + 1) 0 - F.getD k 0), div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith), ?_⟩
      unfold lin2
      rw [show F.getD k 0 * (1 - (Y - F.getD k 0) / (F.getD (k + 1) 0 - F.getD k 0)) +
          F.getD (k + 1) 0 * ((Y - F.getD k 0) / (F.getD (k + 1) 0 - F.getD k 0)) =
          F.getD k 0 + (F.getD (k + 1) 0 - F.getD k 0) * ((Y - F.getD k 0) / (F.getD (k + 1) 0 - F.getD k 0)) by ring,
        mul_div_cancel₀ _ hne]
      ring
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      rw [← heq] at hk2
      have hYk : Y = F.getD k 0 := le_antisymm hk2 hk1
      unfold lin2; rw [hYk, ← heq]; ring
  refine ⟨k, η, hk, h0, h1, ha, hle, hb, hY, ?_⟩
  rintro ⟨hz1, hz2⟩
  have haz : a < zf := lt_of_le_of_lt ha hz1
  have hzb : zf < b := lt_of_lt_of_le hz2 hb
  rcases hzf with ⟨hlen, hz, hused⟩ | hout
  · have hc := hmem 0 hlen (by simpa using hused)
    rw [hz, min_eq_right hzb.le, max_eq_right haz.le] at hc
    exact hno zf hc ⟨hz1, hz2⟩
  · exact hout ⟨haz, hzb⟩

/-! ## The cuts used by a recipe -/

theorem usedCuts_ge (a b : DN) : ∀ (zs : List DN) (ci m : ℕ), m ∈ usedCuts a b zs ci → ci ≤ m
  | [], _, _, h => absurd h List.not_mem_nil
  | z :: zs, ci, m, h => by
    simp only [usedCuts] at h
    split_ifs at h
    · rcases List.mem_cons.mp h with rfl | h'
      · exact le_rfl
      · exact (Nat.le_succ ci).trans (usedCuts_ge a b zs (ci + 1) m h')
    · exact (Nat.le_succ ci).trans (usedCuts_ge a b zs (ci + 1) m h)

/-- The first cut is used exactly when it may lie strictly inside the range. -/
theorem usedCuts_contains_zero (a b z : DN) (zs : List DN) :
    (usedCuts a b (z :: zs) 0).contains 0 = true → overlaps z a b = true := by
  intro h
  simp only [usedCuts] at h
  by_contra ho
  simp only [ho, Bool.false_eq_true, if_false] at h
  have := usedCuts_ge a b zs 1 0 (by simpa using h)
  omega

/-- A cut that is not used lies outside the open range (all enclosed). -/
theorem not_inside_of_not_overlaps {L X : Ival} {fz fa fb : RF} {z a b : DN} (hz : DE L X fz z) (ha : DE L X fa a)
    (hb : DE L X fb b) (hzok : z.ok = true) (haok : a.ok = true) (hbok : b.ok = true) (h : overlaps z a b = false)
    {l x : ℝ} (hl : L.Mem l) (hx : X.Mem x) : ¬ (fa l x < fz l x ∧ fz l x < fb l x) := by
  have hz' := ((hz hzok).val l x hl hx)
  have ha' := ((ha haok).val l x hl hx)
  have hb' := ((hb hbok).val l x hl hx)
  simp only [overlaps, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at h
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · have := toR_le_toR.mpr h; linarith [hz'.2, ha'.1]
  · have := toR_le_toR.mpr h; linarith [hz'.1, hb'.2]

/-! ## The DN piece lists: head and length -/

theorem insertL_head (Ls : List DN) (c : DN) (h : Ls ≠ []) : (insertL Ls c).getD 0 zeroDN = Ls.getD 0 zeroDN := by
  rcases Ls with _ | ⟨a, rest⟩
  · exact absurd rfl h
  · rfl

theorem insertL_length (Ls : List DN) (c : DN) : Ls.length ≤ (insertL Ls c).length := by
  rcases Ls with _ | ⟨a, rest⟩
  · simp [insertL]
  · simp only [insertL, List.length_cons, List.length_append, List.length_singleton]
    have : ∀ (a : DN) (rest : List DN), (insMid c (a :: rest)).length = rest.length := by
      intro a rest
      induction rest generalizing a with
      | nil => simp [insMid]
      | cons b rest ih => simp [insMid, ih]
    rw [this]; omega

theorem insertCuts_head_length (a b : DN) (used : List ℕ) : ∀ (zs : List DN) (ci : ℕ) (Ls : List DN), Ls ≠ [] →
    (insertCuts a b used zs ci Ls).getD 0 zeroDN = Ls.getD 0 zeroDN ∧ Ls.length ≤ (insertCuts a b used zs ci Ls).length
  | [], _, Ls, _ => ⟨rfl, le_rfl⟩
  | z :: zs, ci, Ls, h => by
    simp only [insertCuts]
    split_ifs
    · have hne : insertL Ls (mx a (mn b z)) ≠ [] := by
        intro h'; have := insertL_length Ls (mx a (mn b z)); rw [h'] at this
        exact h (List.eq_nil_of_length_eq_zero (by simpa using this))
      obtain ⟨h1, h2⟩ := insertCuts_head_length a b used zs (ci + 1) _ hne
      exact ⟨h1.trans (insertL_head Ls _ h), (insertL_length Ls _).trans h2⟩
    · exact insertCuts_head_length a b used zs (ci + 1) Ls h

/-! ## The index of a list in `zipIdx` -/

theorem mem_zipIdx_getD {α : Type} (l : List α) (d : α) {n : ℕ} (hn : n < l.length) : (l.getD n d, n) ∈ l.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]
  simp [List.getD_eq_getElem _ _ hn, hn]

/-! ## Segments of the fixed-point numbers -/

theorem fdivP_eq (n : ℤ) : fdivP n = n / one := by
  unfold fdivP; rw [Int.shiftRight_eq_div_pow, one_eq]; norm_num

theorem one_pos'' : (0 : ℤ) < one := by unfold one; norm_num

theorem fdivP_le_of_lt {n m : ℤ} (h : n < (m + 1) * one) : fdivP n ≤ m := by
  rw [fdivP_eq]
  have := (Int.ediv_lt_iff_lt_mul one_pos'').mpr h
  omega

theorem le_fdivP_of_le {n m : ℤ} (h : m * one ≤ n) : m ≤ fdivP n := by
  rw [fdivP_eq]
  exact (Int.le_ediv_iff_mul_le one_pos'').mpr h

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The cell: flags, anchors, labels, lists -/

theorem ctxE_flags {L X : Ival} {sd : SegData} {fl : Flags} {c : Ctx}
    (h : CtxE L X sd ⟨fl.kern, fl.low, 3⟩ c) (hy : fl.y0b = c.y0b) : CtxE L X sd fl c :=
  { h with y0b := fun _ => hy.symm }

theorem ctx_y0b_le (sd : SegData) (lam x : DN) (fl : Flags) : (context sd lam x fl).y0b ≤ 2 := by
  simp only [context]; split_ifs <;> omega

theorem anchorPt_mem {A : Ival} (h : A.lo ≤ A.hi) (c : ℕ) : A.lo ≤ anchorPt A c ∧ anchorPt A c ≤ A.hi := by
  unfold anchorPt; split_ifs <;> omega

theorem anchor_enc {sd : SegData} {bx : BoxCtx} {fl : Flags} (hb : BoxOK bx) (hL : 0 < bx.lamI.lo)
    (hX : 0 < bx.xI.lo) (hk1 : fl.kern = false → bx.xI.hi < one) (code : ℕ) :
    CtxE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))) sd fl (anchorCtx sd bx fl code) := by
  have h1 := anchorPt_mem hb.hL (code / 3)
  have h2 := anchorPt_mem hb.hX (code % 3)
  exact context_enc_pt sd fl (by omega) (by omega) (fun hk => lt_of_le_of_lt h2.2 (hk1 hk))

theorem anchor_y0b {sd : SegData} {bx : BoxCtx} {fl : Flags} {c : Ctx} (hy : fl.y0b = c.y0b) (hc2 : c.y0b ≤ 2)
    (code : ℕ) : (anchorCtx sd bx fl code).y0b = c.y0b := by
  simp only [anchorCtx, context]
  rw [if_pos (by omega)]; exact hy

theorem mem_labels_low (c : Ctx) : ((0, 0) : ℕ × ℕ) ∈ labelsOf c := by
  simp [labelsOf]

theorem mem_labels_knot (c : Ctx) {j : ℕ} (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (h : (j : ℤ) * eighth ≤ c.upper.v.hi) :
    ((1, j) : ℕ × ℕ) ∈ labelsOf c := by
  unfold labelsOf
  apply List.mem_append_right
  simp only [List.mem_map, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  exact ⟨j, ⟨⟨hj1, by omega⟩, h⟩, rfl⟩

theorem mem_labels_high (c : Ctx) {j : ℕ} (hj7 : j ≤ 7) (hlo : fdivP (8 * c.upper.v.lo) ≤ j)
    (hhi : (j : ℤ) ≤ fdivP (8 * c.upper.v.hi)) : ((2, j) : ℕ × ℕ) ∈ labelsOf c := by
  unfold labelsOf
  apply List.mem_append_left
  apply List.mem_append_right
  simp only [List.mem_map, List.mem_range'_1]
  refine ⟨j, ⟨?_, ?_⟩, rfl⟩
  · have : max 0 (min 7 (fdivP (8 * c.upper.v.lo))) ≤ (j : ℤ) := max_le (by omega) ((min_le_right _ _).trans hlo)
    omega
  · have : (j : ℤ) ≤ max 0 (min 7 (fdivP (8 * c.upper.v.hi))) := le_max_of_le_right (le_min (by omega) hhi)
    omega

/-- The segments of the parent case `t/q = Y`. -/
def segsOf (c : Ctx) : List ℕ := (List.range 8).filter (fun (s : ℕ) => decide ((s : ℤ) * eighth < c.upper.v.hi))

theorem recipe_low (c : Ctx) : recipeOf c (0, 0) =
    .low (segsOf c) ((segsOf c).map (fun s => usedCuts (portion c s).1 (portion c s).2 c.cuts 0)) := rfl

theorem recipe_other (c : Ctx) {lab : ℕ × ℕ} (h : lab.1 ≠ 0) :
    recipeOf c lab = .other (usedCuts zeroDN (highOf c lab) c.cuts 0) := by
  simp [recipeOf, h]

theorem listsOf_low_getD (c : Ctx) (segs : List ℕ) (used : List (List ℕ)) {n : ℕ} (hn : n < segs.length) :
    (listsOf c (0, 0) (.low segs used)).getD n (0, []) =
      (segs[n], insertCuts (portion c segs[n]).1 (portion c segs[n]).2 (used.getD n []) c.cuts 0
        [(portion c segs[n]).1, (portion c segs[n]).2]) := by
  simp only [listsOf]
  rw [List.getD_eq_getElem _ _ (by simpa using hn)]
  simp [List.getElem_map, List.getElem_zipIdx]

theorem listsR_low_getD (cuts : List RF) (segs : List ℕ) (used : List (List ℕ)) {n : ℕ} (hn : n < segs.length) :
    (listsR upR cuts (0, 0) (.low segs used)).getD n (0, []) =
      (segs[n], rinsertCuts (fun l x => min ((segs[n] : ℝ) / 8) (upR l x))
        (fun l x => min (((segs[n] + 1 : ℕ) : ℝ) / 8) (upR l x)) (used.getD n []) cuts 0
        [fun l x => min ((segs[n] : ℝ) / 8) (upR l x), fun l x => min (((segs[n] + 1 : ℕ) : ℝ) / 8) (upR l x)]) := by
  simp only [listsR]
  rw [List.getD_eq_getElem _ _ (by simpa using hn)]
  simp [List.getElem_map, List.getElem_zipIdx]

theorem listsOf_low_length (c : Ctx) (segs : List ℕ) (used : List (List ℕ)) :
    (listsOf c (0, 0) (.low segs used)).length = segs.length := by
  simp [listsOf]

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem usedCuts_zero_of_overlaps {a b z : DN} (zs : List DN) (h : overlaps z a b = true) :
    (usedCuts a b (z :: zs) 0).contains 0 = true := by
  simp [usedCuts, h]

/-- **The payment on the list `n` of a parent case**: every `Y` of the list's range lies in a passing piece, and
the payment there (with A16's source and the piece's interpolated parent fields) is nonnegative. -/
theorem pay_at_list {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) {bx : BoxCtx} {fl : Flags} {c : Ctx} (hb : BoxOK bx)
    (hc : CtxE bx.lamI bx.xI sd fl c)
    (hA : ∀ code, CtxE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))) sd fl
      (anchorCtx sd bx fl code))
    (hAy : ∀ code, (anchorCtx sd bx fl code).y0b = c.y0b)
    (hcut0 : fl.low = false → (c.cuts.getD 0 zeroDN).ok = true ∧ ∃ z0 rest, c.cuts = z0 :: rest)
    {lab : ℕ × ℕ} (hlab : lab.2 ≤ 7) (n : ℕ)
    (hpass : ∀ k < ((listsOf c lab (recipeOf c lab)).getD n (0, [])).2.length - 1,
      pieceOK sd bx fl (ancArr sd bx fl) lab (recipeOf c lab) (alArr sd bx fl lab (recipeOf c lab)) n k
        (triples c lab ((listsOf c lab (recipeOf c lab)).getD n (0, [])).1
          (pieceAt ((listsOf c lab (recipeOf c lab)).getD n (0, [])).2 k).1
          (pieceAt ((listsOf c lab (recipeOf c lab)).getD n (0, [])).2 k).2) = true)
    (a b : RF) (A B : DN) (s : ℕ)
    (hFR : (listsR upR (cutsR fl.low c.y0b) lab (recipeOf c lab)).getD n (0, []) =
      (s, rinsertCuts a b (usedCuts A B c.cuts 0) (cutsR fl.low c.y0b) 0 [a, b]))
    (hAe : DE bx.lamI bx.xI a A) (hBe : DE bx.lamI bx.xI b B) (hAok : A.ok = true) (hBok : B.ok = true)
    {l x : ℝ} (hl : bx.lamI.Mem l) (hx : bx.xI.Mem x) (hl0 : 0 < l) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hab : a l x ≤ b l x) (ha0 : 0 ≤ a l x) (hbP : b l x ≤ upR l x)
    {Y : ℝ} (hY1 : a l x ≤ Y) (hY2 : Y ≤ b l x) (z : ℝ) :
    ∃ (η : ℝ) (FA FB : RF), 0 ≤ η ∧ η ≤ 1 ∧ a l x ≤ FA l x ∧ FA l x ≤ FB l x ∧ FB l x ≤ b l x ∧
      Y = lin2 (FA l x) (FB l x) η ∧
      0 ≤ payE ((ctxR sd fl).C l x) (1 - qR l * Y) (src l (pR l x) (1 - qR l * Y)) (pR l x) z
        ((ctxR sd fl).au l x) ((ctxR sd fl).av l x) ((ctxR sd fl).so l x)
        (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).u l x η) (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).v l x η)
        (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).s l x η) ((ctxR sd fl).tau l x)
        (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).t l x η) ((ctxR sd fl).w l x) ((ctxR sd fl).phi l x)
        ((ctxR sd fl).ell l x) ((ctxR sd fl).G l x) ((ctxR sd fl).hp l x) := by
  set used := usedCuts A B c.cuts 0 with hused
  set zs := (cutsR fl.low c.y0b).map (fun f => f l x) with hzs
  -- the first source cut is not strictly inside a piece
  obtain ⟨zf, hzf, hzfdef⟩ : ∃ zf : ℝ, ((0 < zs.length ∧ zs.getD 0 0 = zf ∧ used.contains 0 = true) ∨
      ¬ (a l x < zf ∧ zf < b l x)) ∧ (fl.low = false → zf = nnR l x / pR l x) := by
    cases hlow : fl.low
    · refine ⟨nnR l x / pR l x, ?_, fun _ => rfl⟩
      obtain ⟨hok0, z0, rest, hcuts⟩ := hcut0 hlow
      by_cases hu : used.contains 0 = true
      · left
        refine ⟨by simp [hzs, cutsR, hlow], by simp [hzs, cutsR, hlow, cutR], hu⟩
      · right
        have hov : overlaps (c.cuts.getD 0 zeroDN) A B = false := by
          rw [hcuts, List.getD_cons_zero]
          by_contra h
          apply hu
          rw [hused, hcuts]
          exact usedCuts_zero_of_overlaps rest (by simpa using h)
        have hlen : 0 < c.cuts.length := by rw [hcuts]; simp
        have hz0 : DE bx.lamI bx.xI (cutR c.y0b 0) (c.cuts.getD 0 zeroDN) := hc.cuts.2 0 hlen
        have := not_inside_of_not_overlaps hz0 hAe hBe hok0 hAok hBok hov hl hx
        simpa [cutR] using this
    · exact ⟨a l x, Or.inr (fun h => lt_irrefl _ h.1), fun h => absurd h (by simp)⟩
  obtain ⟨k, η, hk, h0, h1, haF, hle, hbF, hY, hnot⟩ := find_piece_vals (a l x) (b l x) hab used zs hY1 hY2 zf hzf
  -- the real piece ends
  set RL := rinsertCuts a b used (cutsR fl.low c.y0b) 0 [a, b] with hRL
  have hev : RL.map (fun f => f l x) = insertCutsV (a l x) (b l x) used zs 0 [a l x, b l x] := by
    rw [hRL, ev_insertCuts]; rfl
  have hFA : (RL.getD k 0) l x = (insertCutsV (a l x) (b l x) used zs 0 [a l x, b l x]).getD k 0 := by
    rw [← hev, getD_map_ev]
  have hFB : (RL.getD (k + 1) 0) l x = (insertCutsV (a l x) (b l x) used zs 0 [a l x, b l x]).getD (k + 1) 0 := by
    rw [← hev, getD_map_ev]
  have hlenR : RL.length = (insertCutsV (a l x) (b l x) used zs 0 [a l x, b l x]).length := by
    rw [← hev, List.length_map]
  -- the cell's piece passes
  obtain ⟨hseg, hle2⟩ := lists_at hc c.y0b rfl lab (recipeOf c lab) n
  rw [hFR] at hseg hle2
  have hlenC : ((listsOf c lab (recipeOf c lab)).getD n (0, [])).2.length = RL.length := hle2.length_eq.symm
  have hpk := hpass k (by rw [hlenC, hlenR]; omega)
  have hbq : ∀ part < 3, ∀ ζ : ℝ, (if part = 1 then 0 ≤ ζ ∧ ζ ≤ 1 else 0 ≤ ζ) →
      0 ≤ bq ((triplesR (ctxR sd fl) fl.low lab s (RL.getD k 0) (RL.getD (k + 1) 0)).getD part []) l x η ζ := by
    intro part hp ζ hζ
    have := piece_sound hb hc hA hAy hlab (recipeOf c lab) n k (listsOf_seg_le c lab n) hpk part hp hl hx h0 h1 hζ
    rw [hFR] at this
    exact this
  refine ⟨η, RL.getD k 0, RL.getD (k + 1) 0, h0, h1, by rw [hFA]; exact haF, by rw [hFA, hFB]; exact hle,
    by rw [hFB]; exact hbF, by rw [hFA, hFB]; exact hY, ?_⟩
  refine pay_of_bq hγ fl lab s (RL.getD k 0) (RL.getD (k + 1) 0) hl0 hx0 hx1 (by rw [hFA]; linarith)
    (by rw [hFA, hFB]; exact hle) (by rw [hFB]; linarith) ?_ h0 h1 hbq Y (by rw [hFA, hFB]; exact hY) z
  intro hlow
  rw [← hzfdef hlow, hFA, hFB]
  exact hnot

end Erdos993Lean.Analytic.O2.Cert
