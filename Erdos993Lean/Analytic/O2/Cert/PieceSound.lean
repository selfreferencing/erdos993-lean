import Mathlib
import Erdos993Lean.Analytic.O2.Cert.SourceSound
import Erdos993Lean.Analytic.O2.Cert.LowerSound
import Erdos993Lean.Analytic.O2.Cert.PartSound
import Erdos993Lean.Analytic.O2.Cert.ListSound

/-!
# O2 certificate checker (lane A18): one piece

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  A passing piece (`pieceOK`) of a cell:

* its side conditions: the lower piece end and `p > 0` are enclosed (`pieceOK_ok`, from the first control of part
  `0`), hence the upper end of `P` and the first source cut of the cell (`cell_upper_hi_pos`, `cell_cut0_ok`);
* the Bernstein combination of each part is nonnegative on the box (**`piece_sound`**: the cell's and the anchors'
  controls enclose the same real controls, `triples_enc` and `lists_enc` at the anchors' point boxes, then
  `partcheck_sound`);
* it is the payment on the part's response range (`bq_eq_payE`), with the parent fields of the parent cases
  `t/q = Y`, `P`, `j/8` (`parAt_low`, `parAt_high`, `parAt_knot`), and with A16's source above the chord it gives the
  payment (**`pay_of_bq`**).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## Memo tables and side conditions of a passing cell -/

/-- A memo table of thunks returns the memoized function (the default is the same value). -/
theorem getD_thunk_range {α : Type} (f : ℕ → α) (code : ℕ) :
    (((Array.range 9).map (fun c => Thunk.mk (fun _ => f c))).getD code (Thunk.mk (fun _ => f code))).get =
      f code := by
  by_cases h : code < 9
  · simp [Array.getD, h]
  · simp [Array.getD, h]

theorem forall₂_getD {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β} (h : List.Forall₂ R l1 l2)
    {d1 : α} {d2 : β} (hd : R d1 d2) (n : ℕ) : R (l1.getD n d1) (l2.getD n d2) := by
  induction h generalizing n with
  | nil => simpa using hd
  | cons hab _ ih =>
    cases n with
    | zero => simpa using hab
    | succ n => simpa using ih n

theorem mx_ok (a b : DN) : (mx a b).ok = (a.ok && b.ok) := by unfold mx; split_ifs <;> rfl

theorem mn_ok (a b : DN) : (mn a b).ok = (a.ok && b.ok) := by unfold mn; split_ifs <;> rfl

/-- A passing quadratic test has an enclosed constant coefficient. -/
theorem quad_E_ok {bx : BoxCtx} {anchor : ℕ → Tri} {t : Tri} {part : ℕ} (h : quad bx anchor t part = true) :
    t.E.ok = true := by
  by_cases h2 : lowerB bx anchor t 2 false < 0
  · unfold quad at h; simp only [h2, if_true] at h; exact absurd h (by decide)
  · have h3 : 0 ≤ lowerB bx anchor t 2 false := not_lt.mp h2
    rw [lowerB_eq] at h3
    simpa [derive] using lowerCore_ok h3

/-- A passing part check has an enclosed constant coefficient in its first control. -/
theorem partcheck_head_ok {bx : BoxCtx} {anch : List Bool → ℕ → ℕ → Tri} {part lvl : ℕ} {t0 : Tri}
    {rest : List Tri} (h : partcheck bx anch part lvl [] (t0 :: rest) = true) : t0.E.ok = true := by
  cases lvl with
  | zero => simp only [partcheck, allQuad, Bool.and_eq_true] at h; exact quad_E_ok h.1
  | succ lvl =>
    simp only [partcheck, allQuad, headT, List.headD_cons, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · exact quad_E_ok h.1
    · exact quad_E_ok h.1.1.1

/-- Part `0` of a piece has a first control. -/
theorem triples_part0 (c : Ctx) (lab : ℕ × ℕ) (s : ℕ) (ya yb : DN) :
    ∃ t0 rest, (triples c lab s ya yb).getD 0 [] = t0 :: rest := by
  simp only [triples, controls, List.getD_cons_zero]
  exact ⟨_, _, rfl⟩

/-- The constant coefficient of the first control of part `0` is enclosed only if the lower piece end and
`p > 0` are. -/
theorem triples_E0_ok {c : Ctx} {lab : ℕ × ℕ} {s : ℕ} {ya yb : DN}
    (h : (((triples c lab s ya yb).getD 0 []).getD 0 ⟨zeroDN, zeroDN, zeroDN⟩).E.ok = true) :
    ya.ok = true ∧ c.p.ok = true ∧ 0 < c.p.v.lo := by
  simp only [triples, controls, belev, badd, bsub, bneg, bmul, lin, List.getD_cons_zero, List.getD_cons_succ,
    List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.zipWith_nil_right] at h
  simp [dadd, dsub, dneg, dmul, dmulI, ddiv, ddivI, daddI, drsubI, dsubI] at h
  refine ⟨?_, ?_, ?_⟩ <;> tauto

/-- **The side conditions of a passing piece**: its lower end and `p > 0` are enclosed. -/
theorem pieceOK_ok {sd : SegData} {bx : BoxCtx} {fl : Flags} {anc : Array (Thunk Ctx)} {lab : ℕ × ℕ}
    {rcp : Recipe} {al : Array (Thunk (List (ℕ × List DN)))} {n k : ℕ} {c : Ctx} {s : ℕ} {ya yb : DN}
    (h : pieceOK sd bx fl anc lab rcp al n k (triples c lab s ya yb) = true) :
    ya.ok = true ∧ c.p.ok = true ∧ 0 < c.p.v.lo := by
  simp only [pieceOK, List.all_eq_true, List.mem_range] at h
  have h0 := h 0 (by norm_num)
  obtain ⟨t0, rest, e⟩ := triples_part0 c lab s ya yb
  rw [e] at h0
  have h1 := partcheck_head_ok h0
  have ht0 : ((triples c lab s ya yb).getD 0 []).getD 0 ⟨zeroDN, zeroDN, zeroDN⟩ = t0 := by rw [e]; rfl
  rw [← ht0] at h1
  exact triples_E0_ok h1

theorem cdiv_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < cdiv a b := by
  unfold cdiv
  have : (-a) / b < 0 := Int.ediv_neg_of_neg_of_pos (by omega) hb
  omega

theorem fdiv_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ fdiv a b := by
  unfold fdiv; exact Int.ediv_nonneg ha hb

section CellCtx

variable {sd : SegData} {fl : Flags} {L X : Ival}

theorem one_pos' : (0 : ℤ) < one := by unfold one; norm_num

theorem ctx_q (sd : SegData) (lam x : DN) (fl : Flags) : (context sd lam x fl).q = ddiv lam (daddI lam oneI) := rfl

theorem ctx_p (sd : SegData) (lam x : DN) (fl : Flags) : (context sd lam x fl).p = dmul (context sd lam x fl).q x :=
  rfl

theorem ctx_upper (sd : SegData) (lam x : DN) (fl : Flags) :
    (context sd lam x fl).upper = ddiv (drsubI oneI (context sd lam x fl).p)
      (drsubI oneI (dmul (context sd lam x fl).q (context sd lam x fl).p)) := rfl

theorem cell_q_ok (hL : 0 < L.lo) : (context sd (lamDN L) (xDN X) fl).q.ok = true := by
  rw [ctx_q]
  simp only [ddiv, daddI, lamDN, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and, add, oneI, pt]
  have := one_pos'; omega

theorem cell_q_lo (hL : 0 < L.lo) (hLL : L.lo ≤ L.hi) : 0 ≤ (context sd (lamDN L) (xDN X) fl).q.v.lo := by
  rw [ctx_q]
  simp only [ddiv, daddI, lamDN, div, add, oneI, pt]
  have h0 := one_pos'
  have h1 : 0 ≤ L.lo * one := mul_nonneg hL.le h0.le
  exact le_min (fdiv_nonneg h1 (by omega)) (fdiv_nonneg h1 (by omega))

theorem cell_p_ok (hL : 0 < L.lo) : (context sd (lamDN L) (xDN X) fl).p.ok = true := by
  rw [ctx_p]
  simp only [dmul, xDN, Bool.and_true]
  exact cell_q_ok hL

/-- The upper end of the enclosure of `P` is positive (so the parent case `t/q = Y` has a piece). -/
theorem cell_upper_hi_pos (hc : CtxE L X sd fl (context sd (lamDN L) (xDN X) fl)) (hL : 0 < L.lo)
    (hLL : L.lo ≤ L.hi) (hX : 0 < X.lo) (hXX : X.lo ≤ X.hi) (hX1 : X.hi ≤ one) :
    0 < (context sd (lamDN L) (xDN X) fl).upper.v.hi := by
  have hq := cell_q_ok (sd := sd) (fl := fl) (X := X) hL
  have hp := cell_p_ok (sd := sd) (fl := fl) (X := X) hL
  set c := context sd (lamDN L) (xDN X) fl with hcdef
  have hup : c.upper = ddiv (drsubI oneI c.p) (drsubI oneI (dmul c.q c.p)) := ctx_upper _ _ _ _
  -- a point of the box
  have hl : L.Mem (toR L.lo) := ⟨le_rfl, toR_le_toR.mpr hLL⟩
  have hx : X.Mem (toR X.lo) := ⟨le_rfl, toR_le_toR.mpr hXX⟩
  have hl0 : 0 < toR L.lo := toR_pos.mpr hL
  have hx0 : 0 < toR X.lo := toR_pos.mpr hX
  have hx1 : toR X.lo ≤ 1 := by have := toR_le_toR.mpr (hXX.trans hX1); rwa [toR_one] at this
  have hqv := qR_pos hl0
  have hq1 := qR_lt_one hl0
  have hpv : pR (toR L.lo) (toR X.lo) < 1 := by unfold pR; nlinarith
  have hpv0 : 0 < pR (toR L.lo) (toR X.lo) := by unfold pR; positivity
  have hok1 : (drsubI oneI c.p).ok = true := by simpa [drsubI, dneg, daddI] using hp
  have hok2 : (drsubI oneI (dmul c.q c.p)).ok = true := by simp [drsubI, dneg, daddI, dmul, hp, hq]
  have homp := ((de_rsubI mem_oneI hc.p) hok1).val _ _ hl hx
  have hden := ((de_rsubI mem_oneI (de_mul hc.q hc.p)) hok2).val _ _ hl hx
  have h1 : 0 < (drsubI oneI c.p).v.hi := by
    have : 0 < toR (drsubI oneI c.p).v.hi := by linarith [homp.2]
    exact toR_pos.mp this
  have h2 : 0 < (drsubI oneI (dmul c.q c.p)).v.hi := by
    have : 0 < toR (drsubI oneI (dmul c.q c.p)).v.hi := by
      have : qR (toR L.lo) * pR (toR L.lo) (toR X.lo) < 1 := by nlinarith
      linarith [hden.2]
    exact toR_pos.mp this
  rw [hup]
  simp only [ddiv, div]
  exact lt_max_of_lt_right (cdiv_pos (mul_pos h1 one_pos') h2)

/-- In source mode the first cut `Y_f` is enclosed as soon as `p > 0` is. -/
theorem cell_cut0_ok (hL : 0 < L.lo) (hLL : L.lo ≤ L.hi) (hlow : fl.low = false)
    (hp : 0 < (context sd (lamDN L) (xDN X) fl).p.v.lo) :
    ((context sd (lamDN L) (xDN X) fl).cuts.getD 0 zeroDN).ok = true := by
  have hq := cell_q_ok (sd := sd) (fl := fl) (X := X) hL
  have hqlo := cell_q_lo (sd := sd) (fl := fl) (X := X) hL hLL
  have hpok := cell_p_ok (sd := sd) (fl := fl) (X := X) hL
  have hk : 0 < (daddI (context sd (lamDN L) (xDN X) fl).q oneI).v.lo := by
    simp only [daddI, add, oneI, pt]; have := one_pos'; omega
  rw [cuts_eq]
  simp only [hlow, Bool.false_eq_true, if_false, List.getD_cons_zero]
  simp [ddiv, nnDN, kapDN, mx_ok, dsub, dadd, dneg, zeroDN, DN.cst, hq, hpok, hp, hk]
  exact ⟨rfl, rfl, hq⟩

end CellCtx

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## One piece -/

/-- The memo table of the anchor contexts of a cell (as in `boxOK`). -/
def ancArr (sd : SegData) (bx : BoxCtx) (fl : Flags) : Array (Thunk Ctx) :=
  (Array.range 9).map (fun code => Thunk.mk (fun _ => anchorCtx sd bx fl code))

/-- The memo table of the anchor piece lists of a parent case (as in `boxOK`). -/
def alArr (sd : SegData) (bx : BoxCtx) (fl : Flags) (lab : ℕ × ℕ) (rcp : Recipe) :
    Array (Thunk (List (ℕ × List DN))) :=
  (Array.range 9).map (fun code => Thunk.mk (fun _ => anchorLists sd bx fl (ancArr sd bx fl) lab rcp code))

theorem ancGet_eq (sd : SegData) (bx : BoxCtx) (fl : Flags) (code : ℕ) :
    ancGet sd bx fl (ancArr sd bx fl) code = anchorCtx sd bx fl code := by
  unfold ancGet ancArr; exact getD_thunk_range _ code

theorem alGet_eq (sd : SegData) (bx : BoxCtx) (fl : Flags) (lab : ℕ × ℕ) (rcp : Recipe) (code : ℕ) :
    alGet sd bx fl (ancArr sd bx fl) lab rcp (alArr sd bx fl lab rcp) code =
      listsOf (anchorCtx sd bx fl code) lab rcp := by
  unfold alGet alArr
  rw [getD_thunk_range (fun code => anchorLists sd bx fl (ancArr sd bx fl) lab rcp code) code]
  unfold anchorLists; rw [ancGet_eq]

theorem triplesR_length (cr : CR) (low : Bool) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (part : ℕ) (hp : part < 3) :
    ((triplesR cr low lab s ya yb).getD part []).length = 3 := by
  interval_cases part <;> simp [triplesR, rcontrols]

/-- The real lists of a cell and of its anchors are the same. -/
theorem lists_at {L X : Ival} {sd : SegData} {fl : Flags} {c : Ctx} (hc : CtxE L X sd fl c) (y0 : ℕ)
    (hy : c.y0b = y0) (lab : ℕ × ℕ) (rcp : Recipe) (n : ℕ) :
    ((listsR upR (cutsR fl.low y0) lab rcp).getD n (0, [])).1 = ((listsOf c lab rcp).getD n (0, [])).1 ∧
      LE L X ((listsR upR (cutsR fl.low y0) lab rcp).getD n (0, [])).2 ((listsOf c lab rcp).getD n (0, [])).2 := by
  have h := lists_enc hc lab rcp
  rw [hy] at h
  exact forall₂_getD h (d1 := (0, [])) (d2 := (0, [])) ⟨rfl, le_nil⟩ n

/-- The segment of every piece list of a recipe of the cell is at most `7`. -/
theorem listsOf_seg_le (c : Ctx) (lab : ℕ × ℕ) (n : ℕ) : ((listsOf c lab (recipeOf c lab)).getD n (0, [])).1 ≤ 7 := by
  unfold recipeOf
  split_ifs
  · simp only [listsOf]
    rw [List.getD_eq_getD_getElem?]
    rcases h : (List.map _ _)[n]? with _ | ⟨a⟩
    · simp
    · simp only [Option.getD_some]
      obtain ⟨hm, e⟩ := List.getElem?_eq_some_iff.mp h
      rw [← e]
      simp only [List.getElem_map, List.getElem_zipIdx]
      have := List.getElem_mem (l := (List.range 8).filter (fun (s : ℕ) => decide ((s : ℤ) * eighth < c.upper.v.hi)))
        (n := n) (by simpa using hm)
      simp only [List.mem_filter, List.mem_range] at this
      omega
  · simp only [listsOf]
    cases n <;> simp

/-- **One piece**: a passing piece makes the Bernstein combination of each of its parts nonnegative on the
box, for every piece coordinate and every response in the part's range. -/
theorem piece_sound {sd : SegData} {bx : BoxCtx} {fl : Flags} {c : Ctx} (hb : BoxOK bx)
    (hc : CtxE bx.lamI bx.xI sd fl c)
    (hA : ∀ code, CtxE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))) sd fl
      (anchorCtx sd bx fl code))
    (hAy : ∀ code, (anchorCtx sd bx fl code).y0b = c.y0b)
    {lab : ℕ × ℕ} (hlab : lab.2 ≤ 7) (rcp : Recipe) (n k : ℕ) (hs : ((listsOf c lab rcp).getD n (0, [])).1 ≤ 7)
    (hok : pieceOK sd bx fl (ancArr sd bx fl) lab rcp (alArr sd bx fl lab rcp) n k
      (triples c lab ((listsOf c lab rcp).getD n (0, [])).1 (pieceAt ((listsOf c lab rcp).getD n (0, [])).2 k).1
        (pieceAt ((listsOf c lab rcp).getD n (0, [])).2 k).2) = true)
    (part : ℕ) (hpart : part < 3) {l x : ℝ} (hl : bx.lamI.Mem l) (hx : bx.xI.Mem x) {η : ℝ} (h0 : 0 ≤ η)
    (h1 : η ≤ 1) {ζ : ℝ} (hζ : if part = 1 then 0 ≤ ζ ∧ ζ ≤ 1 else 0 ≤ ζ) :
    0 ≤ bq ((triplesR (ctxR sd fl) fl.low lab ((listsR upR (cutsR fl.low c.y0b) lab rcp).getD n (0, [])).1
      (((listsR upR (cutsR fl.low c.y0b) lab rcp).getD n (0, [])).2.getD k 0)
      (((listsR upR (cutsR fl.low c.y0b) lab rcp).getD n (0, [])).2.getD (k + 1) 0)).getD part []) l x η ζ := by
  set FR := (listsR upR (cutsR fl.low c.y0b) lab rcp).getD n (0, []) with hFR
  set CL := (listsOf c lab rcp).getD n (0, []) with hCL
  obtain ⟨hseg, hle⟩ := lists_at hc c.y0b rfl lab rcp n
  rw [← hFR, ← hCL] at hseg hle
  rw [hseg]
  -- the cell's controls
  have hT := triples_enc hc lab hlab CL.1 hs (le_getD hle k) (le_getD hle (k + 1))
  have hT0 := forall₂_getD hT (d1 := []) (d2 := []) List.Forall₂.nil part
  -- the anchors' controls
  have hTa : ∀ code, List.Forall₂ (TE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))))
      ((triplesR (ctxR sd fl) fl.low lab CL.1 (FR.2.getD k 0) (FR.2.getD (k + 1) 0)).getD part [])
      ((anchorTriples sd bx fl (ancArr sd bx fl) lab rcp (alArr sd bx fl lab rcp) n k code).getD part []) := by
    intro code
    obtain ⟨hsegA, hleA⟩ := lists_at (hA code) c.y0b (hAy code) lab rcp n
    rw [← hFR] at hsegA hleA
    have hsA : ((listsOf (anchorCtx sd bx fl code) lab rcp).getD n (0, [])).1 ≤ 7 := by
      rw [← hsegA, hseg]; exact hs
    have hTA := triples_enc (hA code) lab hlab _ hsA (le_getD hleA k) (le_getD hleA (k + 1))
    simp only [anchorTriples, alGet_eq, ancGet_eq]
    rw [← hseg, hsegA]
    exact forall₂_getD hTA (d1 := []) (d2 := []) List.Forall₂.nil part
  -- the part check
  simp only [pieceOK, List.all_eq_true, List.mem_range] at hok
  have hpc := hok part hpart
  refine partcheck_sound bx hb part _ _ (triplesR_length _ _ _ _ _ _ part hpart) _ ?_ 3 [] hT0 hpc l x hl hx η h0 h1
    ζ hζ
  intro path j code
  have e := getD_thunk_range (fun code => anchorTriples sd bx fl (ancArr sd bx fl) lab rcp (alArr sd bx fl lab rcp)
    n k code) code
  simp only at e ⊢
  rw [e]
  exact te_getD (te_subP path (hTa code)) j

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## From the Bernstein combination to the payment -/

/-- The Bernstein combination of a part is the payment on the part's response range. -/
theorem bq_eq_payE (cr : CR) (low : Bool) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (l x η z : ℝ) (part : ℕ)
    (hz : (part = 0 ∧ z ≤ 0) ∨ (part = 1 ∧ 0 ≤ z ∧ z ≤ 1) ∨ (part = 2 ∧ 1 ≤ z)) :
    bq ((triplesR cr low lab s ya yb).getD part []) l x η (etaOf part z) =
      payE (cr.C l x) (lin2 (1 - cr.q l x * ya l x) (1 - cr.q l x * yb l x) η)
        (lin2 (srcR cr low ya l x) (srcR cr low yb l x) η) (cr.p l x) z (cr.au l x) (cr.av l x) (cr.so l x)
        (parAt cr lab s ya yb cr.u l x η) (parAt cr lab s ya yb cr.v l x η) (parAt cr lab s ya yb cr.s l x η)
        (cr.tau l x) (parAt cr lab s ya yb cr.t l x η) (cr.w l x) (cr.phi l x) (cr.ell l x) (cr.G l x)
        (cr.hp l x) := by
  have hp : part < 3 := by omega
  rw [payE_quad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ part hz, ← bernA cr low lab s ya yb l x η part hp,
    ← bernB cr low lab s ya yb l x η part hp, ← bernE cr low lab s ya yb l x η part hp]
  rfl

/-- The part of a response and the range of its variable. -/
theorem part_of_z (z : ℝ) : ∃ part, ((part = 0 ∧ z ≤ 0) ∨ (part = 1 ∧ 0 ≤ z ∧ z ≤ 1) ∨ (part = 2 ∧ 1 ≤ z)) ∧
    part < 3 ∧ (if part = 1 then 0 ≤ etaOf part z ∧ etaOf part z ≤ 1 else 0 ≤ etaOf part z) := by
  rcases le_total z 0 with h | h
  · exact ⟨0, Or.inl ⟨rfl, h⟩, by norm_num, by simp [etaOf]; linarith⟩
  · rcases le_total z 1 with h1 | h1
    · exact ⟨1, Or.inr (Or.inl ⟨rfl, h, h1⟩), by norm_num, by simp [etaOf]; constructor <;> linarith⟩
    · exact ⟨2, Or.inr (Or.inr ⟨rfl, h1⟩), by norm_num, by simp [etaOf]; linarith⟩

/-! ## The parent fields -/

/-- The real field of a table pair at a point `τ` of the parent (`pwLin` of the knots at `λ`). -/
theorem segR_eq_field (sd : SegData) (L R : Array ℚ) (j : ℕ) (hj : j < 8) (X : RF) (l x : ℝ)
    (h1 : (j : ℝ) / 8 ≤ X l x) (h2 : X l x ≤ ((j : ℝ) + 1) / 8) :
    segR (fun i l _ => lerpR sd.lo sd.hi L[i]! R[i]! l) X j l x = fieldR sd L R l (X l x) := by
  unfold segR fieldR
  rw [pwLin_eq_cell _ j hj h1 h2]
  simp only
  ring

theorem clampR_eq (Y : RF) (s : ℕ) (l x : ℝ) (h1 : (s : ℝ) / 8 ≤ Y l x) (h2 : Y l x ≤ ((s : ℝ) + 1) / 8) :
    clampR Y s l x = Y l x := by
  unfold clampR
  rw [min_eq_right (by push_cast; linarith), max_eq_right h1]

/-- The parent field of the parent case `t/q = Y` on a piece inside segment `s`. -/
theorem parAt_low (cr : CR) (sd : SegData) (L R : Array ℚ) (f : ℕ → RF)
    (hf : f = fun i l _ => lerpR sd.lo sd.hi L[i]! R[i]! l) (s : ℕ) (hs : s < 8) (ya yb : RF) (l x η : ℝ)
    (h0 : 0 ≤ η) (h1 : η ≤ 1) (ha1 : (s : ℝ) / 8 ≤ ya l x) (ha2 : ya l x ≤ yb l x)
    (hb2 : yb l x ≤ ((s : ℝ) + 1) / 8) :
    parAt cr (0, 0) s ya yb f l x η = fieldR sd L R l (lin2 (ya l x) (yb l x) η) := by
  have hY1 : (s : ℝ) / 8 ≤ lin2 (ya l x) (yb l x) η := by unfold lin2; nlinarith
  have hY2 : lin2 (ya l x) (yb l x) η ≤ ((s : ℝ) + 1) / 8 := by unfold lin2; nlinarith
  simp only [parAt, show ((0, 0) : ℕ × ℕ).1 = 0 from rfl, zero_ne_one, OfNat.zero_ne_ofNat, if_false]
  have ca := clampR_eq ya s l x ha1 (ha2.trans hb2)
  have cb := clampR_eq yb s l x (ha1.trans ha2) hb2
  subst hf
  rw [segR_eq_field sd L R s hs _ l x (by rw [ca]; exact ha1) (by rw [ca]; exact ha2.trans hb2),
    segR_eq_field sd L R s hs _ l x (by rw [cb]; exact ha1.trans ha2) (by rw [cb]; exact hb2), ca, cb]
  unfold fieldR
  rw [pwLin_eq_cell _ s hs ha1 (ha2.trans hb2), pwLin_eq_cell _ s hs (ha1.trans ha2) hb2,
    pwLin_eq_cell _ s hs hY1 hY2]
  unfold lin2
  ring

/-- The parent field of the parent case `t/q = P` (segment `j`). -/
theorem parAt_high (cr : CR) (sd : SegData) (L R : Array ℚ) (f : ℕ → RF)
    (hf : f = fun i l _ => lerpR sd.lo sd.hi L[i]! R[i]! l) (j : ℕ) (hj : j < 8) (s : ℕ) (ya yb : RF) (l x η : ℝ)
    (h1 : (j : ℝ) / 8 ≤ cr.upper l x) (h2 : cr.upper l x ≤ ((j : ℝ) + 1) / 8) :
    parAt cr (2, j) s ya yb f l x η = fieldR sd L R l (cr.upper l x) := by
  simp only [parAt, show ((2, j) : ℕ × ℕ).1 = 2 from rfl, show ((2, j) : ℕ × ℕ).2 = j from rfl,
    OfNat.ofNat_ne_one, if_false, if_true]
  subst hf
  rw [segR_eq_field sd L R j hj _ l x (by rw [clampR_eq _ j l x h1 h2]; exact h1)
    (by rw [clampR_eq _ j l x h1 h2]; exact h2), clampR_eq _ j l x h1 h2]

/-- The parent field of the parent case `t/q = j/8`. -/
theorem parAt_knot (cr : CR) (sd : SegData) (L R : Array ℚ) (f : ℕ → RF)
    (hf : f = fun i l _ => lerpR sd.lo sd.hi L[i]! R[i]! l) (j : ℕ) (hj : j ≤ 8) (s : ℕ) (ya yb : RF) (l x η : ℝ) :
    parAt cr (1, j) s ya yb f l x η = fieldR sd L R l ((j : ℝ) / 8) := by
  simp only [parAt, show ((1, j) : ℕ × ℕ).1 = 1 from rfl, show ((1, j) : ℕ × ℕ).2 = j from rfl, if_true]
  subst hf
  unfold fieldR
  have := pwLin_knot (fun i : Fin 9 => lerpR sd.lo sd.hi L[(i : ℕ)]! R[(i : ℕ)]! l) ⟨j, by omega⟩
  simp only at this
  rw [this]

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The payment on a passing piece -/

/-- **The payment on a piece** from the nonnegativity of its Bernstein combinations: with A16's source `g`
(above the chord of the retained-source bound, no kink of `f(xr)` strictly inside), the payment with the
interpolated parent fields is nonnegative for every response `z`. -/
theorem pay_of_bq {sd : SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) (fl : Flags) (lab : ℕ × ℕ) (s : ℕ) (FA FB : RF)
    {l x η : ℝ} (hl0 : 0 < l) (hx0 : 0 < x) (hx1 : x ≤ 1) (ha0 : 0 ≤ FA l x) (hab : FA l x ≤ FB l x)
    (hbP : FB l x ≤ upR l x) (hcut : fl.low = false → ¬ (FA l x < nnR l x / pR l x ∧ nnR l x / pR l x < FB l x))
    (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (hbq : ∀ part < 3, ∀ ζ : ℝ, (if part = 1 then 0 ≤ ζ ∧ ζ ≤ 1 else 0 ≤ ζ) →
      0 ≤ bq ((triplesR (ctxR sd fl) fl.low lab s FA FB).getD part []) l x η ζ)
    (Y : ℝ) (hY : Y = lin2 (FA l x) (FB l x) η) (z : ℝ) :
    0 ≤ payE ((ctxR sd fl).C l x) (1 - qR l * Y) (src l (pR l x) (1 - qR l * Y)) (pR l x) z
      ((ctxR sd fl).au l x) ((ctxR sd fl).av l x) ((ctxR sd fl).so l x)
      (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).u l x η) (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).v l x η)
      (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).s l x η) ((ctxR sd fl).tau l x)
      (parAt (ctxR sd fl) lab s FA FB (ctxR sd fl).t l x η) ((ctxR sd fl).w l x) ((ctxR sd fl).phi l x)
      ((ctxR sd fl).ell l x) ((ctxR sd fl).G l x) ((ctxR sd fl).hp l x) := by
  obtain ⟨part, hz, hpart, hζ⟩ := part_of_z z
  have hq := hbq part hpart _ hζ
  rw [bq_eq_payE _ _ _ _ _ _ l x η z part hz] at hq
  generalize ha : FA l x = a at *
  generalize hb : FB l x = b at *
  have hr : lin2 (1 - (ctxR sd fl).q l x * a) (1 - (ctxR sd fl).q l x * b) η = 1 - qR l * Y := by
    rw [hY]; show lin2 (1 - qR l * a) (1 - qR l * b) η = 1 - qR l * lin2 a b η
    unfold lin2; ring
  rw [hr] at hq
  have hq0 := qR_pos hl0
  have hq1 := qR_lt_one hl0
  have hYP : Y ≤ upR l x := by rw [hY]; unfold lin2; nlinarith
  have hY0 : 0 ≤ Y := by rw [hY]; unfold lin2; nlinarith
  have hp1 : pR l x < 1 := by unfold pR; nlinarith
  have hp0 : 0 < pR l x := by unfold pR; positivity
  have hP1 : upR l x ≤ 1 := by
    unfold upR
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hr0 : 0 ≤ 1 - qR l * Y := by nlinarith
  have hch := srcV_chord fl.low hl0 hx0 ha0 hab h0 h1 hcut
  have hsrc := srcV_le_src fl.low (Y := Y) hl0 hx0 hx1
  rw [srcR_eq, srcR_eq, ha, hb] at hq
  rw [← hY] at hch
  have hC : 0 ≤ (ctxR sd fl).C l x * (1 - qR l * Y) :=
    mul_nonneg (mul_nonneg (by show (0 : ℝ) ≤ 1 / (l + 1); positivity) hγ) hr0
  exact hq.trans (payE_mono_g hC (hch.trans hsrc))

end Erdos993Lean.Analytic.O2.Cert
