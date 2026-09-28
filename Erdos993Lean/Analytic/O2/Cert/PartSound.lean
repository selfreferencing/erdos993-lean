import Mathlib
import Erdos993Lean.Analytic.O2.Cert.LowerSound
import Erdos993Lean.Analytic.O2.Cert.QuadSound

/-!
# O2 certificate checker (lane A18): de Casteljau subdivision and the part check

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The part check (`partcheck`) tests the three Bernstein
controls of a response quadratic, subdividing at `1/2` (de Casteljau, `splitP`, real mirror `splitR`) up to three
levels.  A passing part check makes the Bernstein combination `bq` nonnegative at every point of the box, every
piece coordinate `η ∈ [0, 1]` and every response in the part's range (**`partcheck_sound`**).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## de Casteljau subdivision (real mirror) and the part check -/

/-- The midpoint of two real controls. -/
noncomputable def halfR (a b : TriR) : TriR :=
  ⟨fun l x => (a.A l x + b.A l x) / 2, fun l x => (a.B l x + b.B l x) / 2, fun l x => (a.E l x + b.E l x) / 2⟩

/-- de Casteljau at `1/2` (mirror of `splitP`). -/
noncomputable def splitR (poly : List TriR) : List TriR × List TriR :=
  match poly with
  | [c0, c1, c2] =>
    ([c0, halfR c0 c1, halfR (halfR c0 c1) (halfR c1 c2)], [halfR (halfR c0 c1) (halfR c1 c2), halfR c1 c2, c2])
  | _ => (poly, poly)

/-- The controls after a subdivision path (mirror of `subP`). -/
noncomputable def subR (poly : List TriR) : List Bool → List TriR
  | [] => poly
  | d :: ds => subR (if d then (splitR poly).2 else (splitR poly).1) ds

section Split

variable {L X : Ival}

theorem te_halfT {a b : TriR} {a' b' : Tri} (ha : TE L X a a') (hb : TE L X b b') : TE L X (halfR a b) (halfT a' b') :=
  ⟨de_divI (de_add ha.1 hb.1) mem_twoI, de_divI (de_add ha.2.1 hb.2.1) mem_twoI,
    de_divI (de_add ha.2.2 hb.2.2) mem_twoI⟩

theorem te_splitP {P : List TriR} {Q : List Tri} (h : List.Forall₂ (TE L X) P Q) :
    List.Forall₂ (TE L X) (splitR P).1 (splitP Q).1 ∧ List.Forall₂ (TE L X) (splitR P).2 (splitP Q).2 := by
  rcases h with _ | ⟨h0, h⟩
  · exact ⟨List.Forall₂.nil, List.Forall₂.nil⟩
  · rcases h with _ | ⟨h1, h⟩
    · simp only [splitR, splitP]; exact ⟨List.Forall₂.cons h0 List.Forall₂.nil, List.Forall₂.cons h0 List.Forall₂.nil⟩
    · rcases h with _ | ⟨h2, h⟩
      · simp only [splitR, splitP]
        exact ⟨List.Forall₂.cons h0 (List.Forall₂.cons h1 List.Forall₂.nil),
          List.Forall₂.cons h0 (List.Forall₂.cons h1 List.Forall₂.nil)⟩
      · rcases h with _ | ⟨h3, h⟩
        · simp only [splitR, splitP]
          have hab := te_halfT h0 h1; have hbc := te_halfT h1 h2; have hm := te_halfT hab hbc
          exact ⟨List.Forall₂.cons h0 (List.Forall₂.cons hab (List.Forall₂.cons hm List.Forall₂.nil)),
            List.Forall₂.cons hm (List.Forall₂.cons hbc (List.Forall₂.cons h2 List.Forall₂.nil))⟩
        · simp only [splitR, splitP]
          exact ⟨List.Forall₂.cons h0 (List.Forall₂.cons h1 (List.Forall₂.cons h2 (List.Forall₂.cons h3 h))),
            List.Forall₂.cons h0 (List.Forall₂.cons h1 (List.Forall₂.cons h2 (List.Forall₂.cons h3 h)))⟩

theorem te_subP : ∀ (path : List Bool) {P : List TriR} {Q : List Tri}, List.Forall₂ (TE L X) P Q →
    List.Forall₂ (TE L X) (subR P path) (subP Q path)
  | [], _, _, h => h
  | d :: ds, P, Q, h => by
    simp only [subR, subP]
    have hs := te_splitP h
    cases d
    · exact te_subP ds hs.1
    · exact te_subP ds hs.2

end Split

/-- The response quadratic of the Bernstein combination of three controls at `(λ, x)`. -/
noncomputable def bq (P : List TriR) (l x η ζ : ℝ) : ℝ :=
  let c := fun j => P.getD j ⟨0, 0, 0⟩
  bev3 ((c 0).A l x) ((c 1).A l x) ((c 2).A l x) η * ζ ^ 2 +
    bev3 ((c 0).B l x) ((c 1).B l x) ((c 2).B l x) η * ζ + bev3 ((c 0).E l x) ((c 1).E l x) ((c 2).E l x) η

theorem bq_nonneg_of_controls (P : List TriR) (l x ζ : ℝ)
    (h : ∀ j < 3, 0 ≤ (P.getD j ⟨0, 0, 0⟩).A l x * ζ ^ 2 + (P.getD j ⟨0, 0, 0⟩).B l x * ζ + (P.getD j ⟨0, 0, 0⟩).E l x)
    {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) : 0 ≤ bq P l x η ζ := by
  have e : bq P l x η ζ =
      (1 - η) ^ 2 * ((P.getD 0 ⟨0, 0, 0⟩).A l x * ζ ^ 2 + (P.getD 0 ⟨0, 0, 0⟩).B l x * ζ + (P.getD 0 ⟨0, 0, 0⟩).E l x) +
      (2 * η * (1 - η)) * ((P.getD 1 ⟨0, 0, 0⟩).A l x * ζ ^ 2 + (P.getD 1 ⟨0, 0, 0⟩).B l x * ζ +
        (P.getD 1 ⟨0, 0, 0⟩).E l x) +
      η ^ 2 * ((P.getD 2 ⟨0, 0, 0⟩).A l x * ζ ^ 2 + (P.getD 2 ⟨0, 0, 0⟩).B l x * ζ + (P.getD 2 ⟨0, 0, 0⟩).E l x) := by
    unfold bq bev3; ring
  rw [e]
  have := h 0 (by norm_num); have := h 1 (by norm_num); have := h 2 (by norm_num)
  have hw : 0 ≤ 2 * η * (1 - η) := by nlinarith
  positivity

theorem bq_split_left (P : List TriR) (hP : P.length = 3) (l x η ζ : ℝ) :
    bq P l x η ζ = bq (splitR P).1 l x (2 * η) ζ := by
  match P, hP with
  | [c0, c1, c2], _ => simp only [bq, splitR, halfR, List.getD_cons_zero, List.getD_cons_succ, bev3]; ring

theorem bq_split_right (P : List TriR) (hP : P.length = 3) (l x η ζ : ℝ) :
    bq P l x η ζ = bq (splitR P).2 l x (2 * η - 1) ζ := by
  match P, hP with
  | [c0, c1, c2], _ => simp only [bq, splitR, halfR, List.getD_cons_zero, List.getD_cons_succ, bev3]; ring

theorem splitR_length (P : List TriR) (hP : P.length = 3) : (splitR P).1.length = 3 ∧ (splitR P).2.length = 3 := by
  match P, hP with
  | [c0, c1, c2], _ => simp [splitR]

theorem subR_length (P : List TriR) (hP : P.length = 3) : ∀ path, (subR P path).length = 3 := by
  intro path
  induction path generalizing P with
  | nil => exact hP
  | cons d ds ih =>
    simp only [subR]
    cases d
    · exact ih _ (splitR_length P hP).1
    · exact ih _ (splitR_length P hP).2

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem subR_append (P : List TriR) (path : List Bool) (d : Bool) :
    subR P (path ++ [d]) = if d then (splitR (subR P path)).2 else (splitR (subR P path)).1 := by
  induction path generalizing P with
  | nil => simp [subR]
  | cons e es ih => simp only [List.cons_append, subR]; exact ih _

theorem subP_append (P : List Tri) (path : List Bool) (d : Bool) :
    subP P (path ++ [d]) = if d then (splitP (subP P path)).2 else (splitP (subP P path)).1 := by
  induction path generalizing P with
  | nil => simp [subP]
  | cons e es ih => simp only [List.cons_append, subP]; exact ih _

theorem te_getD {L X : Ival} {P : List TriR} {Q : List Tri} (h : List.Forall₂ (TE L X) P Q) (j : ℕ) :
    TE L X (P.getD j ⟨0, 0, 0⟩) (Q.getD j ⟨zeroDN, zeroDN, zeroDN⟩) := by
  induction h generalizing j with
  | nil => simp only [List.getD_nil]; exact ⟨de_zero, de_zero, de_zero⟩
  | cons ha _ ih => cases j with
    | zero => simpa using ha
    | succ j => simpa using ih j

/-- The box facts shared by the soundness lemmas. -/
structure BoxOK (bx : BoxCtx) : Prop where
  hL : bx.lamI.lo ≤ bx.lamI.hi
  hX : bx.xI.lo ≤ bx.xI.hi
  hrL : bx.radL = (bx.lamI.hi - bx.lamI.lo + 1) / 2
  hrX : bx.radX = (bx.xI.hi - bx.xI.lo + 1) / 2

theorem allQuad_sound (bx : BoxCtx) (hb : BoxOK bx) (part : ℕ) (anch : List Bool → ℕ → ℕ → Tri)
    (path : List Bool) (RL : List TriR) (Q : List Tri) (hT : List.Forall₂ (TE bx.lamI bx.xI) RL Q) :
    ∀ (j0 : ℕ), (∀ j code, TE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3)))
        (RL.getD j ⟨0, 0, 0⟩) (anch path (j0 + j) code)) →
      allQuad bx anch path part Q j0 = true →
      ∀ j < Q.length, ∀ l x, bx.lamI.Mem l → bx.xI.Mem x → ∀ ζ, (if part = 1 then 0 ≤ ζ ∧ ζ ≤ 1 else 0 ≤ ζ) →
        0 ≤ (RL.getD j ⟨0, 0, 0⟩).A l x * ζ ^ 2 + (RL.getD j ⟨0, 0, 0⟩).B l x * ζ + (RL.getD j ⟨0, 0, 0⟩).E l x := by
  induction hT with
  | nil => intro j0 _ _ j hj; simp at hj
  | @cons r t rs ts hrt hrest ih =>
    intro j0 hanc hq j hj
    have hq' : quad bx (anch path j0) t part = true ∧ allQuad bx anch path part ts (j0 + 1) = true := by
      simpa only [allQuad, Bool.and_eq_true] using hq
    cases j with
    | zero =>
      intro l x hl hx ζ hζ
      have hanc0 : ∀ code, TE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3))) r
          (anch path j0 code) := fun code => by
        have := hanc 0 code; rw [List.getD_cons_zero, Nat.add_zero] at this; exact this
      rw [List.getD_cons_zero]
      exact quad_sound bx hb.hL hb.hX hb.hrL hb.hrX hrt (anch path j0) hanc0 part hq'.1 hl hx hζ
    | succ j =>
      have hanc' : ∀ j' code, TE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3)))
          (rs.getD j' ⟨0, 0, 0⟩) (anch path (j0 + 1 + j') code) := fun j' code => by
        have := hanc (j' + 1) code
        rw [List.getD_cons_succ, show j0 + (j' + 1) = j0 + 1 + j' by ring] at this; exact this
      have hj' : j < ts.length := by simp only [List.length_cons] at hj; omega
      rw [List.getD_cons_succ]
      exact ih (j0 + 1) hanc' hq'.2 j hj'

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- **Soundness of the part check**: the Bernstein combination of the piece's controls is a nonnegative response
quadratic at every point of the box and every piece coordinate `η ∈ [0, 1]`. -/
theorem partcheck_sound (bx : BoxCtx) (hb : BoxOK bx) (part : ℕ) (anch : List Bool → ℕ → ℕ → Tri)
    (R0 : List TriR) (hR0 : R0.length = 3) (P0 : List Tri)
    (hanc : ∀ path j code, TE (pt (anchorPt bx.lamI (code / 3))) (pt (anchorPt bx.xI (code % 3)))
      ((subR R0 path).getD j ⟨0, 0, 0⟩) (anch path j code)) :
    ∀ (lvl : ℕ) (path : List Bool), List.Forall₂ (TE bx.lamI bx.xI) (subR R0 path) (subP P0 path) →
      partcheck bx anch part lvl path (subP P0 path) = true →
      ∀ l x, bx.lamI.Mem l → bx.xI.Mem x → ∀ η, 0 ≤ η → η ≤ 1 → ∀ ζ,
        (if part = 1 then 0 ≤ ζ ∧ ζ ≤ 1 else 0 ≤ ζ) → 0 ≤ bq (subR R0 path) l x η ζ := by
  have hlen : ∀ path, (subR R0 path).length = 3 := subR_length R0 hR0
  have hall : ∀ path, List.Forall₂ (TE bx.lamI bx.xI) (subR R0 path) (subP P0 path) →
      allQuad bx anch path part (subP P0 path) 0 = true →
      ∀ l x, bx.lamI.Mem l → bx.xI.Mem x → ∀ η, 0 ≤ η → η ≤ 1 → ∀ ζ,
        (if part = 1 then 0 ≤ ζ ∧ ζ ≤ 1 else 0 ≤ ζ) → 0 ≤ bq (subR R0 path) l x η ζ := by
    intro path hT hq l x hl hx η h0 h1 ζ hζ
    have hQ : (subP P0 path).length = 3 := by rw [← hT.length_eq, hlen]
    refine bq_nonneg_of_controls _ l x ζ (fun j hj => ?_) h0 h1
    exact allQuad_sound bx hb part anch path _ _ hT 0 (fun j code => by simpa using hanc path j code) hq j
      (by rw [hQ]; exact hj) l x hl hx ζ hζ
  intro lvl
  induction lvl with
  | zero => intro path hT hq; exact hall path hT (by simpa [partcheck] using hq)
  | succ lvl ih =>
    intro path hT hq l x hl hx η h0 h1 ζ hζ
    simp only [partcheck, Bool.or_eq_true, Bool.and_eq_true] at hq
    rcases hq with hq | ⟨⟨⟨-, -⟩, hleft⟩, hright⟩
    · exact hall path hT hq l x hl hx η h0 h1 ζ hζ
    · have hs := te_splitP hT
      rcases le_total η (1 / 2) with hη | hη
      · rw [bq_split_left _ (hlen path)]
        have hT' : List.Forall₂ (TE bx.lamI bx.xI) (subR R0 (path ++ [false])) (subP P0 (path ++ [false])) := by
          rw [subR_append, subP_append]; simpa using hs.1
        have hq' : partcheck bx anch part lvl (path ++ [false]) (subP P0 (path ++ [false])) = true := by
          rw [subP_append]; simpa using hleft
        have := ih (path ++ [false]) hT' hq' l x hl hx (2 * η) (by linarith) (by linarith) ζ hζ
        rw [subR_append] at this; simpa using this
      · rw [bq_split_right _ (hlen path)]
        have hT' : List.Forall₂ (TE bx.lamI bx.xI) (subR R0 (path ++ [true])) (subP P0 (path ++ [true])) := by
          rw [subR_append, subP_append]; simpa using hs.2
        have hq' : partcheck bx anch part lvl (path ++ [true]) (subP P0 (path ++ [true])) = true := by
          rw [subP_append]; simpa using hright
        have := ih (path ++ [true]) hT' hq' l x hl hx (2 * η - 1) (by linarith) (by linarith) ζ hζ
        rw [subR_append] at this; simpa using this

end Erdos993Lean.Analytic.O2.Cert
