import Mathlib
import Erdos993Lean.Analytic.O2.Cert.BernSound

/-!
# O2 certificate checker (lane A18): the piece lists

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The pieces of a parent case are the consecutive pairs
of a sorted list of `Y` values (the ends of the parent case's range and the source cuts it may meet, inserted by
`insertL` with clipping).  Here: the real-value insertion keeps the list sorted, keeps its ends and contains every
inserted cut (`Good`, `good_insertCuts`); every `Y` between the ends lies in a piece with no list value strictly
inside (**`piece_exists`**); the checker's lists enclose the real lists (`listsR`, **`lists_enc`**) whose values at a
point are the real-value insertion (`ev_insertCuts`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

/-! ## Sorted insertion of cuts (real values) -/

/-- `max(lᵢ₋₁, min(lᵢ, c))` over consecutive pairs. -/
noncomputable def insMidV (c : ℝ) : List ℝ → List ℝ
  | a :: b :: rest => max a (min b c) :: insMidV c (b :: rest)
  | _ => []

/-- The last element (or `0`). -/
noncomputable def lastV : List ℝ → ℝ
  | [] => 0
  | [a] => a
  | _ :: b :: rest => lastV (b :: rest)

/-- Insertion into a sorted list. -/
noncomputable def insertV (Ls : List ℝ) (c : ℝ) : List ℝ :=
  match Ls with
  | [] => []
  | l0 :: _ => l0 :: (insMidV c Ls ++ [lastV Ls])

theorem insMidV_chain (c : ℝ) : ∀ (a : ℝ) (rest : List ℝ), List.IsChain (· ≤ ·) (a :: rest) →
    List.IsChain (· ≤ ·) (a :: (insMidV c (a :: rest) ++ [lastV (a :: rest)]))
  | a, [], _ => by
    simp only [insMidV, lastV, List.nil_append]
    exact List.IsChain.cons_cons le_rfl (List.isChain_singleton a)
  | a, b :: rest, h => by
    have hab : a ≤ b := (List.isChain_cons_cons.mp h).1
    have hrest : List.IsChain (· ≤ ·) (b :: rest) := (List.isChain_cons_cons.mp h).2
    have ih := insMidV_chain c b rest hrest
    simp only [insMidV, lastV, List.cons_append]
    refine List.IsChain.cons_cons (le_max_left _ _) ?_
    -- the tail: max a (min b c) :: (insMidV c (b :: rest) ++ [lastV (b :: rest)])
    rcases rest with _ | ⟨d, rest⟩
    · simp only [insMidV, lastV, List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact max_le hab (min_le_left _ _)
    · simp only [insMidV, List.cons_append] at ih ⊢
      refine List.IsChain.cons_cons ?_ (List.isChain_cons_cons.mp ih).2
      have hbd : b ≤ d := (List.isChain_cons_cons.mp hrest).1
      exact max_le_max hab (min_le_min_right _ hbd)

theorem insertV_chain {Ls : List ℝ} (h : List.IsChain (· ≤ ·) Ls) (c : ℝ) : List.IsChain (· ≤ ·) (insertV Ls c) := by
  rcases Ls with _ | ⟨a, rest⟩
  · exact List.isChain_nil
  · exact insMidV_chain c a rest h

theorem lastV_mem : ∀ {Ls : List ℝ}, Ls ≠ [] → lastV Ls ∈ Ls
  | [], h => absurd rfl h
  | [a], _ => by simp [lastV]
  | a :: b :: rest, _ => by
    simp only [lastV]
    exact List.mem_cons_of_mem _ (lastV_mem (List.cons_ne_nil _ _))

theorem lastV_append (Ls : List ℝ) (y : ℝ) : lastV (Ls ++ [y]) = y := by
  induction Ls with
  | nil => simp [lastV]
  | cons a rest ih =>
    rcases rest with _ | ⟨b, rest⟩
    · simp [lastV]
    · simp only [List.cons_append] at ih ⊢; simpa [lastV] using ih

theorem insertV_last (Ls : List ℝ) (c : ℝ) (h : Ls ≠ []) : lastV (insertV Ls c) = lastV Ls := by
  rcases Ls with _ | ⟨a, rest⟩
  · exact absurd rfl h
  · simp only [insertV]
    rw [show a :: (insMidV c (a :: rest) ++ [lastV (a :: rest)]) = (a :: insMidV c (a :: rest)) ++
      [lastV (a :: rest)] by simp, lastV_append]

/-- In a chain `l₀ ≤ l₁ ≤ …`, every element is at most the last. -/
theorem le_lastV_of_chain : ∀ {Ls : List ℝ}, List.IsChain (· ≤ ·) Ls → ∀ y ∈ Ls, y ≤ lastV Ls
  | [], _, y, hy => absurd hy (List.not_mem_nil)
  | [a], _, y, hy => by simp at hy; simp [lastV, hy]
  | a :: b :: rest, h, y, hy => by
    simp only [lastV]
    have h2 := (List.isChain_cons_cons.mp h).2
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact (List.isChain_cons_cons.mp h).1.trans (le_lastV_of_chain h2 b (List.mem_cons_self))
    · exact le_lastV_of_chain h2 y hy'

/-- The inserted value appears (when it lies between the ends). -/
theorem mem_insMidV (c : ℝ) : ∀ (a : ℝ) (rest : List ℝ), List.IsChain (· ≤ ·) (a :: rest) → a ≤ c →
    c ≤ lastV (a :: rest) → c ∈ insMidV c (a :: rest) ∨ c = lastV (a :: rest)
  | a, [], _, h1, h2 => Or.inr (le_antisymm (by simpa [lastV] using h2) h1)
  | a, b :: rest, h, h1, h2 => by
    simp only [insMidV, lastV] at h2 ⊢
    by_cases hcb : c ≤ b
    · left; rw [min_eq_right hcb, max_eq_right h1]; exact List.mem_cons_self
    · have := mem_insMidV c b rest (List.isChain_cons_cons.mp h).2 (not_le.mp hcb).le h2
      rcases this with h3 | h3
      · left; exact List.mem_cons_of_mem _ h3
      · right; exact h3

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

theorem mem_insMidV_of_mem (c : ℝ) : ∀ (a : ℝ) (rest : List ℝ), List.IsChain (· ≤ ·) (a :: rest) →
    ∀ y ∈ rest, y ∈ insMidV c (a :: rest) ∨ y = lastV (a :: rest)
  | a, [], _, y, hy => absurd hy List.not_mem_nil
  | a, b :: rest, h, y, hy => by
    simp only [insMidV, lastV]
    have hab := (List.isChain_cons_cons.mp h).1
    have h2 := (List.isChain_cons_cons.mp h).2
    rcases List.mem_cons.mp hy with rfl | hy'
    · -- y = b
      by_cases hcb : y ≤ c
      · left; rw [min_eq_left hcb, max_eq_right hab]; exact List.mem_cons_self
      · rcases rest with _ | ⟨d, rest⟩
        · right; simp [lastV]
        · left; apply List.mem_cons_of_mem
          simp only [insMidV]
          have hbd := (List.isChain_cons_cons.mp h2).1
          rw [max_eq_left (min_le_of_right_le (not_le.mp hcb).le)]
          exact List.mem_cons_self
    · rcases mem_insMidV_of_mem c b rest h2 y hy' with h3 | h3
      · left; exact List.mem_cons_of_mem _ h3
      · right; exact h3

theorem mem_insertV_of_mem {Ls : List ℝ} (h : List.IsChain (· ≤ ·) Ls) (c : ℝ) {y : ℝ} (hy : y ∈ Ls) :
    y ∈ insertV Ls c := by
  rcases Ls with _ | ⟨a, rest⟩
  · exact absurd hy List.not_mem_nil
  · simp only [insertV]
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact List.mem_cons_self
    · rcases mem_insMidV_of_mem c a rest h y hy' with h3 | h3
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h3)
      · rw [h3]; exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

/-- The real-value mirror of `insertCuts`. -/
noncomputable def insertCutsV (a b : ℝ) (used : List ℕ) : List ℝ → ℕ → List ℝ → List ℝ
  | [], _, Ls => Ls
  | z :: zs, ci, Ls =>
    insertCutsV a b used zs (ci + 1) (if used.contains ci then insertV Ls (max a (min b z)) else Ls)

theorem insertV_head (Ls : List ℝ) (c : ℝ) : (insertV Ls c).head? = Ls.head? := by
  rcases Ls with _ | ⟨a, rest⟩ <;> simp [insertV]

theorem insertV_length_ge (Ls : List ℝ) (c : ℝ) : Ls.length ≤ (insertV Ls c).length := by
  rcases Ls with _ | ⟨a, rest⟩
  · simp [insertV]
  · simp only [insertV, List.length_cons, List.length_append, List.length_singleton]
    have : ∀ (a : ℝ) (rest : List ℝ), (insMidV c (a :: rest)).length = rest.length := by
      intro a rest
      induction rest generalizing a with
      | nil => simp [insMidV]
      | cons b rest ih => simp [insMidV, ih]
    rw [this]; omega

/-- A sorted list from `a` to `b` (at least two entries) containing the listed values. -/
structure Good (F : List ℝ) (a b : ℝ) (S : List ℝ) : Prop where
  chain : List.IsChain (· ≤ ·) F
  head : F.head? = some a
  last : lastV F = b
  len : 2 ≤ F.length
  mem : ∀ s ∈ S, s ∈ F

theorem good_insert {F : List ℝ} {a b : ℝ} {S : List ℝ} (h : Good F a b S) (hab : a ≤ b) (z : ℝ) :
    Good (insertV F (max a (min b z))) a b (max a (min b z) :: S) := by
  have hne : F ≠ [] := by intro h'; have := h.len; rw [h'] at this; simp at this
  set c := max a (min b z)
  have hac : a ≤ c := le_max_left _ _
  have hcb : c ≤ b := max_le hab (min_le_left _ _)
  refine ⟨insertV_chain h.chain c, by rw [insertV_head, h.head], by rw [insertV_last _ _ hne, h.last],
    (h.len.trans (insertV_length_ge F c)), fun s hs => ?_⟩
  rcases List.mem_cons.mp hs with rfl | hs'
  · rcases F with _ | ⟨f0, rest⟩
    · exact absurd rfl hne
    · have hf0 : f0 = a := by simpa using h.head
      subst hf0
      simp only [insertV]
      rcases mem_insMidV c f0 rest h.chain hac (h.last ▸ hcb) with h3 | h3
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h3)
      · rw [h3]; exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
  · exact mem_insertV_of_mem h.chain c (h.mem s hs')

theorem good_insertCuts (a b : ℝ) (hab : a ≤ b) (used : List ℕ) :
    ∀ (zs : List ℝ) (ci : ℕ) (Ls : List ℝ) (S : List ℝ), Good Ls a b S →
      Good (insertCutsV a b used zs ci Ls) a b S ∧
        ∀ i < zs.length, used.contains (ci + i) = true →
          max a (min b (zs.getD i 0)) ∈ insertCutsV a b used zs ci Ls
  | [], ci, Ls, S, h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | z :: zs, ci, Ls, S, h => by
    by_cases hu : used.contains ci = true
    · have h1 := good_insert h hab z
      obtain ⟨h2, h3⟩ := good_insertCuts a b hab used zs (ci + 1) _ _ h1
      simp only [insertCutsV, hu, if_true]
      refine ⟨⟨h2.chain, h2.head, h2.last, h2.len, fun s hs => h2.mem s (List.mem_cons_of_mem _ hs)⟩,
        fun i hi hui => ?_⟩
      rcases i with _ | i
      · exact h2.mem _ List.mem_cons_self
      · simp only [List.length_cons] at hi
        have := h3 i (by omega) (by rw [show ci + 1 + i = ci + (i + 1) by ring]; exact hui)
        simpa using this
    · obtain ⟨h2, h3⟩ := good_insertCuts a b hab used zs (ci + 1) Ls S h
      simp only [insertCutsV, hu, Bool.false_eq_true, if_false]
      refine ⟨h2, fun i hi hui => ?_⟩
      rcases i with _ | i
      · simp only [Nat.add_zero] at hui; exact absurd hui hu
      · simp only [List.length_cons] at hi
        have := h3 i (by omega) (by rw [show ci + 1 + i = ci + (i + 1) by ring]; exact hui)
        simpa using this

/-- **The pieces cover**: in a sorted list from `a` to `b`, every `Y ∈ [a, b]` lies in a consecutive piece that has
no list element strictly inside. -/
theorem piece_exists : ∀ (F : List ℝ), List.IsChain (· ≤ ·) F → 2 ≤ F.length → ∀ Y, F.headD 0 ≤ Y → Y ≤ lastV F →
    ∃ k, k + 1 < F.length ∧ F.getD k 0 ≤ Y ∧ Y ≤ F.getD (k + 1) 0 ∧
      ∀ s ∈ F, ¬(F.getD k 0 < s ∧ s < F.getD (k + 1) 0)
  | [], _, h, _, _, _ => absurd h (by simp)
  | [_], _, h, _, _, _ => absurd h (by simp)
  | f0 :: f1 :: rest, hc, _, Y, h0, h1 => by
    have h01 := (List.isChain_cons_cons.mp hc).1
    have hc1 := (List.isChain_cons_cons.mp hc).2
    by_cases hY : Y ≤ f1
    · refine ⟨0, by simp, by simpa using h0, by simpa using hY, fun s hs ⟨hs1, hs2⟩ => ?_⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hs1 hs2
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact lt_irrefl _ hs1
      · have := (List.isChain_iff_pairwise.mp hc1)
        rcases List.mem_cons.mp hs' with rfl | hs''
        · exact lt_irrefl _ hs2
        · exact absurd (List.rel_of_pairwise_cons this hs'') (not_le.mpr hs2)
    · rcases rest with _ | ⟨f2, rest⟩
      · simp only [lastV] at h1; exact absurd h1 hY
      · obtain ⟨k, hk, hk1, hk2, hk3⟩ := piece_exists (f1 :: f2 :: rest) hc1 (by simp) Y
          (by simpa using (not_le.mp hY).le) (by simpa [lastV] using h1)
        refine ⟨k + 1, by simp at hk ⊢; omega, by simpa using hk1, by simpa using hk2, fun s hs hs' => ?_⟩
        simp only [List.getD_cons_succ] at hs'
        rcases List.mem_cons.mp hs with rfl | hs''
        · -- s = f0 ≤ f1 ≤ F_k
          have hmono : f1 ≤ (f1 :: f2 :: rest).getD k 0 := by
            have hp := List.isChain_iff_pairwise.mp hc1
            rcases k with _ | k
            · simp
            · simp only [List.getD_cons_succ]
              have hkk : k < (f2 :: rest).length := by simp at hk ⊢; omega
              rw [List.getD_eq_getElem _ _ hkk]
              exact List.rel_of_pairwise_cons hp (List.getElem_mem hkk) |> le_of_eq_of_le rfl
          exact absurd (lt_of_lt_of_le hs'.1 (h01.trans hmono)) (lt_irrefl _) |> fun h => h
        · exact hk3 s hs'' hs'

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The piece lists (real mirror) -/

noncomputable def rinsMid (c : RF) : List RF → List RF
  | a :: b :: rest => (fun l x => max (a l x) (min (b l x) (c l x))) :: rinsMid c (b :: rest)
  | _ => []

noncomputable def rlastD : List RF → RF
  | [] => 0
  | [a] => a
  | _ :: b :: rest => rlastD (b :: rest)

noncomputable def rinsertL (Ls : List RF) (c : RF) : List RF :=
  match Ls with
  | [] => []
  | l0 :: _ => l0 :: (rinsMid c Ls ++ [rlastD Ls])

noncomputable def rclip (a b z : RF) : RF := fun l x => max (a l x) (min (b l x) (z l x))

noncomputable def rinsertCuts (a b : RF) (used : List ℕ) : List RF → ℕ → List RF → List RF
  | [], _, Ls => Ls
  | z :: zs, ci, Ls => rinsertCuts a b used zs (ci + 1) (if used.contains ci then rinsertL Ls (rclip a b z) else Ls)

/-- The real piece lists of a parent case (mirror of `listsOf`). -/
noncomputable def listsR (upper : RF) (cuts : List RF) (lab : ℕ × ℕ) (rec : Recipe) : List (ℕ × List RF) :=
  match rec with
  | .low segs used =>
    segs.zipIdx.map (fun sn =>
      let a : RF := fun l x => min ((sn.1 : ℝ) / 8) (upper l x)
      let b : RF := fun l x => min (((sn.1 + 1 : ℕ) : ℝ) / 8) (upper l x)
      (sn.1, rinsertCuts a b (used.getD sn.2 []) cuts 0 [a, b]))
  | .other used =>
    let high : RF := if lab.1 = 1 then fun l x => min (upper l x) ((lab.2 : ℝ) / 8)
      else fun l x => min (upper l x) (((lab.2 + 1 : ℕ) : ℝ) / 8)
    [(0, rinsertCuts 0 high used cuts 0 [0, high])]

section ListsEnc

variable {L X : Ival}

theorem le_insMid {c : RF} {c' : DN} (hc : DE L X c c') :
    ∀ {Ls : List RF} {Ls' : List DN}, LE L X Ls Ls' → LE L X (rinsMid c Ls) (insMid c' Ls')
  | [], [], _ => by simp [rinsMid, insMid, LE]
  | [_], [_], _ => by simp [rinsMid, insMid, LE]
  | a :: b :: rest, a' :: b' :: rest', List.Forall₂.cons ha (List.Forall₂.cons hb hr) => by
    simp only [rinsMid, insMid]
    exact List.Forall₂.cons (de_mx ha (de_mn hb hc)) (le_insMid hc (List.Forall₂.cons hb hr))

theorem de_lastD : ∀ {Ls : List RF} {Ls' : List DN}, LE L X Ls Ls' → DE L X (rlastD Ls) (lastD Ls')
  | [], [], _ => de_zero
  | [a], [a'], List.Forall₂.cons ha _ => ha
  | a :: b :: rest, a' :: b' :: rest', List.Forall₂.cons _ h => by
    simp only [rlastD, lastD]; exact de_lastD h

theorem le_insertL {Ls : List RF} {Ls' : List DN} (h : LE L X Ls Ls') {c : RF} {c' : DN} (hc : DE L X c c') :
    LE L X (rinsertL Ls c) (insertL Ls' c') := by
  rcases h with _ | ⟨ha, hr⟩
  · exact le_nil
  · simp only [rinsertL, insertL]
    exact List.Forall₂.cons ha (List.rel_append (le_insMid hc (List.Forall₂.cons ha hr))
      (le_single (de_lastD (List.Forall₂.cons ha hr))))

theorem le_insertCuts {a b : RF} {a' b' : DN} (ha : DE L X a a') (hb : DE L X b b') (used : List ℕ) :
    ∀ {cuts : List RF} {cuts' : List DN}, LE L X cuts cuts' → ∀ (ci : ℕ) {Ls : List RF} {Ls' : List DN},
      LE L X Ls Ls' → LE L X (rinsertCuts a b used cuts ci Ls) (insertCuts a' b' used cuts' ci Ls')
  | [], [], _, _, _, _, h => h
  | z :: zs, z' :: zs', List.Forall₂.cons hz hzs, ci, Ls, Ls', h => by
    simp only [rinsertCuts, insertCuts]
    apply le_insertCuts ha hb used hzs
    split_ifs
    · exact le_insertL h (de_mx ha (de_mn hb hz))
    · exact h

end ListsEnc

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The real source cuts of a context. -/
noncomputable def cutsR (low : Bool) (b : ℕ) : List RF := if low then [] else [cutR b 0, cutR b 1, cutR b 2]

theorem le_cuts {L X : Ival} {sd : SegData} {fl : Flags} {c : Ctx} (hc : CtxE L X sd fl c) :
    LE L X (cutsR fl.low c.y0b) c.cuts := by
  obtain ⟨hlen, hde⟩ := hc.cuts
  unfold cutsR
  cases hlow : fl.low
  · simp only [hlow, Bool.false_eq_true, if_false] at hlen ⊢
    obtain ⟨a, b, d, hcuts⟩ := List.length_eq_three.mp hlen
    have h0 := hde 0 (by rw [hcuts]; simp); have h1 := hde 1 (by rw [hcuts]; simp)
    have h2 := hde 2 (by rw [hcuts]; simp)
    rw [hcuts] at h0 h1 h2 ⊢
    exact List.Forall₂.cons h0 (List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil))
  · simp only [hlow, if_true] at hlen ⊢
    rw [List.length_eq_zero_iff] at hlen; rw [hlen]; exact le_nil

theorem lists_enc {L X : Ival} {sd : SegData} {fl : Flags} {c : Ctx} (hc : CtxE L X sd fl c) (lab : ℕ × ℕ)
    (rcp : Recipe) : List.Forall₂ (fun (a : ℕ × List RF) (b : ℕ × List DN) => a.1 = b.1 ∧ LE L X a.2 b.2)
      (listsR upR (cutsR fl.low c.y0b) lab rcp) (listsOf c lab rcp) := by
  have hcuts := le_cuts hc
  cases rcp with
  | low segs used =>
    simp only [listsR, listsOf]
    induction segs.zipIdx with
    | nil => exact List.Forall₂.nil
    | cons sn rest ih =>
      refine List.Forall₂.cons ⟨rfl, ?_⟩ ih
      have ha : DE L X (fun l x => min ((sn.1 : ℝ) / 8) (upR l x)) (portion c sn.1).1 :=
        de_mn (de_cst (mem_knotI _)) hc.upper
      have hb : DE L X (fun l x => min (((sn.1 + 1 : ℕ) : ℝ) / 8) (upR l x)) (portion c sn.1).2 :=
        de_mn (de_cst (mem_knotI _)) hc.upper
      exact le_insertCuts ha hb _ hcuts 0 (le_pair ha hb)
  | other used =>
    simp only [listsR, listsOf]
    refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
    have hh : DE L X (if lab.1 = 1 then fun l x => min (upR l x) ((lab.2 : ℝ) / 8)
        else fun l x => min (upR l x) (((lab.2 + 1 : ℕ) : ℝ) / 8)) (highOf c lab) := by
      unfold highOf; split_ifs
      · exact de_mn hc.upper (de_cst (mem_knotI _))
      · exact de_mn hc.upper (de_cst (mem_knotI _))
    have h0 : DE L X (0 : RF) zeroDN := de_zero
    exact le_insertCuts h0 hh _ hcuts 0 (le_pair h0 hh)

/-! ## Evaluation of the real lists -/

theorem ev_insMid (c : RF) (l x : ℝ) : ∀ Ls : List RF,
    (rinsMid c Ls).map (fun f => f l x) = insMidV (c l x) (Ls.map (fun f => f l x))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have := ev_insMid c l x (b :: rest)
    simp only [rinsMid, List.map_cons, insMidV] at this ⊢
    rw [this]

theorem ev_lastD (l x : ℝ) : ∀ Ls : List RF, rlastD Ls l x = lastV (Ls.map (fun f => f l x))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have := ev_lastD l x (b :: rest)
    simp only [rlastD, List.map_cons, lastV] at this ⊢
    exact this

theorem ev_insertL (Ls : List RF) (c : RF) (l x : ℝ) :
    (rinsertL Ls c).map (fun f => f l x) = insertV (Ls.map (fun f => f l x)) (c l x) := by
  rcases Ls with _ | ⟨a, rest⟩
  · rfl
  · simp only [rinsertL, insertV, List.map_cons, List.map_append, List.map_nil]
    rw [ev_insMid, ev_lastD]
    rfl

theorem ev_insertCuts (a b : RF) (used : List ℕ) (l x : ℝ) : ∀ (cuts : List RF) (ci : ℕ) (Ls : List RF),
    (rinsertCuts a b used cuts ci Ls).map (fun f => f l x) =
      insertCutsV (a l x) (b l x) used (cuts.map (fun f => f l x)) ci (Ls.map (fun f => f l x))
  | [], _, _ => rfl
  | z :: zs, ci, Ls => by
    simp only [rinsertCuts, insertCutsV, List.map_cons]
    rw [ev_insertCuts a b used l x zs (ci + 1)]
    congr 1
    split_ifs
    · rw [ev_insertL]; rfl
    · rfl

end Erdos993Lean.Analytic.O2.Cert
