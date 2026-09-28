import Mathlib
import Erdos993Lean.Analytic.O2.Cert.ContextSound

/-!
# O2 certificate checker (lane A18): the controls of a piece enclose real controls

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The checker (`Compute/Engine.lean`, `triples`) forms on a
piece `[ya, yb]` of a parent case the three response quadratics of the payment (`PRO_R2_PROOF.md` (13)) as
lists of degree `≤ 2` in the piece coordinate (`belev`, `badd`, `bmul`) and their Bernstein controls (`controls`).
Here each list operation has a real mirror on real functions of `(λ, x)` (`relev`, `radd`, `rmul`, ...,
`triplesR`), and the checker's lists enclose the mirrors (`LE`, `le_radd`, `le_rmul`, ...,
**`triples_enc`**): the real context `ctxR` (the functions named in `CtxE`), the retained-source lower bound
`srcR` (mirror of `source`), the parent fields on one segment (`segR`, `clampR`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## Bernstein lists of real functions (mirroring the dual-number lists) -/

/-- A real function of the box coordinates `(λ, x)`. -/
abbrev RF := ℝ → ℝ → ℝ

/-- The real number `1/2` as the checker encloses it. -/
noncomputable def rhalf : ℝ := ((1 / 2 : ℚ) : ℝ)

theorem rhalf_eq : rhalf = 1 / 2 := by unfold rhalf; push_cast; ring

/-- Degree elevation (mirror of `belev`). -/
noncomputable def relev (c : List RF) (n : ℕ) : List RF :=
  match c with
  | [a] => if n = 0 then [a] else if n = 1 then [a, a] else [a, fun l x => a l x * rhalf + a l x * rhalf, a]
  | [a, b] => if n ≤ 1 then [a, b] else [a, fun l x => a l x * rhalf + b l x * rhalf, b]
  | l => l

/-- Sum (mirror of `badd`). -/
noncomputable def radd (a b : List RF) : List RF :=
  List.zipWith (fun f g l x => f l x + g l x) (relev a (max a.length b.length - 1))
    (relev b (max a.length b.length - 1))

/-- Negation. -/
def rneg (a : List RF) : List RF := a.map (fun f l x => -f l x)

/-- Difference. -/
noncomputable def rsub (a b : List RF) : List RF := radd a (rneg b)

/-- Product (mirror of `bmul`). -/
noncomputable def rmul (a b : List RF) : List RF :=
  match a, b with
  | a, [b0] => a.map (fun v l x => v l x * b0 l x)
  | [a0], b => b.map (fun v l x => a0 l x * v l x)
  | [a0, a1], [b0, b1] => [fun l x => a0 l x * b0 l x, fun l x => (a0 l x * b1 l x + a1 l x * b0 l x) / 2,
      fun l x => a1 l x * b1 l x]
  | _, _ => []

/-- Two lists enclose elementwise on the box. -/
def LE (L X : Ival) (fs : List RF) (ds : List DN) : Prop := List.Forall₂ (fun f d => DE L X f d) fs ds

section LE

variable {L X : Ival}

theorem le_nil : LE L X [] [] := List.Forall₂.nil

theorem le_single {f : RF} {d : DN} (h : DE L X f d) : LE L X [f] [d] := List.Forall₂.cons h List.Forall₂.nil

theorem le_pair {f g : RF} {d e : DN} (h1 : DE L X f d) (h2 : DE L X g e) : LE L X [f, g] [d, e] :=
  List.Forall₂.cons h1 (le_single h2)

theorem LE.length_eq {fs : List RF} {ds : List DN} (h : LE L X fs ds) : fs.length = ds.length :=
  List.Forall₂.length_eq h

theorem de_half {f : RF} {a : DN} (h : DE L X f a) : DE L X (fun l x => f l x * rhalf) (dmulI a halfI) :=
  de_mulI h (mem_ofRat _)

theorem le_relev {fs : List RF} {ds : List DN} (h : LE L X fs ds) (n : ℕ) :
    LE L X (relev fs n) (belev ds n) := by
  rcases h with _ | ⟨ha, h⟩
  · exact le_nil
  · rename_i f d fs ds
    rcases h with _ | ⟨hb, h⟩
    · simp only [relev, belev]
      split_ifs
      · exact le_single ha
      · exact le_pair ha ha
      · exact List.Forall₂.cons ha (le_pair (de_add (de_half ha) (de_half ha)) ha)
    · rename_i g e gs es
      rcases h with _ | ⟨hc, h⟩
      · simp only [relev, belev]
        split_ifs
        · exact le_pair ha hb
        · exact List.Forall₂.cons ha (le_pair (de_add (de_half ha) (de_half hb)) hb)
      · exact List.Forall₂.cons ha (List.Forall₂.cons hb (List.Forall₂.cons hc h))

theorem le_zipWith {fs gs : List RF} {ds es : List DN} (h1 : LE L X fs ds) (h2 : LE L X gs es) :
    LE L X (List.zipWith (fun f g l x => f l x + g l x) fs gs) (List.zipWith dadd ds es) := by
  induction h1 generalizing gs es with
  | nil => simp [LE]
  | cons ha _ ih =>
    rcases h2 with _ | ⟨hb, h2⟩
    · simp [LE]
    · exact List.Forall₂.cons (de_add ha hb) (ih h2)

theorem le_radd {fs gs : List RF} {ds es : List DN} (h1 : LE L X fs ds) (h2 : LE L X gs es) :
    LE L X (radd fs gs) (badd ds es) := by
  unfold radd badd
  rw [h1.length_eq, h2.length_eq]
  exact le_zipWith (le_relev h1 _) (le_relev h2 _)

theorem le_rneg {fs : List RF} {ds : List DN} (h : LE L X fs ds) : LE L X (rneg fs) (bneg ds) := by
  unfold rneg bneg
  induction h with
  | nil => exact le_nil
  | cons ha _ ih => exact List.Forall₂.cons (de_neg ha) ih

theorem le_rsub {fs gs : List RF} {ds es : List DN} (h1 : LE L X fs ds) (h2 : LE L X gs es) :
    LE L X (rsub fs gs) (bsub ds es) := le_radd h1 (le_rneg h2)

theorem le_map_mul_right {fs : List RF} {ds : List DN} {g : RF} {e : DN} (h : LE L X fs ds) (hg : DE L X g e) :
    LE L X (fs.map (fun v l x => v l x * g l x)) (ds.map (fun v => dmul v e)) := by
  induction h with
  | nil => exact le_nil
  | cons ha _ ih => exact List.Forall₂.cons (de_mul ha hg) ih

theorem le_map_mul_left {fs : List RF} {ds : List DN} {g : RF} {e : DN} (h : LE L X fs ds) (hg : DE L X g e) :
    LE L X (fs.map (fun v l x => g l x * v l x)) (ds.map (fun v => dmul e v)) := by
  induction h with
  | nil => exact le_nil
  | cons ha _ ih => exact List.Forall₂.cons (de_mul hg ha) ih

theorem le_rmul {fs gs : List RF} {ds es : List DN} (h1 : LE L X fs ds) (h2 : LE L X gs es) :
    LE L X (rmul fs gs) (bmul ds es) := by
  rcases h2 with _ | ⟨hb0, h2⟩
  · -- b = []
    rcases h1 with _ | ⟨ha0, h1⟩
    · simp [rmul, bmul, LE]
    · rename_i f d fs' ds'
      rcases h1 with _ | ⟨ha1, h1⟩
      · simp [rmul, bmul, LE]
      · rename_i f' d' fs'' ds''
        rcases h1 with _ | ⟨_, _⟩ <;> simp [rmul, bmul, LE]
  · rename_i g e gs es
    rcases h2 with _ | ⟨hb1, h2⟩
    · -- b = [b0]
      simp only [rmul, bmul]
      exact le_map_mul_right (h1) hb0
    · rename_i g' e' gs' es'
      rcases h1 with _ | ⟨ha0, h1⟩
      · simp [rmul, bmul, LE]
      · rename_i f d fs' ds'
        rcases h1 with _ | ⟨ha1, h1⟩
        · -- a = [a0], b of length ≥ 2
          simp only [rmul, bmul]
          exact le_map_mul_left (List.Forall₂.cons hb0 (List.Forall₂.cons hb1 h2)) ha0
        · rename_i f' d' fs'' ds''
          rcases h1 with _ | ⟨_, h1⟩
          · rcases h2 with _ | ⟨_, _⟩
            · simp only [rmul, bmul]
              exact List.Forall₂.cons (de_mul ha0 hb0)
                (le_pair (de_divI (de_add (de_mul ha0 hb1) (de_mul ha1 hb0)) mem_twoI) (de_mul ha1 hb1))
            · simp [rmul, bmul, LE]
          · rcases h2 with _ | ⟨_, _⟩ <;> simp [rmul, bmul, LE]

end LE

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The real mirror of a piece -/

/-- The real functions of a context (from `CtxE`). -/
structure CR where
  lam : RF
  x : RF
  q : RF
  p : RF
  upper : RF
  hp : RF
  G : RF
  tau : RF
  au : RF
  av : RF
  so : RF
  phi : RF
  hn : RF
  u : ℕ → RF
  v : ℕ → RF
  s : ℕ → RF
  t : ℕ → RF
  w : RF
  ell : RF
  C : RF

/-- A real control `(A, B, E)`. -/
structure TriR where
  A : RF
  B : RF
  E : RF

/-- A control encloses. -/
def TE (L X : Ival) (t : TriR) (d : Tri) : Prop := DE L X t.A d.A ∧ DE L X t.B d.B ∧ DE L X t.E d.E

/-- `f(a) = max(αa, a − β(1 − a))`, `α = 1 − 1/((λ+1)·2)`, `β = 1/(λ·2)` (mirror of `fnorm`). -/
noncomputable def fnR (l a : ℝ) : ℝ := max ((1 - 1 / ((l + 1) * 2)) * a) (a - 1 / (l * 2) * (1 - a))

/-- The retained-source lower bound at `Y` (mirror of `source`). -/
noncomputable def srcR (cr : CR) (low : Bool) (Y : RF) : RF := fun l x =>
  if low then cr.x l x * (1 - cr.q l x * Y l x) * (1 - 1 / ((cr.lam l x + 1) * 2))
  else (fnR (cr.lam l x) (cr.x l x * (1 - cr.q l x * Y l x)) + 1 -
    fnR (cr.lam l x) (max (Y l x) ((1 - cr.p l x * (1 - cr.q l x * Y l x)) * cr.hn l x))) / 2

/-- `clamp(Y, s/8, (s+1)/8)`. -/
noncomputable def clampR (Y : RF) (s : ℕ) : RF := fun l x => max ((s : ℝ) / 8) (min (((s + 1 : ℕ) : ℝ) / 8) (Y l x))

/-- The segment formula (mirror of `interpSeg`). -/
noncomputable def segR (f : ℕ → RF) (X : RF) (j : ℕ) : RF := fun l x =>
  f j l x + (f (j + 1) l x - f j l x) * (X l x * 8 - j)

/-- The parent field list (mirror of `par` in `triples`). -/
noncomputable def parR (cr : CR) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) (f : ℕ → RF) : List RF :=
  if lab.1 = 1 then [f lab.2]
  else if lab.1 = 2 then [segR f (clampR cr.upper lab.2) lab.2]
  else [segR f (clampR ya s) s, segR f (clampR yb s) s]

/-- The three controls of a triple of lists (mirror of `controls`). -/
noncomputable def rcontrols (A B E : List RF) : List TriR :=
  let a := relev A 2
  let b := relev B 2
  let e := relev E 2
  [⟨a.getD 0 0, b.getD 0 0, e.getD 0 0⟩, ⟨a.getD 1 0, b.getD 1 0, e.getD 1 0⟩, ⟨a.getD 2 0, b.getD 2 0, e.getD 2 0⟩]

/-- **The real controls of a piece** (mirror of `triples`). -/
noncomputable def triplesR (cr : CR) (low : Bool) (lab : ℕ × ℕ) (s : ℕ) (ya yb : RF) : List (List TriR) :=
  let r : List RF := [fun l x => 1 - cr.q l x * ya l x, fun l x => 1 - cr.q l x * yb l x]
  let gs : List RF := [srcR cr low ya, srcR cr low yb]
  let ut := parR cr lab s ya yb cr.u
  let vt := parR cr lab s ya yb cr.v
  let st := parR cr lab s ya yb cr.s
  let tt := parR cr lab s ya yb cr.t
  let omp : List RF := [fun l x => 1 - cr.p l x]
  let omr := rsub [fun _ _ => 1] r
  let nu := radd (radd (rmul r omp) (rmul ut [cr.hp])) (rmul (rmul omr st) omp)
  let nv := radd (radd (rmul r omp) (rmul vt [cr.hp])) (rmul (rmul omr st) omp)
  let beta := radd (radd (rmul r [cr.tau]) (rmul omr tt)) [cr.w]
  let ss := rmul r [cr.so]
  let elG : List RF := [fun l x => cr.ell l x * cr.G l x / cr.p l x]
  let rgC := rmul (rmul r gs) [cr.C]
  let rphw := rmul (rmul r [cr.phi]) [cr.w]
  let d1 := rsub (radd (radd (rsub rgC nv) (rmul omr tt)) rphw) elG
  let d0 := radd (radd (rsub (radd (rsub (rsub rgC (rmul r [cr.tau])) [cr.w]) rphw) elG) [cr.av]) ss
  let ssav := radd ss [cr.av]
  let two : List RF := [fun _ _ => 2]
  [rcontrols (rsub ssav nu) (rsub (rmul ssav two) beta) d0,
    rcontrols (rsub ssav nv) (rsub (rmul nv two) beta) d1,
    rcontrols (rsub (radd ss [cr.au]) nv) (rsub beta (rmul nv two)) d1]

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The real functions of the context of a band with branch choices `fl`. -/
noncomputable def ctxR (sd : SegData) (fl : Flags) : CR where
  lam := fun l _ => l
  x := fun _ x => x
  q := fun l _ => qR l
  p := pR
  upper := upR
  hp := fun l x => pR l x / -Real.log (1 - pR l x)
  G := fun l x => Real.log ((l + 1) * x / (le1R l x * le1R l x))
  tau := fieldR sd sd.Ltau sd.Rtau
  au := auR sd fl.kern
  av := avR sd fl.kern
  so := soR sd fl.kern
  phi := phiR fl.kern
  hn := hnR
  u := fun j l _ => lerpR sd.lo sd.hi sd.Lu[j]! sd.Ru[j]! l
  v := fun j l _ => lerpR sd.lo sd.hi sd.Lv[j]! sd.Rv[j]! l
  s := fun j l _ => lerpR sd.lo sd.hi sd.Ls[j]! sd.Rs[j]! l
  t := fun j l _ => lerpR sd.lo sd.hi sd.Ltau[j]! sd.Rtau[j]! l
  w := fun l _ => lerpR sd.lo sd.hi sd.Lw sd.Rw l
  ell := fun l _ => lerpR sd.lo sd.hi sd.Lell sd.Rell l
  C := fun l _ => 1 / (l + 1) * (sd.gamma : ℝ)

section Enc

variable {L X : Ival} {sd : SegData} {fl : Flags} {c : Ctx}

theorem de_zero : DE L X (0 : RF) zeroDN := de_cst mem_zI

theorem le_getD {fs : List RF} {ds : List DN} (h : LE L X fs ds) (i : ℕ) :
    DE L X (fs.getD i 0) (ds.getD i zeroDN) := by
  induction h generalizing i with
  | nil => simpa using de_zero
  | cons ha _ ih =>
    cases i with
    | zero => simpa using ha
    | succ i => simpa using ih i

theorem te_controls {A B E : List RF} {A' B' E' : List DN} (hA : LE L X A A') (hB : LE L X B B')
    (hE : LE L X E E') : List.Forall₂ (TE L X) (rcontrols A B E) (controls A' B' E') := by
  have ha := le_relev hA 2; have hb := le_relev hB 2; have he := le_relev hE 2
  exact List.Forall₂.cons ⟨le_getD ha 0, le_getD hb 0, le_getD he 0⟩
    (List.Forall₂.cons ⟨le_getD ha 1, le_getD hb 1, le_getD he 1⟩
      (List.Forall₂.cons ⟨le_getD ha 2, le_getD hb 2, le_getD he 2⟩ List.Forall₂.nil))

theorem de_fnorm {fa fl' : RF} {a lam : DN} (ha : DE L X fa a) (hl : DE L X fl' lam) :
    DE L X (fun l x => fnR (fl' l x) (fa l x)) (fnorm a lam) := by
  unfold fnorm fnR
  exact de_dmax (de_mul (de_rsubI mem_oneI (de_div (de_cst mem_oneI) (de_mulI (de_addI hl mem_oneI) mem_twoI))) ha)
    (de_sub ha (de_mul (de_div (de_cst mem_oneI) (de_mulI hl mem_twoI)) (de_rsubI mem_oneI ha)))

theorem de_source (hc : CtxE L X sd fl c) {fY : RF} {Y : DN} (hY : DE L X fY Y) :
    DE L X (srcR (ctxR sd fl) fl.low fY) (source c Y) := by
  have hr := de_rsubI mem_oneI (de_mul hc.q hY)
  unfold source srcR
  rw [hc.low]
  cases hlow : fl.low
  · simp only [if_false, Bool.false_eq_true]
    exact de_divI (de_sub (de_addI (de_fnorm (de_mul hc.x hr) hc.lam) mem_oneI)
      (de_fnorm (de_mx hY (de_mul (de_rsubI mem_oneI (de_mul hc.p hr)) hc.hn)) hc.lam)) mem_twoI
  · simp only [if_true]
    exact de_mul (de_mul hc.x hr) (de_rsubI mem_oneI (de_div (de_cst mem_oneI) (de_mulI (de_addI hc.lam mem_oneI) mem_twoI)))

theorem de_clampSeg {fY : RF} {Y : DN} (hY : DE L X fY Y) (s : ℕ) : DE L X (clampR fY s) (clampSeg Y s) := by
  unfold clampSeg clampR
  have h1 := mem_knotI s
  have h2 := mem_knotI (s + 1)
  exact de_mx (de_cst h1) (de_mn (de_cst h2) hY)

theorem de_segR {f : ℕ → RF} {vals : Array DN} (hv : ∀ j < 9, DE L X (f j) (vals.getD j zeroDN)) {fX : RF}
    {Xd : DN} (hX : DE L X fX Xd) {j : ℕ} (hj : j < 8) : DE L X (segR f fX j) (interpSeg vals Xd j) :=
  de_add (hv j (by omega)) (de_mul (de_sub (hv (j + 1) (by omega)) (hv j (by omega)))
    (de_subI (de_mulI hX mem_eightI) (mem_ptOne j)))

theorem le_parR (hc : CtxE L X sd fl c) (lab : ℕ × ℕ) (hlab : lab.2 ≤ 7) (s : ℕ) (hs : s ≤ 7) {fa fb : RF}
    {ya yb : DN} (hya : DE L X fa ya) (hyb : DE L X fb yb) {f : ℕ → RF} {vals : Array DN}
    (hv : ∀ j < 9, DE L X (f j) (vals.getD j zeroDN)) :
    LE L X (parR (ctxR sd fl) lab s fa fb f)
      (if lab.1 = 1 then [vals.getD lab.2 zeroDN]
        else if lab.1 = 2 then [interpSeg vals (clampSeg c.upper lab.2) lab.2]
        else lin (interpSeg vals (clampSeg ya s) s) (interpSeg vals (clampSeg yb s) s)) := by
  unfold parR lin
  split_ifs
  · exact le_single (hv _ (by omega))
  · exact le_single (de_segR hv (de_clampSeg hc.upper _) (by omega))
  · exact le_pair (de_segR hv (de_clampSeg hya _) (by omega)) (de_segR hv (de_clampSeg hyb _) (by omega))

/-- **The controls of a piece enclose the real controls.** -/
theorem triples_enc (hc : CtxE L X sd fl c) (lab : ℕ × ℕ) (hlab : lab.2 ≤ 7) (s : ℕ) (hs : s ≤ 7) {fa fb : RF}
    {ya yb : DN} (hya : DE L X fa ya) (hyb : DE L X fb yb) :
    List.Forall₂ (List.Forall₂ (TE L X)) (triplesR (ctxR sd fl) fl.low lab s fa fb) (triples c lab s ya yb) := by
  have hr : LE L X [fun l x => 1 - qR l * fa l x, fun l x => 1 - qR l * fb l x]
      (lin (drsubI oneI (dmul c.q ya)) (drsubI oneI (dmul c.q yb))) :=
    le_pair (de_rsubI mem_oneI (de_mul hc.q hya)) (de_rsubI mem_oneI (de_mul hc.q hyb))
  have hgs : LE L X [srcR (ctxR sd fl) fl.low fa, srcR (ctxR sd fl) fl.low fb] (lin (source c ya) (source c yb)) :=
    le_pair (de_source hc hya) (de_source hc hyb)
  have hut := le_parR hc lab hlab s hs hya hyb (f := (ctxR sd fl).u) hc.co.u
  have hvt := le_parR hc lab hlab s hs hya hyb (f := (ctxR sd fl).v) hc.co.v
  have hst := le_parR hc lab hlab s hs hya hyb (f := (ctxR sd fl).s) hc.co.s
  have htt := le_parR hc lab hlab s hs hya hyb (f := (ctxR sd fl).t) hc.co.tau
  have homp : LE L X [fun l x => 1 - pR l x] [drsubI oneI c.p] := le_single (de_rsubI mem_oneI hc.p)
  have homr := le_rsub (le_single (de_cst (L := L) (X := X) mem_oneI)) hr
  have hhp := le_single hc.hp
  have htau := le_single hc.tau
  have hw := le_single hc.co.w
  have hso := le_single hc.so
  have hphi := le_single hc.phi
  have hav := le_single hc.av
  have hau := le_single hc.au
  have hC := le_single hc.co.C
  have helG : LE L X [fun l x => lerpR sd.lo sd.hi sd.Lell sd.Rell l *
      Real.log ((l + 1) * x / (le1R l x * le1R l x)) / pR l x] [ddiv (dmul c.co.ell c.G) c.p] :=
    le_single (de_div (de_mul hc.co.ell hc.G) hc.p)
  have htwo : LE L X [fun _ _ => (2 : ℝ)] [DN.cst twoI] := le_single (de_cst mem_twoI)
  have hnu := le_radd (le_radd (le_rmul hr homp) (le_rmul hut hhp)) (le_rmul (le_rmul homr hst) homp)
  have hnv := le_radd (le_radd (le_rmul hr homp) (le_rmul hvt hhp)) (le_rmul (le_rmul homr hst) homp)
  have hbeta := le_radd (le_radd (le_rmul hr htau) (le_rmul homr htt)) hw
  have hss := le_rmul hr hso
  have hrgC := le_rmul (le_rmul hr hgs) hC
  have hrphw := le_rmul (le_rmul hr hphi) hw
  have hd1 := le_rsub (le_radd (le_radd (le_rsub hrgC hnv) (le_rmul homr htt)) hrphw) helG
  have hd0 := le_radd (le_radd (le_rsub (le_radd (le_rsub (le_rsub hrgC (le_rmul hr htau)) hw) hrphw) helG) hav) hss
  have hssav := le_radd hss hav
  exact List.Forall₂.cons (te_controls (le_rsub hssav hnu) (le_rsub (le_rmul hssav htwo) hbeta) hd0)
    (List.Forall₂.cons (te_controls (le_rsub hssav hnv) (le_rsub (le_rmul hnv htwo) hbeta) hd1)
      (List.Forall₂.cons (te_controls (le_rsub (le_radd hss hau) hnv) (le_rsub hbeta (le_rmul hnv htwo)) hd1)
        List.Forall₂.nil))

end Enc

end Erdos993Lean.Analytic.O2.Cert
