import Mathlib
import Erdos993Lean.Analytic.O2.Cert.PackSound

/-!
# O2 certificate checker (lane A18): the context of a cell encloses the real payment data

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The checker's context
(`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, `context`) evaluates at the dual numbers of the box coordinates
`λ`, `x = p/q` all quantities of the local payment (`PRO_R2_PROOF.md` §4, §6, §8).  Here every one of them is shown
to enclose a named real function (`CtxE`, **`context_enc`**), with the conventions of `Erdos993Lean/Analytic/O2/Defs.lean`:

* the packed child masses through `de_packing` (`PackSound.lean`);
* the fields `pwLin` on one segment (`de_interpSeg`, `de_interpX`, by A16's `pwLin_eq_cell`);
* the kernel branch `x ≥ 7/8` through `kR` (`KernelSound.lean`);
* the three source cuts (`cutR`, `cuts_eq`).

The coordinates may be any dual numbers enclosing `λ` and `x` (`context_enc'`): the cell uses `lamDN`, `xDN`
(`context_enc`), an anchor point uses `ptDN` over a point box (`context_enc_pt`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The real functions of the context -/

/-- The activity interpolation of one table entry: `(λ − lo)/(hi − lo) · (b − a) + a`. -/
noncomputable def lerpR (lo hi a b : ℚ) (l : ℝ) : ℝ := (l - lo) / ((hi - lo : ℚ) : ℝ) * ((b : ℝ) - a) + a

/-- The field of the table pair `(L, R)` at `(λ, x)`: `pwLin` of the interpolated knots. -/
noncomputable def fieldR (sd : SegData) (L R : Array ℚ) (l x : ℝ) : ℝ :=
  pwLin (fun i : Fin 9 => lerpR sd.lo sd.hi L[(i : ℕ)]! R[(i : ℕ)]! l) x

noncomputable def qR (l : ℝ) : ℝ := l / (l + 1)
noncomputable def pR (l x : ℝ) : ℝ := qR l * x
noncomputable def upR (l x : ℝ) : ℝ := (1 - pR l x) / (1 - qR l * pR l x)
noncomputable def le1R (l x : ℝ) : ℝ := l * (1 - x) + 1
noncomputable def hnR (l x : ℝ) : ℝ := min 1 ((l + 1) * (l + 1) * (1 - x) / (l * le1R l x))
noncomputable def kapR (l : ℝ) : ℝ := 1 / (qR l + 1)
noncomputable def nnR (l x : ℝ) : ℝ := max 0 (x - kapR l)

/-- The three source cuts `Y_f`, `Y_M`, `Y_o` (the last by the formula `b`). -/
noncomputable def cutR (b : ℕ) (i : ℕ) (l x : ℝ) : ℝ :=
  if i = 0 then nnR l x / pR l x
  else if i = 1 then kapR l * nnR l x / max (nnR l x) (kapR l * pR l x * qR l * (hnR l x * qR l))
  else if b = 0 then (1 - x) / (qR l * (1 - pR l x * (hnR l x * qR l)))
  else if b = 1 then upR l x
  else hnR l x * (1 - pR l x) / (1 - pR l x * (hnR l x * qR l))

/-- The own coefficients `A_u, A_v`, the `s(x)/H` factor and `φ`, by branch. -/
noncomputable def auR (sd : SegData) (kern : Bool) (l x : ℝ) : ℝ :=
  if kern then lerpR sd.lo sd.hi sd.Lu[7]! sd.Ru[7]! l * 8 / (pR l x * kR (1 - x) l)
  else fieldR sd sd.Lu sd.Ru l x / (pR l x * Real.log (le1R l x / x))

noncomputable def avR (sd : SegData) (kern : Bool) (l x : ℝ) : ℝ :=
  if kern then lerpR sd.lo sd.hi sd.Lv[7]! sd.Rv[7]! l * 8 / (pR l x * kR (1 - x) l)
  else fieldR sd sd.Lv sd.Rv l x / (pR l x * Real.log (le1R l x / x))

noncomputable def soR (sd : SegData) (kern : Bool) (l x : ℝ) : ℝ :=
  if kern then lerpR sd.lo sd.hi sd.Ls[7]! sd.Rs[7]! l * 8 * x / (l + 1)
  else fieldR sd sd.Ls sd.Rs l x / packH l (pR l x)

noncomputable def phiR (kern : Bool) (l x : ℝ) : ℝ :=
  if kern then (l + 1) * (1 - x) / le1R l x else packPhi l (pR l x)

/-- The enclosure of the coefficient fields. -/
structure CoeffE (L X : Ival) (sd : SegData) (co : Coeffs) : Prop where
  u : ∀ j < 9, DE L X (fun l _ => lerpR sd.lo sd.hi sd.Lu[j]! sd.Ru[j]! l) (co.u.getD j zeroDN)
  v : ∀ j < 9, DE L X (fun l _ => lerpR sd.lo sd.hi sd.Lv[j]! sd.Rv[j]! l) (co.v.getD j zeroDN)
  s : ∀ j < 9, DE L X (fun l _ => lerpR sd.lo sd.hi sd.Ls[j]! sd.Rs[j]! l) (co.s.getD j zeroDN)
  tau : ∀ j < 9, DE L X (fun l _ => lerpR sd.lo sd.hi sd.Ltau[j]! sd.Rtau[j]! l) (co.tau.getD j zeroDN)
  w : DE L X (fun l _ => lerpR sd.lo sd.hi sd.Lw sd.Rw l) co.w
  ell : DE L X (fun l _ => lerpR sd.lo sd.hi sd.Lell sd.Rell l) co.ell
  C : DE L X (fun l _ => 1 / (l + 1) * (sd.gamma : ℝ)) co.C

theorem de_knotDN {L X : Ival} {sd : SegData} {ww : DN}
    (hww : DE L X (fun l _ => (l - sd.lo) / ((sd.hi - sd.lo : ℚ) : ℝ)) ww) (a b : ℚ) :
    DE L X (fun l _ => lerpR sd.lo sd.hi a b l) (knotDN ww a b) :=
  de_addI (de_mulI hww (mem_sub (mem_ofRat b) (mem_ofRat a))) (mem_ofRat a)

theorem knotTab_getD (ww : DN) (A B : Array ℚ) {j : ℕ} (hj : j < 9) :
    (knotTab ww A B).getD j zeroDN = knotDN ww A[j]! B[j]! := by
  unfold knotTab
  simp [Array.getD, hj]

/-- The coefficient fields at any dual number `lam` enclosing `λ`. -/
theorem coeffs_enc {L X : Ival} (sd : SegData) {lam : DN} (hlam : DE L X (fun l _ => l) lam) :
    CoeffE L X sd (coefficients sd lam) := by
  have hww : DE L X (fun l _ => (l - sd.lo) / ((sd.hi - sd.lo : ℚ) : ℝ))
      (ddivI (dsubI lam (ofRat sd.lo)) (ofRat (sd.hi - sd.lo))) :=
    de_divI (de_subI hlam (mem_ofRat _)) (mem_ofRat _)
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, de_knotDN hww _ _, de_knotDN hww _ _,
    de_mulI (de_div (de_cst mem_oneI) (de_addI hlam mem_oneI)) (mem_ofRat _)⟩ <;>
  · simp only [coefficients]; rw [knotTab_getD _ _ _ hj]; exact de_knotDN hww _ _

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- `segOf X = some j` puts every point of `X` into segment `j`. -/
theorem segOf_spec {X : Ival} {j : ℕ} (h : segOf X = some j) :
    j < 8 ∧ ∀ x, X.Mem x → (j : ℝ) / 8 ≤ x ∧ x ≤ ((j : ℝ) + 1) / 8 := by
  unfold segOf at h
  simp only at h
  set k := (max 0 (min 7 (fdivP (8 * X.lo)))).toNat with hk
  have hk7 : k ≤ 7 := by
    have : max 0 (min 7 (fdivP (8 * X.lo))) ≤ 7 := max_le (by norm_num) (min_le_left _ _)
    omega
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    refine ⟨by omega, fun x hx => ⟨?_, ?_⟩⟩
    · have := (toR_le_toR.mpr h1.1).trans hx.1
      rw [toR_eighth_mul] at this; push_cast at this; exact this
    · have := hx.2.trans (toR_le_toR.mpr h1.2)
      rw [show ((k : ℤ) + 1) * eighth = (((k + 1 : ℕ) : ℤ)) * eighth by push_cast; ring, toR_eighth_mul] at this
      push_cast at this; exact this
  · simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨h21, h22⟩, h23⟩ := h2
    refine ⟨by omega, fun x hx => ⟨?_, ?_⟩⟩
    · have := (toR_le_toR.mpr h22).trans hx.1
      rw [show ((k : ℤ) - 1) * eighth = (((k - 1 : ℕ) : ℤ)) * eighth by push_cast [Nat.cast_sub h21]; ring,
        toR_eighth_mul] at this
      push_cast at this; exact this
    · have := hx.2.trans (toR_le_toR.mpr h23)
      rw [toR_eighth_mul] at this
      have e : ((k - 1 : ℕ) : ℝ) + 1 = k := by push_cast [Nat.cast_sub h21]; ring
      rw [e]; exact this

/-- The segment formula encloses the field. -/
theorem de_interpSeg {L X : Ival} {sd : SegData} {vals : Array DN} {A B : Array ℚ} {Xd : DN} {fX : ℝ → ℝ → ℝ}
    (hv : ∀ j < 9, DE L X (fun l _ => lerpR sd.lo sd.hi A[j]! B[j]! l) (vals.getD j zeroDN))
    (hX : DE L X fX Xd) {j : ℕ} (hj : j < 8)
    (hseg : ∀ l x, L.Mem l → X.Mem x → (j : ℝ) / 8 ≤ fX l x ∧ fX l x ≤ ((j : ℝ) + 1) / 8) :
    DE L X (fun l x => pwLin (fun i : Fin 9 => lerpR sd.lo sd.hi A[(i : ℕ)]! B[(i : ℕ)]! l) (fX l x))
      (interpSeg vals Xd j) := by
  have h := de_add (hv j (by omega)) (de_mul (de_sub (hv (j + 1) (by omega)) (hv j (by omega)))
    (de_subI (de_mulI hX mem_eightI) (mem_ptOne j)))
  refine de_congr h (fun l x hl hx => ?_)
  obtain ⟨h1, h2⟩ := hseg l x hl hx
  rw [pwLin_eq_cell _ j hj h1 h2]
  simp only
  ring

theorem de_interpX {L X : Ival} {sd : SegData} {vals : Array DN} {A B : Array ℚ} {xd : DN}
    (hxd : DE L X (fun _ x => x) xd) (hxv : ∀ x, X.Mem x → xd.v.Mem x)
    (hv : ∀ j < 9, DE L X (fun l _ => lerpR sd.lo sd.hi A[j]! B[j]! l) (vals.getD j zeroDN)) :
    DE L X (fun l x => pwLin (fun i : Fin 9 => lerpR sd.lo sd.hi A[(i : ℕ)]! B[(i : ℕ)]! l) x)
      (interpX vals xd) := by
  unfold interpX
  split
  · rename_i j hj
    obtain ⟨hj8, hseg⟩ := segOf_spec hj
    exact de_interpSeg hv hxd hj8 (fun l x _ hx => hseg x (hxv x hx))
  · intro h; simp at h

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The crossover threshold `κ = 1/(1+q)` of a context. -/
def kapDN (c : Ctx) : DN := ddiv oneDN (daddI c.q oneI)

/-- `h_c = H_c/q · q`. -/
def hcDN (c : Ctx) : DN := dmul c.hn c.q

/-- `max(0, x − κ)`. -/
def nnDN (c : Ctx) : DN := mx zeroDN (dsub c.x (kapDN c))

theorem cuts_eq (sd : SegData) (lam x : DN) (fl : Flags) :
    (context sd lam x fl).cuts = if fl.low then [] else
      [ddiv (nnDN (context sd lam x fl)) (context sd lam x fl).p,
        ddiv (dmul (kapDN (context sd lam x fl)) (nnDN (context sd lam x fl)))
          (mx (nnDN (context sd lam x fl)) (dmul (dmul (dmul (kapDN (context sd lam x fl)) (context sd lam x fl).p)
            (context sd lam x fl).q) (hcDN (context sd lam x fl)))),
        if (context sd lam x fl).y0b = 0 then
          ddiv (context sd lam x fl).e (dmul (context sd lam x fl).q
            (drsubI oneI (dmul (context sd lam x fl).p (hcDN (context sd lam x fl)))))
        else if (context sd lam x fl).y0b = 1 then (context sd lam x fl).upper
        else ddiv (dmul (context sd lam x fl).hn (drsubI oneI (context sd lam x fl).p))
          (drsubI oneI (dmul (context sd lam x fl).p (hcDN (context sd lam x fl))))] := by
  simp only [context, kapDN, hcDN, nnDN]

theorem cutR_two (b : ℕ) (l x : ℝ) : cutR b 2 l x =
    if b = 0 then (1 - x) / (qR l * (1 - pR l x * (hnR l x * qR l)))
    else if b = 1 then upR l x else hnR l x * (1 - pR l x) / (1 - pR l x * (hnR l x * qR l)) := by
  simp [cutR]

/-- **The enclosure of a context**: every value of the checker's context is a dual number enclosing the named real
function on the box. -/
structure CtxE (L X : Ival) (sd : SegData) (fl : Flags) (c : Ctx) : Prop where
  co : CoeffE L X sd c.co
  lam : DE L X (fun l _ => l) c.lam
  x : DE L X (fun _ x => x) c.x
  q : DE L X (fun l _ => qR l) c.q
  p : DE L X pR c.p
  upper : DE L X upR c.upper
  hp : DE L X (fun l x => pR l x / -Real.log (1 - pR l x)) c.hp
  G : DE L X (fun l x => Real.log ((l + 1) * x / (le1R l x * le1R l x))) c.G
  tau : DE L X (fieldR sd sd.Ltau sd.Rtau) c.tau
  au : DE L X (auR sd fl.kern) c.au
  av : DE L X (avR sd fl.kern) c.av
  so : DE L X (soR sd fl.kern) c.so
  phi : DE L X (phiR fl.kern) c.phi
  hn : DE L X hnR c.hn
  low : c.low = fl.low
  cuts : c.cuts.length = (if fl.low then 0 else 3) ∧
    ∀ i < c.cuts.length, DE L X (cutR c.y0b i) (c.cuts.getD i zeroDN)
  y0b : fl.y0b ≤ 2 → c.y0b = fl.y0b

/-- The box facts used by the non-kernel branch. -/
theorem box_facts {L X : Ival} (hL : 0 < L.lo) (hX : 0 < X.lo) (hX1 : X.hi < one) {l x : ℝ} (hl : L.Mem l)
    (hx : X.Mem x) :
    0 < l ∧ 0 < pR l x ∧ pR l x < actQ l ∧ le1R l x / x = l * (1 - pR l x) / pR l x ∧ qR l = actQ l := by
  have hl0 : 0 < l := (toR_pos.mpr hL).trans_le hl.1
  have hx0 : 0 < x := (toR_pos.mpr hX).trans_le hx.1
  have hx1 : x < 1 := by
    have := hx.2.trans_lt (toR_lt_toR.mpr hX1); rwa [toR_one] at this
  have hq : qR l = actQ l := by unfold qR actQ; rw [add_comm]
  refine ⟨hl0, ?_, ?_, ?_, hq⟩
  · unfold pR qR; positivity
  · unfold pR; rw [hq]
    have : 0 < actQ l := by unfold actQ; positivity
    nlinarith
  · unfold le1R pR qR
    have h1 : (0 : ℝ) < l + 1 := by linarith
    field_simp
    ring

/-- **The enclosure of a context** at any coordinate dual numbers `lam`, `x` enclosing `λ`, `x` on the box. -/
theorem context_enc' {L X : Ival} (sd : SegData) (fl : Flags) {lam x : DN} (hlam : DE L X (fun l _ => l) lam)
    (hx : DE L X (fun _ x => x) x) (hxv : ∀ y, X.Mem y → x.v.Mem y) (hlok : lam.ok = true) (hxok : x.ok = true)
    (hxlo : 0 < x.v.lo) (hL : 0 < L.lo) (hX : 0 < X.lo) (hX1 : fl.kern = false → X.hi < one) :
    CtxE L X sd fl (context sd lam x fl) := by
  have hco := coeffs_enc (L := L) (X := X) sd hlam
  have hlam1 : DE L X (fun l _ => l + 1) (daddI lam oneI) := de_addI hlam mem_oneI
  have hq : DE L X (fun l _ => qR l) (ddiv lam (daddI lam oneI)) := de_div hlam hlam1
  have hp : DE L X pR (dmul (ddiv lam (daddI lam oneI)) x) := de_mul hq hx
  have he : DE L X (fun _ x => 1 - x) (drsubI oneI x) := de_rsubI mem_oneI hx
  have homp : DE L X (fun l x => 1 - pR l x) (drsubI oneI (dmul (ddiv lam (daddI lam oneI)) x)) :=
    de_rsubI mem_oneI hp
  have hle1 : DE L X le1R (daddI (dmul lam (drsubI oneI x)) oneI) := de_addI (de_mul hlam he) mem_oneI
  have hhn := de_mn (de_cst (L := L) (X := X) mem_oneI)
    (de_div (de_mul (de_mul hlam1 hlam1) he) (de_mul hlam hle1))
  have hhc := de_mul hhn hq
  have hkap : DE L X (fun l _ => kapR l) _ := de_div (de_cst (L := L) (X := X) mem_oneI) (de_addI hq mem_oneI)
  have hupper : DE L X upR _ := de_div homp (de_rsubI mem_oneI (de_mul hq hp))
  refine ⟨hco, hlam, hx, hq, hp, hupper, de_div hp (de_neg (de_log homp)),
    de_log (de_div (de_mul hlam1 hx) (de_mul hle1 hle1)), de_interpX hx hxv hco.tau, ?_, ?_, ?_, ?_, hhn, rfl, ?_, ?_⟩
  -- the own coefficients, by branch
  · cases hk : fl.kern
    · simp only [context, hk, auR, if_false]
      exact de_div (de_interpX hx hxv hco.u) (de_mul hp (de_log (de_div hle1 hx)))
    · simp only [context, hk, auR, if_true]
      exact de_div (de_mulI (hco.u 7 (by norm_num)) mem_eightI) (de_mul hp (de_kernel he hlam))
  · cases hk : fl.kern
    · simp only [context, hk, avR, if_false]
      exact de_div (de_interpX hx hxv hco.v) (de_mul hp (de_log (de_div hle1 hx)))
    · simp only [context, hk, avR, if_true]
      exact de_div (de_mulI (hco.v 7 (by norm_num)) mem_eightI) (de_mul hp (de_kernel he hlam))
  · cases hk : fl.kern
    · simp only [context, hk, soR, if_false]
      have haok : (ddiv (daddI (dmul lam (drsubI oneI x)) oneI) x).ok = true := by
        simp [ddiv, daddI, dmul, drsubI, dneg, hlok, hxok, hxlo]
      exact de_div (de_interpX hx hxv hco.s) (de_packing (P := pR) hlam hq (de_div hle1 hx) hlam1 hlok haok
        (fun l x hl hx' => box_facts hL hX (hX1 hk) hl hx')).1
    · simp only [context, hk, soR, if_true]
      exact de_div (de_mul (de_mulI (hco.s 7 (by norm_num)) mem_eightI) hx) hlam1
  · cases hk : fl.kern
    · simp only [context, hk, phiR, if_false]
      have haok : (ddiv (daddI (dmul lam (drsubI oneI x)) oneI) x).ok = true := by
        simp [ddiv, daddI, dmul, drsubI, dneg, hlok, hxok, hxlo]
      exact (de_packing (P := pR) hlam hq (de_div hle1 hx) hlam1 hlok haok
        (fun l x hl hx' => box_facts hL hX (hX1 hk) hl hx')).2
    · simp only [context, hk, phiR, if_true]
      exact de_div (de_mul hlam1 he) hle1
  -- the cuts
  · set c := context sd lam x fl with hc
    have hcx : DE L X (fun _ x => x) c.x := hx
    have hcp : DE L X pR c.p := hp
    have hcq : DE L X (fun l _ => qR l) c.q := hq
    have hce : DE L X (fun _ x => 1 - x) c.e := he
    have hchn : DE L X hnR c.hn := hhn
    have hcup : DE L X upR c.upper := hupper
    have hk : DE L X (fun l _ => kapR l) (kapDN c) := de_div (de_cst (L := L) (X := X) mem_oneI) (de_addI hcq mem_oneI)
    have hhc' : DE L X (fun l x => hnR l x * qR l) (hcDN c) := de_mul hchn hcq
    have hnn : DE L X nnR (nnDN c) := de_mx (de_cst (L := L) (X := X) mem_zI) (de_sub hcx hk)
    rw [cuts_eq]
    cases hlow : fl.low
    · refine ⟨by simp, fun i hi => ?_⟩
      simp only [Bool.false_eq_true, if_false, List.length_cons, List.length_nil] at hi
      interval_cases i
      · exact de_div hnn hcp
      · exact de_div (de_mul hk hnn) (de_mx hnn (de_mul (de_mul (de_mul hk hcp) hcq) hhc'))
      · simp only [Bool.false_eq_true, if_false, List.getD_cons_succ, List.getD_cons_zero]
        refine de_congr ?_ (fun l x _ _ => (cutR_two c.y0b l x).symm)
        split_ifs
        · exact de_div hce (de_mul hcq (de_rsubI mem_oneI (de_mul hcp hhc')))
        · exact hcup
        · exact de_div (de_mul hchn (de_rsubI mem_oneI hcp)) (de_rsubI mem_oneI (de_mul hcp hhc'))
    · exact ⟨by simp, fun i hi => by simp at hi⟩
  · intro h; simp only [context]; rw [if_pos h]


/-- **The enclosure of the context of a cell** (`λ`, `x` the box coordinates). -/
theorem context_enc {L X : Ival} (sd : SegData) (fl : Flags) (hL : 0 < L.lo) (hX : 0 < X.lo)
    (hX1 : fl.kern = false → X.hi < one) :
    CtxE L X sd fl (context sd (lamDN L) (xDN X) fl) :=
  context_enc' sd fl de_lam de_x (fun _ h => h) rfl rfl hX hL hX hX1

/-- A point of a point interval. -/
theorem pt_mem_eq {a : ℤ} {c : ℝ} (h : (pt a).Mem c) : c = toR a := le_antisymm h.2 h.1

/-- Every slope statement holds on a point interval (there are no two distinct points). -/
theorem sl_pt (I : Ival) (a : ℤ) (φ : ℝ → ℝ) : Sl I (pt a) φ := fun _ _ hc hd hcd =>
  absurd ((pt_mem_eq hc).trans (pt_mem_eq hd).symm) hcd

/-- The coordinate `λ` at a point box, with zero slope seeds. -/
theorem de_ptDN_lam (a b : ℤ) : DE (pt a) (pt b) (fun l _ => l) (ptDN a) := fun _ =>
  ⟨fun _ _ hl _ => hl, fun _ _ => sl_pt _ _ _, fun _ _ => sl_pt _ _ _⟩

/-- The coordinate `x` at a point box, with zero slope seeds. -/
theorem de_ptDN_x (a b : ℤ) : DE (pt a) (pt b) (fun _ x => x) (ptDN b) := fun _ =>
  ⟨fun _ _ _ hx => hx, fun _ _ => sl_pt _ _ _, fun _ _ => sl_pt _ _ _⟩

/-- **The enclosure of an anchor context** (a point box, zero slope seeds). -/
theorem context_enc_pt (sd : SegData) (fl : Flags) {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hb1 : fl.kern = false → b < one) :
    CtxE (pt a) (pt b) sd fl (context sd (ptDN a) (ptDN b) fl) :=
  context_enc' sd fl (de_ptDN_lam a b) (de_ptDN_x a b) (fun _ h => h) rfl rfl hb ha hb hb1

end Erdos993Lean.Analytic.O2.Cert
