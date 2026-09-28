import Mathlib
import Erdos993Lean.Analytic.Profile30
import Erdos993Lean.Analytic.Atlas.Sound
import Erdos993Lean.Analytic.Atlas.Params

/-!
# The O4 atlas (lane A9): the certified profile

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  Connects the band checks of the atlas
(`Atlas/Checker.lean`, meaning proved in `Atlas/Sound.lean`) to the certified profile
`Erdos993Lean/Analytic/Profile30.lean` and to T1's explicit threshold condition of
`Erdos993Lean/Analytic/Defs.lean`.

**The tail function.**  Soul's atlas prices the lower tail with the base `(1 + λ_h)/(1 + λ_h t_k)` of
the *box's* upper activity `λ_h = q_h/(1 − q_h)` (`atlas_arb.py: t_upper(m_l, q_h, …)`), while
`Profile30.tailFn` uses the band's upper edge `λ_{i+1} ≥ λ_h`.  With the band edge, 78 of the 1,502
lower boxes have a non-positive margin (2) on their whole `m`-range; each of them passes on the two
halves of its `m`-range with the same dual and centre (the data split them), so all checks use the
band-edge base and apply to `Profile30.P` itself.  Lane A3's `Tail.tail_t31` proves the tail with the
actual activity `t` (`tailFnAct`, below the band-edge terms); `AtlasProfile P` (Profile30's `θ`, `D`,
`M1`, floor, and a tail function `≤ tailFnAct`, e.g. `P30act`) is covered as well.

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* `count_lt_spec`, `edgeR`, `edges_lt`, `edgeR_mono`, **`bandOf_spec`**: an activity in range lies in
  its band, `λ_i ≤ t ≤ λ_{i+1}` for `i = bandOf t < 30`.
* `bandAt_eq`, `tvals_eq`: the checker's band table is Profile30's data (`decide +kernel`).
* `tailTermAct`, `tailFnAct`, `P30act`, `tailFn_le_edge`, `tailFnAct_le`.
* **`edge_of_band`**: one band passing with the band-edge tail base.
* **`explicitThreshold_small_lower_P30_of_checks`** (`m ≤ 50`),
  **`explicitThreshold_small_upper_P30_of_checks`** (`50 ≤ m ≤ 400`),
  **`explicitThreshold_small_P30_of_checks`** (`m < 400`, the `hsmall` hypothesis of
  `thresholdNoValley_of_split`) for `Profile30.P`, and `explicitThreshold_small_of_checks` for every
  `AtlasProfile`: from the band checks, for arbitrary data.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.Profile30

namespace Erdos993Lean.Analytic.Atlas

/-- The count of the terms `e(k + 1) < t` (`k < n`) of a monotone sequence locates `t`. -/
theorem count_lt_spec (e : ℕ → ℝ) (t : ℝ) (n : ℕ) (hmono : ∀ a b, a ≤ b → b ≤ n → e a ≤ e b) :
    (∀ k, k < ((List.range n).filter fun i => decide (e (i + 1) < t)).length → e (k + 1) < t) ∧
    (∀ k, ((List.range n).filter fun i => decide (e (i + 1) < t)).length ≤ k → k < n → t ≤ e (k + 1)) ∧
    ((List.range n).filter fun i => decide (e (i + 1) < t)).length ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun a b hab hb => hmono a b hab (by omega)
    obtain ⟨h1, h2, h3⟩ := ih'
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hn : e (n + 1) < t
    · have hf : ([n].filter fun i => decide (e (i + 1) < t)).length = 1 := by simp [hn]
      rw [hf]
      -- every k < n is counted
      have hall : ((List.range n).filter fun i => decide (e (i + 1) < t)).length = n := by
        by_contra hne
        have hlt : ((List.range n).filter fun i => decide (e (i + 1) < t)).length < n := by omega
        have := h2 _ le_rfl hlt
        have hm := hmono (((List.range n).filter fun i => decide (e (i + 1) < t)).length + 1) (n + 1)
          (by omega) le_rfl
        linarith
      rw [hall]
      refine ⟨fun k hk => ?_, fun k hk hk' => by omega, le_rfl⟩
      exact lt_of_le_of_lt (hmono (k + 1) (n + 1) (by omega) le_rfl) hn
    · have hf : ([n].filter fun i => decide (e (i + 1) < t)).length = 0 := by simp [hn]
      rw [hf, add_zero]
      refine ⟨h1, fun k hk hk' => ?_, by omega⟩
      rcases lt_or_ge k n with hkn | hkn
      · exact h2 k hk hkn
      · have : k = n := by omega
        subst this
        exact not_lt.mp hn

/-- The band edges as reals. -/
noncomputable def edgeR (k : ℕ) : ℝ := ((edges.getD k 0 : ℚ) : ℝ)

theorem edges_lt : ∀ k < 30, edges.getD k 0 < edges.getD (k + 1) 0 := by decide +kernel

theorem edgeR_mono : ∀ a b, a ≤ b → b ≤ 30 → edgeR a ≤ edgeR b := by
  intro a b hab hb
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    refine (ih (by omega)).trans ?_
    unfold edgeR
    exact_mod_cast (edges_lt n (by omega)).le

theorem edge0 : edgeR 0 = 1 / 3 := by unfold edgeR; norm_num [edges]
theorem edge30 : edgeR 30 = 7 / 3 := by unfold edgeR; norm_num [edges]

/-- **The band of an activity in range**: `bandOf t < 30` and `λ_i ≤ t ≤ λ_{i+1}`. -/
theorem bandOf_spec {t : ℝ} (ht : InRange t) :
    bandOf t < 30 ∧ edgeR (bandOf t) ≤ t ∧ t ≤ edgeR (bandOf t + 1) := by
  classical
  have hspec := count_lt_spec edgeR t 29 (fun a b hab hb => edgeR_mono a b hab (by omega))
  have hb : bandOf t = ((List.range 29).filter fun i => decide (edgeR (i + 1) < t)).length := by
    unfold bandOf edgeR
    congr
  rw [hb]
  obtain ⟨h1, h2, h3⟩ := hspec
  set c := ((List.range 29).filter fun i => decide (edgeR (i + 1) < t)).length
  refine ⟨by omega, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0, edge0]; exact ht.1
    · have := h1 (c - 1) (by omega)
      rw [show c - 1 + 1 = c by omega] at this
      exact this.le
  · rcases lt_or_ge c 29 with hlt | hge
    · exact h2 c le_rfl hlt
    · have : c = 29 := by omega
      rw [this, show 29 + 1 = 30 by rfl, edge30]; exact ht.2


/-! ## The band parameters are Profile30's -/

/-- `bandAt` (`Atlas/Params.lean`, core Lean) agrees with `Profile30`'s lists. -/
theorem bandAt_eq : ∀ i < 30,
    (bandAt i).D = Dt.getD i (8 / 5) ∧ (bandAt i).theta = θt.getD i 1 ∧
    (bandAt i).ell = rates.getD i [] ∧ (bandAt i).lamLo = edges.getD i 0 ∧
    (bandAt i).lamHi = edges.getD (i + 1) 0 ∧ (bandAt i).mmin = mmin.getD i 0 := by
  decide +kernel

theorem tvals_eq : Atlas.tvals = Profile30.tvals := by decide +kernel

theorem actQ_le_actQ {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : actQ a ≤ actQ b := by
  unfold actQ
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `actQ t ≤ qh < 1` gives `t ≤ qh/(1 − qh)`. -/
theorem le_lam_of_actQ_le {t qh : ℝ} (ht : 0 ≤ t) (hqh : qh < 1) (h : actQ t ≤ qh) :
    t ≤ qh / (1 - qh) := by
  unfold actQ at h
  rw [div_le_iff₀ (by linarith)] at h
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem edgeR_pos (k : ℕ) (hk : k ≤ 30) : 0 < edgeR k := by
  have := edgeR_mono 0 k (Nat.zero_le _) hk
  rw [edge0] at this
  linarith

/-! ## The tail functions -/

theorem min5_le (f : ℕ → ℝ) :
    min 1 (min (f 0) (min (f 1) (min (f 2) (min (f 3) (f 4))))) ≤ 1 ∧
      ∀ k < 5, min 1 (min (f 0) (min (f 1) (min (f 2) (min (f 3) (f 4))))) ≤ f k := by
  refine ⟨min_le_left _ _, fun k hk => ?_⟩
  interval_cases k <;> simp

/-- The lower-tail term with the **actual activity** `t` in the Laplace base:
`e^{−ℓ_j m} ((1 + t)/(1 + t t_j))^r` (the form proved by lane A3's `Tail.tail_t31`). -/
noncomputable def tailTermAct (t m : ℝ) (r j : ℕ) : ℝ :=
  Real.exp (-(ell t j * m)) * ((1 + t) / (1 + t * ((Profile30.tvals.getD j 0 : ℚ) : ℝ))) ^ r

/-- The lower-tail function with the actual activity:
`min(1, min_j e^{−ℓ_j m} ((1 + t)/(1 + t t_j))^r)`. -/
noncomputable def tailFnAct (t m : ℝ) (r : ℕ) : ℝ :=
  min 1 (min (tailTermAct t m r 0) (min (tailTermAct t m r 1) (min (tailTermAct t m r 2)
    (min (tailTermAct t m r 3) (tailTermAct t m r 4)))))

/-- **The certified profile with the actual-activity tail** (`Profile30.P` with `Tb := tailFnAct`;
the proposed replacement of `Profile30.tailFn`, whose band-edge base breaks 78 atlas boxes). -/
noncomputable def P30act : Profile := { Profile30.P with Tb := tailFnAct }

theorem ell_eq {t : ℝ} (hi : bandOf t < 30) (k : ℕ) :
    ell t k = (((bandAt (bandOf t)).ell.getD k 0 : ℚ) : ℝ) := by
  unfold ell
  rw [(bandAt_eq _ hi).2.2.1]

theorem tvals_getD (k : ℕ) : ((Profile30.tvals.getD k 0 : ℚ) : ℝ) = ((Atlas.tvals.getD k 0 : ℚ) : ℝ) := by
  rw [tvals_eq]

theorem tvals_mem (k : ℕ) (hk : k < 5) : 0 ≤ Atlas.tvals.getD k 0 ∧ Atlas.tvals.getD k 0 ≤ 1 := by
  interval_cases k <;> norm_num [Atlas.tvals]

/-- Profile30's tail function below the checker's band-edge bound. -/
theorem tailFn_le_edge {t : ℝ} (hi : bandOf t < 30) (m : ℝ) (r : ℕ) :
    tailFn t m r ≤ 1 ∧ ∀ k < 5, tailFn t m r ≤
      Real.exp (-((((bandAt (bandOf t)).ell.getD k 0 : ℚ) : ℝ) * m)) *
        ((1 + (((bandAt (bandOf t)).lamHi : ℚ) : ℝ)) /
          (1 + (((bandAt (bandOf t)).lamHi : ℚ) : ℝ) * ((Atlas.tvals.getD k 0 : ℚ) : ℝ))) ^ r := by
  obtain ⟨h1, h2⟩ := min5_le (fun k => tailTerm t m r k)
  refine ⟨h1, fun k hk => (h2 k hk).trans (le_of_eq ?_)⟩
  unfold tailTerm hiEdge
  rw [ell_eq hi, (bandAt_eq _ hi).2.2.2.2.1, tvals_getD]

/-- The actual-activity tail below the checker's bound for any base activity `Λ ≥ t`. -/
theorem tailFnAct_le {t : ℝ} (ht0 : 0 ≤ t) (hi : bandOf t < 30) {Λ : ℝ} (htΛ : t ≤ Λ) (m : ℝ)
    (r : ℕ) : tailFnAct t m r ≤ 1 ∧ ∀ k < 5, tailFnAct t m r ≤
      Real.exp (-((((bandAt (bandOf t)).ell.getD k 0 : ℚ) : ℝ) * m)) *
        ((1 + Λ) / (1 + Λ * ((Atlas.tvals.getD k 0 : ℚ) : ℝ))) ^ r := by
  obtain ⟨h1, h2⟩ := min5_le (fun k => tailTermAct t m r k)
  refine ⟨h1, fun k hk => (h2 k hk).trans ?_⟩
  unfold tailTermAct
  rw [ell_eq hi, tvals_getD]
  obtain ⟨hs0, hs1⟩ := tvals_mem k hk
  have hs0' : (0 : ℝ) ≤ ((Atlas.tvals.getD k 0 : ℚ) : ℝ) := by exact_mod_cast hs0
  have hs1' : ((Atlas.tvals.getD k 0 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hs1
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine pow_le_pow_left₀ (by positivity) ?_ r
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr htΛ) (sub_nonneg.mpr hs1')]

/-! ## One band of the certified profile -/

theorem bandOK_boxes {band : Band} {tl : Box → ℚ} {mcap : ℚ} {boxes : List Box} {slabs : List Slab}
    (h : bandOK band tl mcap boxes slabs = true) : ∀ b ∈ boxes, 0 < b.ql ∧ b.qh < 1 := by
  intro b hb
  unfold bandOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hb' := h.1.2 b hb
  unfold boxOK sane at hb'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hb'
  exact ⟨h0, h1⟩

/-- **A band passing with the band-edge tail base gives T1's explicit threshold** with Profile30's `θ`
and `D`, at every activity `t` of band `i` and every `m ∈ [B.mmin, mcap]`, for every tail function
`T ≤ min(1, e^{−ℓ_k m} ((1 + λ_{i+1})/(1 + λ_{i+1} t_k))^r)` (in particular `Profile30.tailFn`). -/
theorem edge_of_band {i : ℕ} (hi : i < 30) {B : Band} (hBD : B.D = (bandAt i).D)
    (hBθ : B.theta = (bandAt i).theta) (hBell : B.ell = (bandAt i).ell)
    (hBlo : B.lamLo = (bandAt i).lamLo) (hBhi : B.lamHi = (bandAt i).lamHi) {mcap : ℚ}
    {boxes : List Box} {slabs : List Slab}
    (hok : bandOK B (fun _ => (bandAt i).lamHi) mcap boxes slabs = true) {t : ℝ} (ht : InRange t)
    (hti : bandOf t = i) {m : ℝ} (hm : ((B.mmin : ℚ) : ℝ) ≤ m) (hm' : m ≤ mcap) (T : ℕ → ℝ)
    (hT1 : ∀ r, T r ≤ 1)
    (hT : ∀ r, ∀ k < 5, T r ≤ Real.exp (-((((bandAt i).ell.getD k 0 : ℚ) : ℝ) * m)) *
        ((1 + (((bandAt i).lamHi : ℚ) : ℝ)) / (1 + (((bandAt i).lamHi : ℚ) : ℝ) *
          ((Atlas.tvals.getD k 0 : ℚ) : ℝ))) ^ r) :
    ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) T (⌈m⌉₊ + 1) := by
  obtain ⟨-, hlo, hhi⟩ := bandOf_spec ht
  have hag := bandAt_eq i hi
  rw [hti] at hlo hhi
  have ht0 : 0 ≤ t := le_trans (edgeR_pos i (by omega)).le hlo
  have hθ : Profile30.P.θb t = ((B.theta : ℚ) : ℝ) := by
    show ((θt.getD (bandOf t) 1 : ℚ) : ℝ) = _; rw [hti, hBθ, hag.2.1]
  have hD : Profile30.P.Db t = ((B.D : ℚ) : ℝ) := by
    show ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ) = _; rw [hti, hBD, hag.1]
  rw [hθ, hD]
  refine band_explicitThreshold (band := B) hok ?_ ?_ hm hm' T hT1 ?_
  · rw [hBlo, hag.2.2.2.1]
    exact actQ_le_actQ (edgeR_pos i (by omega)).le hlo
  · rw [hBhi, hag.2.2.2.2.1]
    exact actQ_le_actQ ht0 hhi
  · intro _ _ _ _ r k hk
    rw [hBell]
    exact hT r k hk

/-- The tail bounds of Profile30's `tailFn` in the form `edge_of_band` consumes. -/
theorem tailFn_edge {t : ℝ} (hi : bandOf t < 30) (m : ℝ) :
    (∀ r, tailFn t m r ≤ 1) ∧ ∀ r, ∀ k < 5, tailFn t m r ≤
      Real.exp (-((((bandAt (bandOf t)).ell.getD k 0 : ℚ) : ℝ) * m)) *
        ((1 + (((bandAt (bandOf t)).lamHi : ℚ) : ℝ)) / (1 + (((bandAt (bandOf t)).lamHi : ℚ) : ℝ) *
          ((Atlas.tvals.getD k 0 : ℚ) : ℝ))) ^ r :=
  ⟨fun r => (tailFn_le_edge hi m r).1, fun r k hk => (tailFn_le_edge hi m r).2 k hk⟩

/-! ## The atlas statements from the band checks (arbitrary data) -/

/-- **The lower atlas (`m ≤ 50`) for `Profile30.P`**, from the 30 lower band checks (standard axioms). -/
theorem explicitThreshold_small_lower_P30_of_checks (boxes : ℕ → List Box) (slabs : ℕ → List Slab)
    (h : ∀ i < 30, bandOK (bandAt i) (fun _ => (bandAt i).lamHi) 50 (boxes i) (slabs i) = true) :
    ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m ≤ 50 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m) := by
  intro t ht m hm hm'
  have hi := (bandOf_spec ht).1
  have hfl : Profile30.P.mfloor t = (((bandAt (bandOf t)).mmin : ℚ) : ℝ) := by
    show ((mmin.getD (bandOf t) 0 : ℚ) : ℝ) = _; rw [(bandAt_eq _ hi).2.2.2.2.2]
  obtain ⟨h1, h2⟩ := tailFn_edge hi m
  exact edge_of_band hi rfl rfl rfl rfl rfl (h _ hi) ht rfl (by rw [← hfl]; exact hm)
    (by exact_mod_cast hm') (tailFn t m) h1 h2

/-- **The upper atlas (`50 ≤ m ≤ 400`) for `Profile30.P`**, from the 30 upper band checks (standard
axioms). -/
theorem explicitThreshold_small_upper_P30_of_checks (boxes : ℕ → List Box) (slabs : ℕ → List Slab)
    (h : ∀ i < 30, bandOK { bandAt i with mmin := 50 } (fun _ => (bandAt i).lamHi) 400 (boxes i)
      (slabs i) = true) :
    ∀ t, InRange t → ∀ m, 50 ≤ m → m ≤ 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m) := by
  intro t ht m hm hm'
  have hi := (bandOf_spec ht).1
  obtain ⟨h1, h2⟩ := tailFn_edge hi m
  exact edge_of_band (B := { bandAt (bandOf t) with mmin := 50 }) hi rfl rfl rfl rfl rfl (h _ hi) ht rfl
    (by push_cast; exact hm) (by exact_mod_cast hm') (tailFn t m) h1 h2

/-- **O4 on bounded `m` for `Profile30.P`** (the `hsmall` hypothesis of `thresholdNoValley_of_split`),
from the lower and upper band checks (standard axioms). -/
theorem explicitThreshold_small_P30_of_checks (lb : ℕ → List Box) (ls : ℕ → List Slab)
    (ub : ℕ → List Box) (us : ℕ → List Slab)
    (hl : ∀ i < 30, bandOK (bandAt i) (fun _ => (bandAt i).lamHi) 50 (lb i) (ls i) = true)
    (hu : ∀ i < 30, bandOK { bandAt i with mmin := 50 } (fun _ => (bandAt i).lamHi) 400 (ub i)
      (us i) = true) :
    ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m) := by
  intro t ht m hm hm'
  rcases le_total m 50 with h50 | h50
  · exact explicitThreshold_small_lower_P30_of_checks lb ls hl t ht m hm h50
  · exact explicitThreshold_small_upper_P30_of_checks ub us hu t ht m h50 hm'.le

/-- The profiles with Profile30's `θ`, `D`, `M1` and floor of `m`, and a tail function below the
actual-activity tail `tailFnAct` (which is below Profile30's `tailFn`), e.g. `P30act`. -/
def AtlasProfile (P : Profile) : Prop :=
  P.θb = Profile30.P.θb ∧ P.Db = Profile30.P.Db ∧ P.M1b = Profile30.P.M1b ∧
    P.mfloor = Profile30.P.mfloor ∧ ∀ t, InRange t → ∀ m r, P.Tb t m r ≤ tailFnAct t m r

theorem atlasProfile_P30act : AtlasProfile P30act := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => le_rfl⟩

/-- **O4 on bounded `m` for every `AtlasProfile`**, from the same band checks (standard axioms). -/
theorem explicitThreshold_small_of_checks (lb : ℕ → List Box) (ls : ℕ → List Slab)
    (ub : ℕ → List Box) (us : ℕ → List Slab)
    (hl : ∀ i < 30, bandOK (bandAt i) (fun _ => (bandAt i).lamHi) 50 (lb i) (ls i) = true)
    (hu : ∀ i < 30, bandOK { bandAt i with mmin := 50 } (fun _ => (bandAt i).lamHi) 400 (ub i)
      (us i) = true) {P : Profile} (hP : AtlasProfile P) :
    ∀ t, InRange t → ∀ m, P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P.θb t) (P.Db t) (P.Tb t m) (P.M1b t m) := by
  obtain ⟨hθ, hD, hM1, hfl, hT⟩ := hP
  intro t ht m hm hm'
  have hi := (bandOf_spec ht).1
  obtain ⟨-, hlo, hhi⟩ := bandOf_spec ht
  have ht0 : 0 ≤ t := le_trans (edgeR_pos _ (by omega)).le hlo
  have hle : t ≤ (((bandAt (bandOf t)).lamHi : ℚ) : ℝ) := by
    rw [(bandAt_eq _ hi).2.2.2.2.1]; exact hhi
  have htl := tailFnAct_le ht0 hi hle m
  rw [hθ, hD, hM1]
  rw [hfl] at hm
  have hT1 : ∀ r, P.Tb t m r ≤ 1 := fun r => (hT t ht m r).trans (htl r).1
  have hT2 := fun r k (hk : k < 5) => (hT t ht m r).trans ((htl r).2 k hk)
  rcases le_total m 50 with h50 | h50
  · have hfl' : Profile30.P.mfloor t = (((bandAt (bandOf t)).mmin : ℚ) : ℝ) := by
      show ((mmin.getD (bandOf t) 0 : ℚ) : ℝ) = _; rw [(bandAt_eq _ hi).2.2.2.2.2]
    exact edge_of_band hi rfl rfl rfl rfl rfl (hl _ hi) ht rfl (by rw [← hfl']; exact hm)
      (by exact_mod_cast h50) (P.Tb t m) hT1 hT2
  · exact edge_of_band (B := { bandAt (bandOf t) with mmin := 50 }) hi rfl rfl rfl rfl rfl (hu _ hi) ht
      rfl (by push_cast; exact h50) (by exact_mod_cast hm'.le) (P.Tb t m) hT1 hT2

end Erdos993Lean.Analytic.Atlas
