import Mathlib
import Erdos993Lean.Analytic.Atlas.Fibres

/-!
# The O4 atlas (lane A9): a passing box, cover and band give T1's explicit threshold

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A9).  Sources: Soul's `SOUL/O4/ATLAS_PROOF.md`
(the box theorem and the exact cover test), `SOUL/O4/atlas_arb.py` (`certify_box`, `cover_check`);
the interface `ExplicitThreshold` of `Erdos993Lean/Analytic/Defs.lean`.

The conversion of Soul's box theorem to the interface at a point `(q, m)` of the box: `ν = μ`, the same
`c`, Soul's `π(M) = α + β(M − m0) − γ(M − m0)²` re-centred at `m` (`d = m − m0`,
`α' = α + βd − γd² − ∑_{r ≥ M1} z_r`, `β' = β − 2γd`, `γ' = γ`), the fibre bound
`h(M) = π(M) − ∑_{r ≥ M} z_r` and the tail prices `S(M) = ∑_{M ≤ r < M1} z_r` (`M1 = ⌈m⌉ + 1`); the
dual prices `z_r` with `r ≥ M1` are paid at price 1 inside `α'`.  The strict threshold inequality is
Soul's expectation margin (2) (`marginQ > 0`), with the tail bound `T̂`.

## Results (namespace `Erdos993Lean.Analytic.Atlas`)

* **`box_explicitThreshold`**: a box passing `boxOK band Λ` gives `ExplicitThreshold q m θ D T (⌈m⌉ + 1)`
  at every `q ∈ [ql, qh]`, `m ∈ [ml, mh]`, for every `T ≤ min(1, e^{−ℓ_k m}((1 + Λ)/(1 + Λ t_k))^r)`.
* `chainOK_sound`, `slabsOK_sound`, **`coverOK_sound`**: the exact cover.
* **`band_explicitThreshold`**: a passing band gives the explicit threshold on
  `[q(λ_lo), q(λ_hi)] × [mmin, mcap]`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.Atlas

/-! ## Sound: from a passing box to T1's explicit threshold -/

theorem Box.tailSum_succ (b : Box) (M : ℕ) : b.tailSum M = b.z.getD M 0 + b.tailSum (M + 1) := by
  unfold Box.tailSum
  rcases lt_or_ge M b.z.length with h | h
  · rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]
    simp [sumList]
  · rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega), List.getD_eq_default _ _ h]
    simp [sumList]

theorem vmax_ge {b : Box} {q : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) :
    q * (1 - q) ≤ ((b.vmax : ℚ) : ℝ) := by
  unfold Box.vmax
  split_ifs with h
  · push_cast; nlinarith [sq_nonneg (q - 1 / 2)]
  · simp only [qmax_cast]
    push_cast
    push_neg at h
    by_cases hl : b.ql ≤ 1 / 2
    · have hh : b.qh < 1 / 2 := h hl
      have hh' : (b.qh : ℝ) < 1 / 2 := by
        have := (Rat.cast_lt (K := ℝ)).mpr hh; push_cast at this; linarith
      exact (by nlinarith : q * (1 - q) ≤ (b.qh : ℝ) * (1 - b.qh)).trans (le_max_right _ _)
    · push_neg at hl
      have hl' : (1 / 2 : ℝ) < b.ql := by
        have := (Rat.cast_lt (K := ℝ)).mpr hl; push_cast at this; linarith
      exact (by nlinarith : q * (1 - q) ≤ (b.ql : ℝ) * (1 - b.ql)).trans (le_max_left _ _)

/-- **A passing box gives T1's explicit threshold** at every `(q, m)` of the box, for every tail
function `T ≤ min(1, min_k e^{−ℓ_k m} ((1 + Λ)/(1 + Λ t_k))^r)`, with `M1 = ⌈m⌉ + 1`.
Construction: `ν = μ`, the same `c`, `π` re-centred at `m` (`α' = α + βd − γd² − ∑_{r ≥ M1} z_r`,
`β' = β − 2γd`, `d = m − m0`), `h(M) = π(M) − ∑_{r ≥ M} z_r` and `S(M) = ∑_{M ≤ r < M1} z_r`. -/
theorem box_explicitThreshold {band : Band} {Λ : ℚ} {b : Box}
    (hD : 0 ≤ band.D) (hθ : 0 ≤ band.theta) (hell : ∀ k < 5, 0 ≤ band.ell.getD k 0) (hΛ : 0 ≤ Λ)
    (hok : boxOK band Λ b = true) {q m : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh)
    (hm : (b.ml : ℝ) ≤ m) (hm' : m ≤ b.mh) (T : ℕ → ℝ) (hT1 : ∀ r, T r ≤ 1)
    (hT : ∀ r, ∀ k < 5, T r ≤ Real.exp (-(((band.ell.getD k 0 : ℚ) : ℝ) * m)) *
        ((1 + (Λ : ℝ)) / (1 + (Λ : ℝ) * ((tvals.getD k 0 : ℚ) : ℝ))) ^ r) :
    ExplicitThreshold q m (band.theta : ℝ) (band.D : ℝ) T (⌈m⌉₊ + 1) := by
  unfold boxOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hs, -⟩, ht⟩, hmargin⟩, hf⟩ := hok
  have hpt := box_pointwise hs ht hf
  have hs' := hs
  unfold sane at hs'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, hlh⟩, h1⟩, hmu⟩, hga⟩, hz⟩, hml0⟩, hmlh⟩, hcm⟩ := hs'
  set M1 := ⌈m⌉₊ + 1 with hM1
  set m0 : ℝ := ((b.m0 : ℚ) : ℝ) with hm0
  set d : ℝ := m - m0 with hd
  set tl : ℕ → ℝ := fun M => ((b.tailSum M : ℚ) : ℝ) with htl
  set zf : ℕ → ℝ := fun r => ((b.z.getD r 0 : ℚ) : ℝ) with hzf
  have htl_succ : ∀ M, tl M = zf M + tl (M + 1) := fun M => by
    simp only [htl, hzf]; rw [Box.tailSum_succ b M]; push_cast; ring
  have hzf0 : ∀ r, 0 ≤ zf r := fun r => by
    simp only [hzf]
    rcases lt_or_ge r b.z.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact_mod_cast hz _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; simp
  have htl_anti : ∀ M M', M ≤ M' → tl M' ≤ tl M := by
    intro M M' hMM
    induction M', hMM using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => linarith [htl_succ n, hzf0 n]
  have hmuR : (0 : ℝ) < b.mu := by exact_mod_cast hmu
  have hgaR : (0 : ℝ) < b.gamma := by exact_mod_cast hga
  have hpiR : ∀ M : ℕ, ((b.rhs M : ℚ) : ℝ) = (b.alpha : ℝ) + (b.beta : ℝ) * ((M : ℝ) - m0) -
      (b.gamma : ℝ) * ((M : ℝ) - m0) ^ 2 - tl M := fun M => by
    simp only [htl]; unfold Box.rhs; push_cast; rw [Box.piQ_cast]
  refine ⟨b.mu, b.c, (b.alpha : ℝ) + (b.beta : ℝ) * d - (b.gamma : ℝ) * d ^ 2 - tl M1,
    (b.beta : ℝ) - 2 * (b.gamma : ℝ) * d, b.gamma, fun M => ((b.rhs M : ℚ) : ℝ),
    fun M => tl M - tl M1, hmuR, hgaR.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M j
    exact hpt M q hq hq' j
  · intro M hM
    dsimp only
    rw [hpiR M]
    have h2 := htl_anti M1 M hM
    have key : (b.alpha : ℝ) + (b.beta : ℝ) * ((M : ℝ) - m0) - (b.gamma : ℝ) * ((M : ℝ) - m0) ^ 2 - tl M -
        ((b.alpha : ℝ) + (b.beta : ℝ) * d - (b.gamma : ℝ) * d ^ 2 - tl M1 +
          ((b.beta : ℝ) - 2 * (b.gamma : ℝ) * d) * ((M : ℝ) - m) - (b.gamma : ℝ) * ((M : ℝ) - m) ^ 2) =
        tl M1 - tl M := by rw [hd]; ring
    linarith only [key, h2]
  · intro M _
    dsimp only
    rw [hpiR M]
    have e : (M : ℝ) - m0 = ((M : ℝ) - m) + d := by rw [hd]; ring
    rw [e]
    ring_nf
    exact le_refl _
  · intro M hM
    have := htl_anti M M1 hM.le
    linarith
  · intro M _
    have := htl_succ M
    have := hzf0 M
    linarith
  · -- the strict threshold inequality
    rw [abel_tail zf tl T htl_succ M1]
    have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by exact_mod_cast hml0) hm
    -- the margin, cast to ℝ
    have hmarg : (0 : ℝ) < ((marginQ band Λ b : ℚ) : ℝ) := by exact_mod_cast hmargin
    unfold marginQ at hmarg
    push_cast at hmarg
    simp only [qmin_cast, qmax_cast] at hmarg
    push_cast at hmarg
    -- the cost dominates the prices
    set U := uList band b.ml
    have hcost : ((costFrom U Λ b.cm 0 b.z : ℚ) : ℝ) =
        ∑ r ∈ Finset.range (b.z.length + M1), zf r * (((if r ≤ b.cm then tailHat U Λ r else 1 : ℚ) : ℝ)) := by
      rw [costFrom_eq, sum_range_extend b.z _ (Nat.le_add_right b.z.length M1)]
      push_cast
      simp only [zero_add, hzf]
    have htlK : tl M1 = ∑ r ∈ Finset.range (b.z.length + M1), (if M1 ≤ r then zf r else 0) := by
      simp only [htl, hzf]
      unfold Box.tailSum
      rw [sumList_drop_eq, Rat.cast_sum]
      simp only [apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_zero]
      refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_add_right b.z.length M1))
        fun i _ hi => ?_
      rw [Finset.mem_range, not_lt] at hi
      rw [List.getD_eq_default _ _ hi]
      simp
    have hsumK : ∑ r ∈ Finset.range M1, zf r * T r =
        ∑ r ∈ Finset.range (b.z.length + M1), (if r < M1 then zf r * T r else 0) := by
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left M1 b.z.length)]
      have e1 : ∑ r ∈ Finset.range M1, (if r < M1 then zf r * T r else 0) = ∑ r ∈ Finset.range M1, zf r * T r :=
        Finset.sum_congr rfl fun r hr => if_pos (Finset.mem_range.mp hr)
      have e2 : ∑ r ∈ Finset.Ico M1 (b.z.length + M1), (if r < M1 then zf r * T r else 0) = 0 :=
        Finset.sum_eq_zero fun r hr => if_neg (not_lt.mpr (Finset.mem_Ico.mp hr).1)
      rw [e1, e2, add_zero]
    have hcmM1 : b.cm < M1 := by
      have h2 : ((b.cm : ℚ) : ℝ) < (b.ml : ℝ) + 1 := by exact_mod_cast hcm
      have h3 : m ≤ (⌈m⌉₊ : ℝ) := Nat.le_ceil m
      have h4 : (b.cm : ℝ) < (⌈m⌉₊ : ℝ) + 1 := by push_cast at h2; linarith
      have h5 : b.cm < ⌈m⌉₊ + 1 := by exact_mod_cast h4
      rw [hM1]
      exact h5
    have hterm : ∀ r ∈ Finset.range (b.z.length + M1), (if r < M1 then zf r * T r else 0) + (if M1 ≤ r then zf r else 0) ≤
        zf r * (((if r ≤ b.cm then tailHat U Λ r else 1 : ℚ) : ℝ)) := by
      intro r _
      by_cases hr : r < M1
      · rw [if_pos hr, if_neg (by omega), add_zero]
        refine mul_le_mul_of_nonneg_left ?_ (hzf0 r)
        split_ifs with hrc
        · refine tailHat_ge (hT1 r) fun k hk => ?_
          rw [uList_getD band b.ml hk]
          push_cast
          have hU := exp_neg_le_expNegUpper (x := band.ell.getD k 0 * b.ml)
            (mul_nonneg (hell k hk) (by exact_mod_cast hml0.le))
          have hlk : (0 : ℝ) ≤ ((band.ell.getD k 0 : ℚ) : ℝ) := by exact_mod_cast hell k hk
          have hexp : Real.exp (-(((band.ell.getD k 0 : ℚ) : ℝ) * m)) ≤
              Real.exp (-(((band.ell.getD k 0 * b.ml : ℚ) : ℝ))) := by
            apply Real.exp_le_exp.mpr
            push_cast
            nlinarith
          have hbase : (0 : ℝ) ≤ ((1 + (Λ : ℝ)) / (1 + (Λ : ℝ) * ((tvals.getD k 0 : ℚ) : ℝ))) ^ r := by
            have hΛR : (0 : ℝ) ≤ Λ := by exact_mod_cast hΛ
            have htk : (0 : ℝ) ≤ ((tvals.getD k 0 : ℚ) : ℝ) := by
              have : 0 ≤ tvals.getD k 0 := by
                interval_cases k <;> norm_num [tvals]
              exact_mod_cast this
            positivity
          calc T r ≤ Real.exp (-(((band.ell.getD k 0 : ℚ) : ℝ) * m)) *
                ((1 + (Λ : ℝ)) / (1 + (Λ : ℝ) * ((tvals.getD k 0 : ℚ) : ℝ))) ^ r := hT r k hk
            _ ≤ ((expNegUpper (band.ell.getD k 0 * b.ml) : ℚ) : ℝ) *
                ((1 + (Λ : ℝ)) / (1 + (Λ : ℝ) * ((tvals.getD k 0 : ℚ) : ℝ))) ^ r :=
              mul_le_mul_of_nonneg_right (hexp.trans hU) hbase
        · push_cast; exact hT1 r
      · rw [if_neg hr, if_pos (by omega), zero_add, if_neg (by omega)]
        push_cast
        rw [mul_one]
    have hsum_le : ∑ r ∈ Finset.range M1, zf r * T r + tl M1 ≤ ((costFrom U Λ b.cm 0 b.z : ℚ) : ℝ) := by
      rw [hsumK, htlK, hcost, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hterm
    -- the moments
    have hdl : (b.ml : ℝ) - m0 ≤ d := by rw [hd]; linarith
    have hdh : d ≤ (b.mh : ℝ) - m0 := by rw [hd]; linarith
    have hlin : min ((b.beta : ℝ) * ((b.ml : ℝ) - m0)) ((b.beta : ℝ) * ((b.mh : ℝ) - m0)) ≤ (b.beta : ℝ) * d := by
      rcases le_total 0 (b.beta : ℝ) with hb | hb
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hdl hb)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hdh hb)
    have hsq : d ^ 2 ≤ max (((b.ml : ℝ) - m0) * ((b.ml : ℝ) - m0)) (((b.mh : ℝ) - m0) * ((b.mh : ℝ) - m0)) := by
      rcases le_total 0 d with hd0 | hd0
      · exact (by nlinarith : d ^ 2 ≤ ((b.mh : ℝ) - m0) * ((b.mh : ℝ) - m0)).trans (le_max_right _ _)
      · exact (by nlinarith : d ^ 2 ≤ ((b.ml : ℝ) - m0) * ((b.ml : ℝ) - m0)).trans (le_max_left _ _)
    have hDR : (0 : ℝ) ≤ band.D := by exact_mod_cast hD
    have hθR : (0 : ℝ) ≤ band.theta := by exact_mod_cast hθ
    have hv := vmax_ge (b := b) hq hq'
    have hq0 : 0 ≤ q * (1 - q) := by
      have : (0 : ℝ) < b.ql := by exact_mod_cast h0
      have : (b.qh : ℝ) < 1 := by exact_mod_cast h1
      nlinarith
    have hvm : q * (1 - q) * m ≤ ((b.vmax : ℚ) : ℝ) * b.mh :=
      mul_le_mul hv hm' hmR.le (hq0.trans hv)
    have hmuθ : 0 ≤ (b.mu : ℝ) * (band.theta : ℝ) := mul_nonneg hmuR.le hθR
    have hγD : (b.gamma : ℝ) * (band.D : ℝ) * m ≤ (b.gamma : ℝ) * (band.D : ℝ) * b.mh :=
      mul_le_mul_of_nonneg_left hm' (mul_nonneg hgaR.le hDR)
    have hγsq := mul_le_mul_of_nonneg_left hsq hgaR.le
    have key1 : (b.mu : ℝ) * (band.theta : ℝ) * (q * (1 - q)) * m ≤
        (b.mu : ℝ) * (band.theta : ℝ) * ((b.vmax : ℚ) : ℝ) * (b.mh : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hvm hmuθ
      calc (b.mu : ℝ) * (band.theta : ℝ) * (q * (1 - q)) * m
          = (b.mu : ℝ) * (band.theta : ℝ) * (q * (1 - q) * m) := by ring
        _ ≤ (b.mu : ℝ) * (band.theta : ℝ) * (((b.vmax : ℚ) : ℝ) * (b.mh : ℝ)) := h
        _ = (b.mu : ℝ) * (band.theta : ℝ) * ((b.vmax : ℚ) : ℝ) * (b.mh : ℝ) := by ring
    have hγD' : (b.gamma : ℝ) * ((band.D : ℝ) * m) ≤ (b.gamma : ℝ) * ((band.D : ℝ) * (b.mh : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm' hDR) hgaR.le
    rw [mul_add] at hmarg
    have e1 : (b.gamma : ℝ) * (band.D : ℝ) * m = (b.gamma : ℝ) * ((band.D : ℝ) * m) := by ring
    rw [e1]
    linarith only [hmarg, hlin, hγsq, hγD', key1, hsum_le]

/-! ## Sound: the cover -/

theorem chainOK_sound {boxes : List Box} {lo hi : ℚ} : ∀ (chain : List ℕ) (s target : ℚ),
    chainOK boxes lo hi s target chain = true → ∀ m : ℝ, (s : ℝ) ≤ m → m ≤ (target : ℝ) →
      ∃ b ∈ boxes, b.ql ≤ lo ∧ hi ≤ b.qh ∧ (b.ml : ℝ) ≤ m ∧ m ≤ (b.mh : ℝ) := by
  intro chain
  induction chain with
  | nil => intro s target h; simp [chainOK] at h
  | cons i rest ih =>
    intro s target h m hsm hmt
    unfold chainOK at h
    split at h
    · rename_i b hb
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hql, hqh⟩, hml⟩, hrest⟩ := h
      have hbmem : b ∈ boxes := List.mem_of_getElem? hb
      have hml' : (b.ml : ℝ) ≤ s := by exact_mod_cast hml
      by_cases hmb : m ≤ (b.mh : ℝ)
      · exact ⟨b, hbmem, hql, hqh, hml'.trans hsm, hmb⟩
      · push_neg at hmb
        rcases hrest with htb | hr
        · have : (target : ℝ) ≤ b.mh := by exact_mod_cast htb
          linarith
        · exact ih b.mh target hr m hmb.le hmt
    · simp at h

theorem slabsOK_sound {boxes : List Box} {qhi mlo mhi : ℚ} : ∀ (slabs : List Slab) (start : ℚ),
    slabsOK boxes qhi mlo mhi start slabs = true → ∀ q : ℝ, (start : ℝ) ≤ q → q ≤ (qhi : ℝ) →
      ∀ m : ℝ, (mlo : ℝ) ≤ m → m ≤ (mhi : ℝ) →
        ∃ b ∈ boxes, (b.ql : ℝ) ≤ q ∧ q ≤ b.qh ∧ (b.ml : ℝ) ≤ m ∧ m ≤ b.mh := by
  intro slabs
  induction slabs with
  | nil => intro start h; simp [slabsOK] at h
  | cons sl rest ih =>
    intro start h q hsq hqq m hm hm'
    unfold slabsOK at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlo, hch⟩, hrest⟩ := h
    have hlo' : (sl.lo : ℝ) ≤ start := by exact_mod_cast hlo
    by_cases hqs : q ≤ (sl.hi : ℝ)
    · obtain ⟨b, hb, hql, hqh, hbm, hbm'⟩ := chainOK_sound sl.chain mlo mhi hch m hm hm'
      have hql' : (b.ql : ℝ) ≤ sl.lo := by exact_mod_cast hql
      have hqh' : (sl.hi : ℝ) ≤ b.qh := by exact_mod_cast hqh
      exact ⟨b, hb, by linarith, by linarith, hbm, hbm'⟩
    · push_neg at hqs
      rcases hrest with hqh | hr
      · have : (qhi : ℝ) ≤ sl.hi := by exact_mod_cast hqh
        linarith
      · exact ih sl.hi hr q hqs.le hqq m hm hm'

/-- **The cover**: a passing `coverOK` covers `[qlo, qhi] × [mlo, mhi]` by the boxes. -/
theorem coverOK_sound {boxes : List Box} {qlo qhi mlo mhi : ℚ} {slabs : List Slab}
    (h : coverOK boxes qlo qhi mlo mhi slabs = true) {q m : ℝ} (hq : (qlo : ℝ) ≤ q) (hq' : q ≤ qhi)
    (hm : (mlo : ℝ) ≤ m) (hm' : m ≤ mhi) :
    ∃ b ∈ boxes, (b.ql : ℝ) ≤ q ∧ q ≤ b.qh ∧ (b.ml : ℝ) ≤ m ∧ m ≤ b.mh :=
  slabsOK_sound slabs qlo h q hq hq' m hm hm'

/-! ## Sound: one band -/

theorem actQQ_cast (lam : ℚ) : ((actQQ lam : ℚ) : ℝ) = actQ (lam : ℝ) := by
  unfold actQQ actQ; push_cast; ring

/-- **A passing band gives T1's explicit threshold** at every `q ∈ [q(λ_lo), q(λ_hi)]` and
`m ∈ [mmin, mcap]`, for every tail function `T ≤ 1` below `e^{−ℓ_k m} ((1 + Λ_b)/(1 + Λ_b t_k))^r`
for the tail base `Λ_b = tailLam b` of every box `b` containing `q`. -/
theorem band_explicitThreshold {band : Band} {tailLam : Box → ℚ} {mcap : ℚ} {boxes : List Box}
    {slabs : List Slab} (hok : bandOK band tailLam mcap boxes slabs = true) {q m : ℝ}
    (hq : actQ (band.lamLo : ℝ) ≤ q) (hq' : q ≤ actQ (band.lamHi : ℝ)) (hm : (band.mmin : ℝ) ≤ m)
    (hm' : m ≤ mcap) (T : ℕ → ℝ) (hT1 : ∀ r, T r ≤ 1)
    (hT : ∀ b ∈ boxes, (b.ql : ℝ) ≤ q → q ≤ b.qh → ∀ r, ∀ k < 5,
      T r ≤ Real.exp (-(((band.ell.getD k 0 : ℚ) : ℝ) * m)) *
        ((1 + ((tailLam b : ℚ) : ℝ)) / (1 + ((tailLam b : ℚ) : ℝ) * ((tvals.getD k 0 : ℚ) : ℝ))) ^ r) :
    ExplicitThreshold q m (band.theta : ℝ) (band.D : ℝ) T (⌈m⌉₊ + 1) := by
  unfold bandOK at hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hbs, hboxes⟩, hcov⟩ := hok
  unfold bandSane at hbs
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hbs
  obtain ⟨⟨hD, hθ⟩, hell⟩ := hbs
  obtain ⟨b, hb, hbq, hbq', hbm, hbm'⟩ :=
    coverOK_sound (q := q) (m := m) hcov (by rw [actQQ_cast]; exact hq) (by rw [actQQ_cast]; exact hq')
      hm hm'
  have hbok := hboxes b hb
  have hΛ : 0 ≤ tailLam b := by
    unfold boxOK at hbok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbok
    obtain ⟨⟨⟨⟨_, h⟩, _⟩, _⟩, _⟩ := hbok
    exact h
  exact box_explicitThreshold hD hθ hell hΛ hbok hbq hbq' hbm hbm' T hT1 (hT b hb hbq hbq')

end Erdos993Lean.Analytic.Atlas
