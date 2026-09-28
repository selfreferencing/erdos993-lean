import Erdos993Lean.Analytic.Density.Partition

/-!
# Paths: the hard-core sums of `P_j` and the path density bound

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A8 (open object O5).  Source: Soul's
`SOUL/RESULTS/O5.md` §3 "Paths" (the closed form of the path partition function and its mean).

* `zP x j`, `sP x j`: `Z(P_j)` and `S(P_j)` at activity `x`, by the recursions
  `Z_{j+2} = Z_{j+1} + x Z_j`, `S_{j+2} = S_{j+1} + x (S_j + Z_j)`.
* `IsPathSet G s` (connected, all degrees `≤ 2`) and **`IsPathSet.values`**: inside a forest,
  `Z(s) = zP x |s|` and `S(s) = sP x |s|` (delete a leaf and its neighbour).
* The closed forms (`zP_sP_closed`), with `s = √(1 + 4x)`, `a, b = (1 ± s)/2`, `N = j + 2`,
  `ρ = (s − 1)/(2s)` and `c∞ = (1 + 2x − s)/s²`:
  `Z_j = (a^N − b^N)/s` and `S_j = (ρ j + c∞) Z_j − N b^N / s²`.
* **`path_tail`**: `S_j ≥ (r j + c) Z_j` for all `j + 2 ≥ N₀`, given `r ≤ ρ`
  (`(1 − 2r)² (1 + 4x) ≥ 1`), `x ≤ 2` (so `a ≥ 2|b|`), rational enclosures `s_L ≤ s ≤ s_H`, and
  `K (c_L − c) s_L ≥ 1`, `K N₀ + 1 ≤ 2^{N₀}` with `c_L = (1 + 2x − s_H)/(1 + 4x) ≤ c∞`.  For odd `N`
  the error term has the good sign; for even `N` it is at most `N |b|^N / s²` and `a^N ≥ 2^N |b|^N`.
  (Soul's argument uses the decay `(4/3) t² < 1` of the even errors instead; same content.)
-/

namespace Erdos993Lean.Analytic.Density

open Finset Erdos993Lean.Occupation

/-! ## The path sums -/

/-- `Z(P_j)` at activity `x`. -/
def zP (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => 1 + x
  | j + 2 => zP x (j + 1) + x * zP x j

/-- `S(P_j) = Σ_{t indep} |t| x^|t|` for the path `P_j`. -/
def sP (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => x
  | j + 2 => sP x (j + 1) + x * (sP x j + zP x j)

theorem zP_succ_succ (x : ℚ) (j : ℕ) : zP x (j + 2) = zP x (j + 1) + x * zP x j := rfl

theorem sP_succ_succ (x : ℚ) (j : ℕ) : sP x (j + 2) = sP x (j + 1) + x * (sP x j + zP x j) := rfl

theorem zP_pos {x : ℚ} (hx : 0 ≤ x) : ∀ j, 0 < zP x j
  | 0 => by simp [zP]
  | 1 => by simp [zP]; linarith
  | j + 2 => by
    rw [zP_succ_succ]
    have h1 := zP_pos hx (j + 1)
    have h2 := zP_pos hx j
    positivity

/-! ## Path sets inside a forest -/

section PathSets

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- A path set: connected, all degrees at most `2`. -/
def IsPathSet (s : Finset V) : Prop := ConnectedIn G s ∧ ∀ v ∈ s, (nbrsIn G s v).card ≤ 2

/-- Deleting a vertex of degree at most one from a path set leaves a path set. -/
theorem IsPathSet.erase {s : Finset V} (hs : IsPathSet G s) {ℓ : V} (hℓ : ℓ ∈ s)
    (hdeg : (nbrsIn G s ℓ).card ≤ 1) : IsPathSet G (s.erase ℓ) :=
  ⟨connectedIn_erase_of_card_le_one hs.1 hℓ hdeg, fun v hv =>
    (Finset.card_le_card (nbrsIn_mono (Finset.erase_subset ℓ s) v)).trans
      (hs.2 v (Finset.mem_of_mem_erase hv))⟩

/-- A connected set with at most three vertices is a path set. -/
theorem isPathSet_of_card_le_three {s : Finset V} (hs : ConnectedIn G s) (h3 : s.card ≤ 3) :
    IsPathSet G s :=
  ⟨hs, fun v hv => by have := card_nbrsIn_lt (G := G) hv; omega⟩

/-- **The hard-core sums of a path set**: `Z(s) = zP x |s|`, `S(s) = sP x |s|`. -/
theorem IsPathSet.values (hG : G.IsAcyclic) (x : ℚ) :
    ∀ s : Finset V, IsPathSet G s → Zx G x s = zP x s.card ∧ Sx G x s = sP x s.card := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs
    rcases Nat.lt_or_ge s.card 2 with h2 | h2
    · rcases Nat.lt_or_ge s.card 1 with h1 | h1
      · have hs0 : s = ∅ := Finset.card_eq_zero.mp (by omega)
        subst hs0
        simp [Zx_empty, Sx_empty, zP, sP]
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
        simp [Zx_singleton, Sx_singleton, zP, sP]
    · obtain ⟨ℓ, hℓ, a, ha⟩ := exists_leaf hG hs.1 h2
      have haN : a ∈ nbrsIn G s ℓ := by rw [ha]; exact Finset.mem_singleton_self a
      have has : a ∈ s := (mem_nbrsIn.mp haN).1
      have haℓ : a ≠ ℓ := (G.ne_of_adj (mem_nbrsIn.mp haN).2).symm
      have ha' : a ∈ s.erase ℓ := Finset.mem_erase.mpr ⟨haℓ, has⟩
      have hs1 : IsPathSet G (s.erase ℓ) := hs.erase hℓ (by rw [ha, Finset.card_singleton])
      have hdeg : (nbrsIn G (s.erase ℓ) a).card ≤ 1 := by
        rw [nbrsIn_erase]
        have hℓa : ℓ ∈ nbrsIn G s a := mem_nbrsIn.mpr ⟨hℓ, (mem_nbrsIn.mp haN).2.symm⟩
        rw [Finset.card_erase_of_mem hℓa]
        have := hs.2 a has
        omega
      have hs2 : IsPathSet G ((s.erase ℓ).erase a) := hs1.erase ha' hdeg
      have hout : outsideClosedNbhd G s ℓ = (s.erase ℓ).erase a := by
        rw [outsideClosedNbhd_eq, ha, Finset.sdiff_singleton_eq_erase]
      have hZ : Zx G x s = Zx G x (s.erase ℓ) + x * Zx G x ((s.erase ℓ).erase a) := by
        rw [Zx_erase G x hℓ, hout]
      have hS : Sx G x s = Sx G x (s.erase ℓ) +
          x * (Zx G x ((s.erase ℓ).erase a) + Sx G x ((s.erase ℓ).erase a)) := by
        rw [Sx_erase G x hℓ, hout]
      obtain ⟨h1Z, h1S⟩ := ih _ (Finset.erase_ssubset hℓ) hs1
      obtain ⟨h2Z, h2S⟩ := ih _ ((Finset.erase_ssubset ha').trans (Finset.erase_ssubset hℓ)) hs2
      have hc1 : (s.erase ℓ).card + 1 = s.card := Finset.card_erase_add_one hℓ
      have hc2 : ((s.erase ℓ).erase a).card + 1 = (s.erase ℓ).card := Finset.card_erase_add_one ha'
      obtain ⟨j, hj⟩ : ∃ j, s.card = j + 2 := ⟨s.card - 2, by omega⟩
      have e1 : (s.erase ℓ).card = j + 1 := by omega
      have e2 : ((s.erase ℓ).erase a).card = j := by omega
      rw [hZ, hS, h1Z, h1S, h2Z, h2S, hj, e1, e2, zP_succ_succ, sP_succ_succ]
      exact ⟨rfl, by ring⟩

/-- The surplus of a path set with `j` vertices. -/
theorem IsPathSet.Phi_eq (hG : G.IsAcyclic) (x r c : ℚ) {s : Finset V} (hs : IsPathSet G s) :
    Phi G x r c s = sP x s.card - (r * s.card + c) * zP x s.card := by
  obtain ⟨hZ, hS⟩ := IsPathSet.values hG x s hs
  unfold Phi
  rw [hZ, hS]

end PathSets

/-! ## The closed forms -/

section Closed

variable (x : ℚ) {s : ℝ}

/-- The closed form of `Z(P_j)`. -/
noncomputable def zPc (s : ℝ) (j : ℕ) : ℝ := (((1 + s) / 2) ^ (j + 2) - ((1 - s) / 2) ^ (j + 2)) / s

/-- The closed form of `S(P_j)`: `(ρ j + c∞) Z_j − N b^N / s²`. -/
noncomputable def sPc (s : ℝ) (j : ℕ) : ℝ :=
  ((s - 1) / (2 * s) * j + (1 + 2 * (x : ℝ) - s) / s ^ 2) * zPc s j -
    (j + 2) * ((1 - s) / 2) ^ (j + 2) / s ^ 2

theorem zPc_alg (s A B : ℝ) (hs0 : s ≠ 0) :
    (((1 + s) / 2) ^ 2 * A - ((1 - s) / 2) ^ 2 * B) / s =
      (((1 + s) / 2) * A - ((1 - s) / 2) * B) / s + (s ^ 2 - 1) / 4 * ((A - B) / s) := by
  field_simp
  ring

theorem sPc_alg (s A B J : ℝ) (hs0 : s ≠ 0) :
    ((s - 1) / (2 * s) * (J + 2) + (1 + 2 * ((s ^ 2 - 1) / 4) - s) / s ^ 2) *
        ((((1 + s) / 2) ^ 2 * A - ((1 - s) / 2) ^ 2 * B) / s) -
      (J + 2 + 2) * (((1 - s) / 2) ^ 2 * B) / s ^ 2 =
    (((s - 1) / (2 * s) * (J + 1) + (1 + 2 * ((s ^ 2 - 1) / 4) - s) / s ^ 2) *
        ((((1 + s) / 2) * A - ((1 - s) / 2) * B) / s) -
      (J + 1 + 2) * (((1 - s) / 2) * B) / s ^ 2) +
    (s ^ 2 - 1) / 4 * ((((s - 1) / (2 * s) * J + (1 + 2 * ((s ^ 2 - 1) / 4) - s) / s ^ 2) *
        ((A - B) / s) - (J + 2) * B / s ^ 2) + (A - B) / s) := by
  field_simp
  ring

theorem zPc_rec (hs : s ^ 2 = 1 + 4 * (x : ℝ)) (hs0 : s ≠ 0) (j : ℕ) :
    zPc s (j + 2) = zPc s (j + 1) + (x : ℝ) * zPc s j := by
  have hx : (x : ℝ) = (s ^ 2 - 1) / 4 := by linarith
  have e1 : ∀ c : ℝ, c ^ (j + 2 + 2) = c ^ 2 * c ^ (j + 2) := fun c => by ring
  have e2 : ∀ c : ℝ, c ^ (j + 1 + 2) = c * c ^ (j + 2) := fun c => by ring
  unfold zPc
  rw [hx, e1, e1, e2, e2]
  exact zPc_alg s _ _ hs0

theorem sPc_rec (hs : s ^ 2 = 1 + 4 * (x : ℝ)) (hs0 : s ≠ 0) (j : ℕ) :
    sPc x s (j + 2) = sPc x s (j + 1) + (x : ℝ) * (sPc x s j + zPc s j) := by
  have hx : (x : ℝ) = (s ^ 2 - 1) / 4 := by linarith
  have e1 : ∀ c : ℝ, c ^ (j + 2 + 2) = c ^ 2 * c ^ (j + 2) := fun c => by ring
  have e2 : ∀ c : ℝ, c ^ (j + 1 + 2) = c * c ^ (j + 2) := fun c => by ring
  unfold sPc zPc
  rw [hx, e1, e1, e2, e2]
  push_cast
  exact sPc_alg s _ _ (j : ℝ) hs0

theorem closed_base (hs : s ^ 2 = 1 + 4 * (x : ℝ)) (hs0 : s ≠ 0) :
    ((zP x 0 : ℚ) : ℝ) = zPc s 0 ∧ ((sP x 0 : ℚ) : ℝ) = sPc x s 0 ∧
    ((zP x 1 : ℚ) : ℝ) = zPc s 1 ∧ ((sP x 1 : ℚ) : ℝ) = sPc x s 1 := by
  have hx : (x : ℝ) = (s ^ 2 - 1) / 4 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : zPc s 0 = 1 := by unfold zPc; field_simp; ring
    rw [this]; simp [zP]
  · have : sPc x s 0 = 0 := by unfold sPc zPc; rw [hx]; push_cast; field_simp; ring
    rw [this]; simp [sP]
  · have : zPc s 1 = 1 + (x : ℝ) := by unfold zPc; rw [hx]; field_simp; ring
    rw [this]; simp [zP]
  · have : sPc x s 1 = (x : ℝ) := by unfold sPc zPc; rw [hx]; push_cast; field_simp; ring
    rw [this]; simp [sP]

/-- **The closed forms of the path sums.** -/
theorem zP_sP_closed (hs : s ^ 2 = 1 + 4 * (x : ℝ)) (hs0 : s ≠ 0) :
    ∀ j, ((zP x j : ℚ) : ℝ) = zPc s j ∧ ((sP x j : ℚ) : ℝ) = sPc x s j := by
  have key : ∀ j, (((zP x j : ℚ) : ℝ) = zPc s j ∧ ((sP x j : ℚ) : ℝ) = sPc x s j) ∧
      (((zP x (j + 1) : ℚ) : ℝ) = zPc s (j + 1) ∧ ((sP x (j + 1) : ℚ) : ℝ) = sPc x s (j + 1)) := by
    intro j
    induction j with
    | zero =>
      obtain ⟨h1, h2, h3, h4⟩ := closed_base x hs hs0
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    | succ j ih =>
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ih
      refine ⟨⟨h3, h4⟩, ?_, ?_⟩
      · rw [show j + 1 + 1 = j + 2 by ring, zP_succ_succ, zPc_rec x hs hs0]
        push_cast
        rw [h1, h3]
      · rw [show j + 1 + 1 = j + 2 by ring, sP_succ_succ, sPc_rec x hs hs0]
        push_cast
        rw [h1, h2, h4]
  exact fun j => (key j).1

end Closed

/-! ## The tail of the path bound -/

theorem two_pow_ge {K : ℚ} (hK : 0 ≤ K) {N0 : ℕ} (hN01 : 1 ≤ N0) (hN0 : K * N0 + 1 ≤ 2 ^ N0) :
    ∀ N, N0 ≤ N → K * N + 1 ≤ 2 ^ N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hN0
  | succ N hN ih =>
    have hN1 : (1 : ℚ) ≤ N := by exact_mod_cast hN01.trans hN
    push_cast
    rw [pow_succ]
    nlinarith

/-- **The path bound for long paths** (see the module docstring). -/
theorem path_tail (x r c sH sL K : ℚ) (N0 : ℕ) (hx : 0 < x) (hx2 : x ≤ 2) (hr2 : 2 * r < 1)
    (hρ : 1 ≤ (1 - 2 * r) ^ 2 * (1 + 4 * x)) (hsH : 0 ≤ sH)
    (hsH2 : 1 + 4 * x ≤ sH ^ 2) (hsL : 0 ≤ sL) (hsL2 : sL ^ 2 ≤ 1 + 4 * x) (hK : 0 ≤ K)
    (hKc : 1 ≤ K * ((1 + 2 * x - sH) / (1 + 4 * x) - c) * sL) (hN01 : 1 ≤ N0)
    (hN0 : K * N0 + 1 ≤ 2 ^ N0) (j : ℕ) (hj : N0 ≤ j + 2) :
    (r * j + c) * zP x j ≤ sP x j := by
  -- work in `ℝ`
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  set s := Real.sqrt (1 + 4 * (x : ℝ)) with hsdef
  have h14 : (0 : ℝ) ≤ 1 + 4 * (x : ℝ) := by linarith
  have hs2 : s ^ 2 = 1 + 4 * (x : ℝ) := Real.sq_sqrt h14
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  clear_value s
  have hs1 : 1 ≤ s := by nlinarith
  have hs3 : s ≤ 3 := by
    have : (x : ℝ) ≤ 2 := by exact_mod_cast hx2
    nlinarith
  have hsne : s ≠ 0 := by linarith
  have hsHR : s ≤ (sH : ℝ) := by
    have h1 : (1 + 4 * (x : ℝ)) ≤ (sH : ℝ) ^ 2 := by exact_mod_cast hsH2
    have h2 : (0 : ℝ) ≤ sH := by exact_mod_cast hsH
    nlinarith
  have hsLR : (sL : ℝ) ≤ s := by
    have h1 : (sL : ℝ) ^ 2 ≤ 1 + 4 * (x : ℝ) := by exact_mod_cast hsL2
    have h2 : (0 : ℝ) ≤ sL := by exact_mod_cast hsL
    nlinarith
  -- `r ≤ ρ`
  have hρR : (r : ℝ) ≤ (s - 1) / (2 * s) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ (1 - 2 * (r : ℝ)) ^ 2 * (1 + 4 * (x : ℝ)) := by exact_mod_cast hρ
    have h2 : (0 : ℝ) < 1 - 2 * (r : ℝ) := by
      have : (2 * r : ℝ) < 1 := by exact_mod_cast hr2
      linarith
    have h3 : (1 : ℝ) ≤ s * (1 - 2 * (r : ℝ)) := by
      have h4 : (1 : ℝ) ^ 2 ≤ (s * (1 - 2 * (r : ℝ))) ^ 2 := by rw [mul_pow, hs2]; linarith
      exact (pow_le_pow_iff_left₀ zero_le_one (by positivity) two_ne_zero).mp h4
    linarith
  -- `c∞ − c ≥ c_L − c` and `K (c∞ − c) s ≥ 1`
  set δ := (1 + 2 * (x : ℝ) - s) / s ^ 2 - c with hδ
  clear_value δ
  have hcL : (1 + 2 * (x : ℝ) - sH) / (1 + 4 * (x : ℝ)) - c ≤ δ := by
    rw [hδ, hs2]
    have : (0 : ℝ) < 1 + 4 * (x : ℝ) := by linarith
    have h1 : (1 + 2 * (x : ℝ) - sH) / (1 + 4 * (x : ℝ)) ≤ (1 + 2 * (x : ℝ) - s) / (1 + 4 * x) :=
      div_le_div_of_nonneg_right (by linarith) this.le
    linarith
  have hKcR : (1 : ℝ) ≤ K * ((1 + 2 * (x : ℝ) - sH) / (1 + 4 * (x : ℝ)) - c) * sL := by
    exact_mod_cast hKc
  have hKR : (0 : ℝ) ≤ K := by exact_mod_cast hK
  have hsLR0 : (0 : ℝ) ≤ sL := by exact_mod_cast hsL
  have hcpos : 0 < (1 + 2 * (x : ℝ) - sH) / (1 + 4 * (x : ℝ)) - c := by
    by_contra hneg
    push_neg at hneg
    have : K * ((1 + 2 * (x : ℝ) - sH) / (1 + 4 * (x : ℝ)) - c) * (sL : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hKR hneg) hsLR0
    linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hKδ : (1 : ℝ) ≤ K * δ * s := by
    have h1 : (K : ℝ) * ((1 + 2 * (x : ℝ) - sH) / (1 + 4 * (x : ℝ)) - c) ≤ K * δ :=
      mul_le_mul_of_nonneg_left hcL hKR
    have h2 : (K : ℝ) * ((1 + 2 * (x : ℝ) - sH) / (1 + 4 * (x : ℝ)) - c) * sL ≤ K * δ * s :=
      mul_le_mul h1 hsLR (by positivity) (by positivity)
    linarith
  -- the closed forms
  obtain ⟨hz, hσ⟩ := zP_sP_closed x hs2 hsne j
  have hzpos : (0 : ℝ) < ((zP x j : ℚ) : ℝ) := by exact_mod_cast zP_pos hx.le j
  have goalR : ((r : ℝ) * j + c) * ((zP x j : ℚ) : ℝ) ≤ ((sP x j : ℚ) : ℝ) := by
    set N := j + 2 with hN
    clear_value N
    have hdiff : ((sP x j : ℚ) : ℝ) - ((r : ℝ) * j + c) * ((zP x j : ℚ) : ℝ) =
        (((s - 1) / (2 * s) - r) * j + δ) * ((zP x j : ℚ) : ℝ) -
          (N : ℝ) * ((1 - s) / 2) ^ N / s ^ 2 := by
      rw [hσ, hz, hδ]
      unfold sPc
      rw [hN]
      push_cast
      ring
    have hA : 0 ≤ (((s - 1) / (2 * s) - r) * j + δ) := by
      have : (0 : ℝ) ≤ ((s - 1) / (2 * s) - r) * j :=
        mul_nonneg (by linarith) (Nat.cast_nonneg j)
      linarith
    rcases Nat.even_or_odd N with hev | hodd
    · -- even `N`: `b^N = γ^N`, `Z_j = (a^N − γ^N)/s`, `a ≥ 2γ`
      set γ := (s - 1) / 2 with hγ
      set a := (1 + s) / 2 with ha
      clear_value γ a
      have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
      have hb : ((1 - s) / 2) ^ N = γ ^ N := by
        rw [show (1 - s) / 2 = -γ by rw [hγ]; ring, hev.neg_pow]
      have hzc : ((zP x j : ℚ) : ℝ) = (a ^ N - γ ^ N) / s := by
        rw [hz]
        unfold zPc
        rw [← hN, hb, ha]
      have ha2 : 2 * γ ≤ a := by rw [hγ, ha]; linarith
      have haN : 2 ^ N * γ ^ N ≤ a ^ N := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) ha2 N
      have hpow : (K : ℝ) * N + 1 ≤ 2 ^ N := by
        have := two_pow_ge hK hN01 hN0 N (by omega)
        exact_mod_cast this
      have hγN : 0 ≤ γ ^ N := pow_nonneg hγ0 N
      -- `a^N − γ^N ≥ K N γ^N`
      have hgap : (K : ℝ) * N * γ ^ N ≤ a ^ N - γ ^ N := by nlinarith
      have hmain : (N : ℝ) * γ ^ N / s ^ 2 ≤ δ * ((a ^ N - γ ^ N) / s) := by
        have hP : 0 ≤ (N : ℝ) * γ ^ N := by positivity
        have h1 : δ * (K * N * γ ^ N) ≤ δ * (a ^ N - γ ^ N) :=
          mul_le_mul_of_nonneg_left hgap hδ0
        have h2 : (N : ℝ) * γ ^ N ≤ K * δ * s * ((N : ℝ) * γ ^ N) := le_mul_of_one_le_left hP hKδ
        have h3 : s * (δ * (K * N * γ ^ N)) ≤ s * (δ * (a ^ N - γ ^ N)) :=
          mul_le_mul_of_nonneg_left h1 hs0
        have h4 : (N : ℝ) * γ ^ N ≤ δ * (a ^ N - γ ^ N) * s := by
          have e : K * δ * s * ((N : ℝ) * γ ^ N) = s * (δ * (K * N * γ ^ N)) := by ring
          rw [e] at h2
          linarith
        have h5 : (N : ℝ) * γ ^ N * s ≤ δ * (a ^ N - γ ^ N) * s * s :=
          mul_le_mul_of_nonneg_right h4 hs0
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have e2 : δ * (a ^ N - γ ^ N) * s ^ 2 = δ * (a ^ N - γ ^ N) * s * s := by ring
        rw [e2]
        exact h5
      have hB : δ * ((a ^ N - γ ^ N) / s) ≤
          (((s - 1) / (2 * s) - r) * j + δ) * ((zP x j : ℚ) : ℝ) := by
        have hKN : 0 ≤ (K : ℝ) * N * γ ^ N := mul_nonneg (mul_nonneg hKR (Nat.cast_nonneg N)) hγN
        have h1 : 0 ≤ (a ^ N - γ ^ N) / s := div_nonneg (by linarith) hs0
        have h2 : δ ≤ (((s - 1) / (2 * s) - r) * j + δ) := by
          have : (0 : ℝ) ≤ ((s - 1) / (2 * s) - r) * j :=
            mul_nonneg (by linarith) (Nat.cast_nonneg j)
          linarith
        rw [hzc]
        exact mul_le_mul_of_nonneg_right h2 h1
      rw [hb] at hdiff
      linarith
    · -- odd `N`: `b^N ≤ 0`
      have hbN : ((1 - s) / 2) ^ N ≤ 0 := hodd.pow_nonpos (by linarith)
      have h1 : 0 ≤ -((N : ℝ) * ((1 - s) / 2) ^ N / s ^ 2) := by
        rw [neg_nonneg]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hbN) (by positivity)
      have h2 : 0 ≤ (((s - 1) / (2 * s) - r) * j + δ) * ((zP x j : ℚ) : ℝ) :=
        mul_nonneg hA hzpos.le
      linarith
  exact_mod_cast goalR

end Erdos993Lean.Analytic.Density
