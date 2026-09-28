import Erdos993Lean.ZhangKernel.Mirror

/-!
# Kernel-checked finite part: packed vectors

The generic check of `ZhangKernel/Core.lean` packs the coefficients of a row on a layer into
`384`-bit lanes of one natural number.  This module proves what the packed numbers are
(standard axioms only):

* `packS_spec`: the packing loop adds `Σ_i (f (m + i))⁺ 2^(sh + 384 i)` and
  `Σ_i (f (m + i))⁻ 2^(sh + 384 i)`, and its flag bounds every part by `2^80`;
* `sumB_mod`, `sumB_div`: the lowest lane of a packed number and the remaining lanes (lane width `B`);
* **`laneMaxL_spec`**: the best-lane loop returns a pair whose difference is the largest lane
  difference (a left fold of `max`);
* `accL_spec`: the accumulation over the rows is the weighted sum of the packed rows;
  `list_sum_lanes`: a weighted sum of packed vectors is the packed vector of the weighted lane sums;
* **`rowVec_spec`**: the packed rows are the positive and negative parts of `ZhangCertX.coefZ`
  (layers `j ≥ 1`), with the flag bounding them by `2^80`;
* `colS_spec`, `tgtPS_spec`, `tgtQS_spec`, **`tpv_sub_tqv`**: the packed target columns, whose lane
  differences are the target coefficients `ZhangCertX.tgtZ`.
-/

namespace Erdos993Lean

namespace ZhangKernel

open ZhangCertX Finset

theorem LB_eq : LB = 384 := rfl
set_option exponentiation.threshold 400 in
theorem maskB_eq : maskB = 2 ^ LB - 1 := by rfl
theorem partB_eq : partB = 2 ^ 80 - 1 := by rfl
set_option exponentiation.threshold 400 in
theorem land_maskB (y : ℕ) : Nat.land y maskB = y % 2 ^ LB := by
  rw [maskB_eq]
  exact Nat.and_two_pow_sub_one_eq_mod y LB
theorem shiftRight_LB (y : ℕ) : Nat.shiftRight y LB = y / 2 ^ LB := Nat.shiftRight_eq_div_pow y LB
theorem toNat_ofNat' (x : ℕ) : (Int.ofNat x).toNat = x := rfl
theorem toNat_neg_ofNat (x : ℕ) : (-(Int.ofNat x)).toNat = 0 := by cases x <;> rfl
theorem toNat_negSucc' (x : ℕ) : (Int.negSucc x).toNat = 0 := rfl
theorem toNat_neg_negSucc (x : ℕ) : (-(Int.negSucc x)).toNat = x + 1 := rfl
theorem shiftLeft_eq' (x s : ℕ) : Nat.shiftLeft x s = x * 2 ^ s := Nat.shiftLeft_eq x s

theorem sum_shiftB (B : ℕ) (g : ℕ → ℕ) (m sh c : ℕ) :
    ∑ i ∈ range (c + 1), g (m + i) * 2 ^ (sh + B * i) =
      g m * 2 ^ sh + ∑ i ∈ range c, g (m + 1 + i) * 2 ^ (sh + B + B * i) := by
  rw [sum_range_succ', add_comm]
  simp only [add_zero, mul_zero]
  congr 1
  apply sum_congr rfl; intro i _
  rw [show m + (i + 1) = m + 1 + i by ring, show sh + B * (i + 1) = sh + B + B * i by ring]

/-- The packing loop. -/
theorem packS_spec (f : ℕ → ℤ) (c : ℕ) : ∀ (m sh P N : ℕ) (ok : Bool),
    (packS f c m sh P N ok).1 = P + ∑ i ∈ range c, (f (m + i)).toNat * 2 ^ (sh + LB * i) ∧
    (packS f c m sh P N ok).2.1 = N + ∑ i ∈ range c, (-f (m + i)).toNat * 2 ^ (sh + LB * i) ∧
    ((packS f c m sh P N ok).2.2 = true →
      ok = true ∧ ∀ i < c, (f (m + i)).toNat ≤ 2 ^ 80 ∧ (-f (m + i)).toNat ≤ 2 ^ 80) := by
  induction c with
  | zero =>
    intro m sh P N ok
    exact ⟨by simp [packS], by simp [packS], fun h => ⟨h, fun i hi => absurd hi (by omega)⟩⟩
  | succ c ih =>
    intro m sh P N ok
    have hunf : packS f (c + 1) m sh P N ok =
        (match f m with
         | .ofNat x => packS f c (Nat.add m 1) (Nat.add sh LB) (Nat.add P (Nat.shiftLeft x sh)) N
             (and ok (Nat.ble x partB))
         | .negSucc x => packS f c (Nat.add m 1) (Nat.add sh LB) P
             (Nat.add N (Nat.shiftLeft (Nat.add x 1) sh)) (and ok (Nat.ble x partB))) := rfl
    have e1 := sum_shiftB LB (fun k => (f k).toNat) m sh c
    have e2 := sum_shiftB LB (fun k => (-f k).toNat) m sh c
    beta_reduce at e1 e2
    rw [hunf, e1, e2]
    cases hf : f m with
    | ofNat x =>
      obtain ⟨h1, h2, h3⟩ := ih (Nat.add m 1) (Nat.add sh LB) (Nat.add P (Nat.shiftLeft x sh)) N
        (and ok (Nat.ble x partB))
      simp only [Nat.add_eq] at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [h1, toNat_ofNat', shiftLeft_eq', add_assoc]
      · rw [h2, toNat_neg_ofNat, zero_mul, zero_add]
      · intro h
        obtain ⟨hok, hall⟩ := h3 h
        simp only [Bool.and_eq_true, Nat.ble_eq] at hok
        refine ⟨hok.1, fun i hi => ?_⟩
        rcases i with _ | i
        · rw [add_zero, hf, toNat_ofNat', toNat_neg_ofNat]
          have := hok.2; rw [partB_eq] at this; omega
        · have := hall i (by omega)
          rwa [show m + 1 + i = m + (i + 1) by ring] at this
    | negSucc x =>
      obtain ⟨h1, h2, h3⟩ := ih (Nat.add m 1) (Nat.add sh LB) P
        (Nat.add N (Nat.shiftLeft (Nat.add x 1) sh)) (and ok (Nat.ble x partB))
      simp only [Nat.add_eq] at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [h1, toNat_negSucc', zero_mul, zero_add]
      · rw [h2, toNat_neg_negSucc, shiftLeft_eq', add_assoc]
      · intro h
        obtain ⟨hok, hall⟩ := h3 h
        simp only [Bool.and_eq_true, Nat.ble_eq] at hok
        refine ⟨hok.1, fun i hi => ?_⟩
        rcases i with _ | i
        · rw [add_zero, hf, toNat_negSucc', toNat_neg_negSucc]
          have := hok.2; rw [partB_eq] at this; omega
        · have := hall i (by omega)
          rwa [show m + 1 + i = m + (i + 1) by ring] at this

theorem sumB_succ (B : ℕ) (x : ℕ → ℕ) (c : ℕ) :
    ∑ i ∈ range (c + 1), x i * 2 ^ (B * i) = x 0 + 2 ^ B * ∑ i ∈ range c, x (i + 1) * 2 ^ (B * i) := by
  rw [sum_range_succ', mul_sum, add_comm]
  simp only [mul_zero, pow_zero, mul_one]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [mul_add, mul_one, pow_add]
  ring

theorem sumB_mod (B : ℕ) (x : ℕ → ℕ) (c : ℕ) (hx : x 0 < 2 ^ B) :
    (∑ i ∈ range (c + 1), x i * 2 ^ (B * i)) % 2 ^ B = x 0 := by
  rw [sumB_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem sumB_div (B : ℕ) (x : ℕ → ℕ) (c : ℕ) (hx : x 0 < 2 ^ B) :
    (∑ i ∈ range (c + 1), x i * 2 ^ (B * i)) / 2 ^ B = ∑ i ∈ range c, x (i + 1) * 2 ^ (B * i) := by
  rw [sumB_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos B), Nat.div_eq_of_lt hx, zero_add]


/-- The best-lane loop: `x − y` of the returned pair is the largest lane difference. -/
theorem laneMaxL_spec (c : ℕ) : ∀ (x y : ℕ → ℕ) (xb yb : ℕ),
    (∀ i < c, x i < 2 ^ LB) → (∀ i < c, y i < 2 ^ LB) →
    (((laneMaxL c (∑ i ∈ range c, x i * 2 ^ (LB * i)) (∑ i ∈ range c, y i * 2 ^ (LB * i)) xb yb).1
        : ℤ) -
      (laneMaxL c (∑ i ∈ range c, x i * 2 ^ (LB * i)) (∑ i ∈ range c, y i * 2 ^ (LB * i)) xb yb).2 =
      (List.range c).foldl (fun acc i => max acc ((x i : ℤ) - y i)) ((xb : ℤ) - yb)) := by
  induction c with
  | zero => intro x y xb yb _ _; rfl
  | succ c ih =>
    intro x y xb yb hx hy
    have hunf : ∀ X Y : ℕ, laneMaxL (c + 1) X Y xb yb =
        laneMaxL c (Nat.shiftRight X LB) (Nat.shiftRight Y LB)
          (bif Nat.ble (Nat.add xb (Nat.land Y maskB)) (Nat.add (Nat.land X maskB) yb)
            then Nat.land X maskB else xb)
          (bif Nat.ble (Nat.add xb (Nat.land Y maskB)) (Nat.add (Nat.land X maskB) yb)
            then Nat.land Y maskB else yb) := fun _ _ => rfl
    rw [hunf]
    simp only [land_maskB, shiftRight_LB, sumB_mod LB x c (hx 0 (by omega)),
      sumB_mod LB y c (hy 0 (by omega)), sumB_div LB x c (hx 0 (by omega)),
      sumB_div LB y c (hy 0 (by omega))]
    rw [ih (fun i => x (i + 1)) (fun i => y (i + 1)) _ _ (fun i hi => hx (i + 1) (by omega))
      (fun i hi => hy (i + 1) (by omega))]
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    congr 1
    simp only [Nat.add_eq, Bool.cond_eq_ite, Nat.ble_eq]
    split_ifs with h
    · rw [max_eq_right (by omega)]
    · rw [max_eq_left (by omega)]


/-- The packed positive part of the row `ℓ` on the layer `j` (`L` lanes). -/
noncomputable def rowVecP (n a : ℕ) (ℓ : CLabel) (j L : ℕ) : ℕ :=
  match rowFnO n a ℓ j with
  | none => 0
  | some f => (packS f L 0 0 0 0 true).1

/-- The packed negative part of the row `ℓ` on the layer `j`. -/
noncomputable def rowVecN (n a : ℕ) (ℓ : CLabel) (j L : ℕ) : ℕ :=
  match rowFnO n a ℓ j with
  | none => 0
  | some f => (packS f L 0 0 0 0 true).2.1

/-- The flag of the row `ℓ` on the layer `j`. -/
noncomputable def rowVecOK (n a : ℕ) (ℓ : CLabel) (j L : ℕ) : Bool :=
  match rowFnO n a ℓ j with
  | none => true
  | some f => (packS f L 0 0 0 0 true).2.2

theorem accL_spec (n a j L : ℕ) (rows : List (CLabel × ℕ)) : ∀ (P N : ℕ) (ok : Bool),
    (accL n a j L rows P N ok).1 = P + (rows.map fun p => p.2 * rowVecP n a p.1 j L).sum ∧
    (accL n a j L rows P N ok).2.1 = N + (rows.map fun p => p.2 * rowVecN n a p.1 j L).sum ∧
    ((accL n a j L rows P N ok).2.2 = true → ok = true ∧ ∀ p ∈ rows, rowVecOK n a p.1 j L = true) := by
  induction rows with
  | nil => intro P N ok; exact ⟨by simp [accL], by simp [accL], fun h => ⟨h, by simp⟩⟩
  | cons p ps ih =>
    intro P N ok
    have hunf : accL n a j L (p :: ps) P N ok =
        (match rowFnO n a p.1 j with
         | none => accL n a j L ps P N ok
         | some f => accL n a j L ps (Nat.add P (Nat.mul p.2 (packS f L 0 0 0 0 true).1))
             (Nat.add N (Nat.mul p.2 (packS f L 0 0 0 0 true).2.1))
             (and ok (packS f L 0 0 0 0 true).2.2)) := rfl
    rw [hunf]
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    cases hf : rowFnO n a p.1 j with
    | none =>
      obtain ⟨h1, h2, h3⟩ := ih P N ok
      have hP : rowVecP n a p.1 j L = 0 := by unfold rowVecP; rw [hf]
      have hN : rowVecN n a p.1 j L = 0 := by unfold rowVecN; rw [hf]
      have hO : rowVecOK n a p.1 j L = true := by unfold rowVecOK; rw [hf]
      rw [hP, hN, hO]
      simp only [mul_zero, zero_add]
      exact ⟨h1, h2, fun h => ⟨(h3 h).1, trivial, (h3 h).2⟩⟩
    | some f =>
      obtain ⟨h1, h2, h3⟩ := ih (Nat.add P (Nat.mul p.2 (packS f L 0 0 0 0 true).1))
        (Nat.add N (Nat.mul p.2 (packS f L 0 0 0 0 true).2.1)) (and ok (packS f L 0 0 0 0 true).2.2)
      have hP : rowVecP n a p.1 j L = (packS f L 0 0 0 0 true).1 := by unfold rowVecP; rw [hf]
      have hN : rowVecN n a p.1 j L = (packS f L 0 0 0 0 true).2.1 := by unfold rowVecN; rw [hf]
      have hO : rowVecOK n a p.1 j L = (packS f L 0 0 0 0 true).2.2 := by unfold rowVecOK; rw [hf]
      rw [hP, hN, hO]
      dsimp only
      refine ⟨by rw [h1]; simp only [Nat.add_eq, Nat.mul_eq]; ring,
        by rw [h2]; simp only [Nat.add_eq, Nat.mul_eq]; ring, fun h => ?_⟩
      obtain ⟨hok, hall⟩ := h3 h
      simp only [Bool.and_eq_true] at hok
      exact ⟨hok.1, hok.2, hall⟩

/-- A weighted list of packed vectors is the packed vector of the weighted lane sums. -/
theorem list_sum_lanes {α : Type*} (B L : ℕ) (w : α → ℕ) (g : α → ℕ → ℕ) (l : List α) :
    (l.map fun p => w p * ∑ i ∈ range L, g p i * 2 ^ (B * i)).sum =
      ∑ i ∈ range L, (l.map fun p => w p * g p i).sum * 2 ^ (B * i) := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro i _
    rw [List.map_cons, List.sum_cons]; ring


theorem packS_zero (f : ℕ → ℤ) (L : ℕ) :
    (packS f L 0 0 0 0 true).1 = ∑ i ∈ range L, (f i).toNat * 2 ^ (LB * i) ∧
    (packS f L 0 0 0 0 true).2.1 = ∑ i ∈ range L, (-f i).toNat * 2 ^ (LB * i) ∧
    ((packS f L 0 0 0 0 true).2.2 = true → ∀ i < L, (f i).toNat ≤ 2 ^ 80 ∧ (-f i).toNat ≤ 2 ^ 80) := by
  obtain ⟨h1, h2, h3⟩ := packS_spec f L 0 0 0 0 true
  simp only [zero_add] at h1 h2 h3
  exact ⟨h1, h2, fun h => (h3 h).2⟩

theorem rowVec_spec {n a : ℕ} (ℓ : CLabel) {j : ℕ} (hj : 1 ≤ j) (L : ℕ) :
    rowVecP n a ℓ j L = ∑ i ∈ range L, (coefZ n a ℓ j i).toNat * 2 ^ (LB * i) ∧
    rowVecN n a ℓ j L = ∑ i ∈ range L, (-coefZ n a ℓ j i).toNat * 2 ^ (LB * i) ∧
    (rowVecOK n a ℓ j L = true →
      ∀ i < L, (coefZ n a ℓ j i).toNat ≤ 2 ^ 80 ∧ (-coefZ n a ℓ j i).toNat ≤ 2 ^ 80) := by
  obtain ⟨hs, hn⟩ := rowFnO_spec (n := n) (a := a) ℓ hj
  unfold rowVecP rowVecN rowVecOK
  cases hf : rowFnO n a ℓ j with
  | none =>
    have hz := hn hf
    refine ⟨?_, ?_, fun _ i _ => ?_⟩
    · simp [hz]
    · simp [hz]
    · simp [hz]
  | some f =>
    have hfe := hs f hf
    obtain ⟨h1, h2, h3⟩ := packS_zero f L
    simp only [hfe] at h1 h2 h3
    exact ⟨h1, h2, h3⟩


theorem colS_spec (r L : ℕ) :
    (colS r L).1 = ∑ i ∈ range L, chooseK i r * 2 ^ (LB * i) ∧ (colS r L).2.1 = 0 ∧
      ((colS r L).2.2 = true → ∀ i < L, chooseK i r ≤ 2 ^ 80) := by
  obtain ⟨h1, h2, h3⟩ := packS_zero (fun m => Int.ofNat (chooseK m r)) L
  refine ⟨?_, ?_, fun h i hi => ?_⟩
  · rw [colS, h1]; simp only [toNat_ofNat']
  · rw [colS, h2]; simp only [toNat_neg_ofNat, zero_mul, sum_const_zero]
  · have := (h3 h i hi).1; rwa [toNat_ofNat'] at this

/-- The lanes of the positive part of the target. -/
def tpv (kind : Kind) (k j i : ℕ) : ℕ :=
  match kind with
  | .pos => if j + 1 ≤ k then chooseK i (k - j - 1) else 0
  | .neg => if j ≤ k + 1 then chooseK i (k + 1 - j) else 0
  | .cond => if j ≤ k + 1 then chooseK i (k + 1 - j) else 0

/-- The lanes of the negative part of the target. -/
def tqv (k j i : ℕ) : ℕ := if j ≤ k then chooseK i (k - j) else 0

theorem tgtPS_spec (kind : Kind) (k j L : ℕ) :
    (tgtPS kind k j L).1 = ∑ i ∈ range L, tpv kind k j i * 2 ^ (LB * i) ∧
      ((tgtPS kind k j L).2.2 = true → ∀ i < L, tpv kind k j i ≤ 2 ^ 80) := by
  have hz : ∀ r, (∑ i ∈ range L, (0 : ℕ) * 2 ^ (LB * i)) = r * 0 := fun r => by simp
  cases kind
  · by_cases h : j + 1 ≤ k
    · simp only [tgtPS, tpv, Nat.add_eq, Nat.sub_eq, ble_true h, cond_true, if_pos h]
      exact ⟨(colS_spec _ L).1, (colS_spec _ L).2.2⟩
    · simp only [tgtPS, tpv, Nat.add_eq, ble_false h, cond_false, if_neg h]
      exact ⟨by simp, fun _ _ _ => by norm_num⟩
  · by_cases h : j ≤ k + 1
    · simp only [tgtPS, tpv, Nat.add_eq, Nat.sub_eq, ble_true h, cond_true, if_pos h]
      exact ⟨(colS_spec _ L).1, (colS_spec _ L).2.2⟩
    · simp only [tgtPS, tpv, Nat.add_eq, ble_false h, cond_false, if_neg h]
      exact ⟨by simp, fun _ _ _ => by norm_num⟩
  · by_cases h : j ≤ k + 1
    · simp only [tgtPS, tpv, Nat.add_eq, Nat.sub_eq, ble_true h, cond_true, if_pos h]
      exact ⟨(colS_spec _ L).1, (colS_spec _ L).2.2⟩
    · simp only [tgtPS, tpv, Nat.add_eq, ble_false h, cond_false, if_neg h]
      exact ⟨by simp, fun _ _ _ => by norm_num⟩

theorem tgtQS_spec (k j L : ℕ) :
    (tgtQS k j L).1 = ∑ i ∈ range L, tqv k j i * 2 ^ (LB * i) ∧
      ((tgtQS k j L).2.2 = true → ∀ i < L, tqv k j i ≤ 2 ^ 80) := by
  by_cases h : j ≤ k
  · simp only [tgtQS, tqv, Nat.sub_eq, ble_true h, cond_true, if_pos h]
    exact ⟨(colS_spec _ L).1, (colS_spec _ L).2.2⟩
  · simp only [tgtQS, tqv, ble_false h, cond_false, if_neg h]
    exact ⟨by simp, fun _ _ _ => by norm_num⟩

theorem tpv_sub_tqv (kind : Kind) (k j i : ℕ) :
    (tpv kind k j i : ℤ) - tqv k j i = tgtZ kind k j i := by
  have hpos : (tpv .pos k j i : ℤ) - tqv k j i = -BZK i j k := by
    simp only [tpv, tqv, BZK]
    by_cases h1 : j ≤ k
    · by_cases h2 : j = k
      · subst h2
        simp [ble_true (le_refl j), Nat.beq_refl, subNatNat_eq]
      · simp only [ble_true h1, beq_false h2, cond_true, cond_false, if_pos h1,
          if_pos (show j + 1 ≤ k by omega), subNatNat_eq, Nat.sub_eq]
        ring
    · simp only [ble_false h1, cond_false, if_neg h1, if_neg (show ¬ j + 1 ≤ k by omega)]
      rfl
  have hneg : (tpv .neg k j i : ℤ) - tqv k j i = BZK i j (Nat.add k 1) := by
    simp only [tpv, tqv, BZK, Nat.add_eq]
    by_cases h1 : j ≤ k + 1
    · by_cases h2 : j = k + 1
      · subst h2
        simp [ble_true (le_refl (k + 1)), Nat.beq_refl, subNatNat_eq]
      · simp only [ble_true h1, beq_false h2, cond_true, cond_false, if_pos h1,
          if_pos (show j ≤ k by omega), subNatNat_eq, Nat.sub_eq]
        rw [show k + 1 - j - 1 = k - j by omega]
    · simp only [ble_false h1, cond_false, if_neg h1, if_neg (show ¬ j ≤ k by omega)]
      rfl
  cases kind
  · rw [hpos, BZK_eq]; rfl
  · rw [hneg, BZK_eq]; rfl
  · rw [show tpv .cond k j i = tpv .neg k j i from rfl, hneg, BZK_eq]; rfl


end ZhangKernel

end Erdos993Lean
