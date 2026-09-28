import Erdos993Lean.ZhangKernel.Lanes

/-!
# Kernel-checked finite part: soundness of the generic check

* **`layerD_spec`**: on a layer `1 ≤ j ≤ a`, the pair computed by `layerD` has difference the
  largest `σ · tgt_{j,m} − Σ w a_{j,m}` over `0 ≤ m ≤ a − j` (`resMax`), provided the flags hold, the
  target scale is at most `2^240` and the total weight at most `2^250` (then no lane overflows:
  `lanes_bound`);
* `layerMax_eq`, `autoEta_eq`: the package's layer maxima `ZhangCertX.layerMax` and free constant
  `ZhangCertX.autoEta` in terms of `resMax` (`W_j ≥ 0` commutes with the maxima: `foldl_max_mono`);
* `sumLayers_spec`, `rhsSumK_eq`, `sumW_eq`: the remaining loops;
* **`genericOK_of_genericOKV`**: `genericOKV n a k kind σ rows = true` implies
  `ZhangCertX.genericOK n a k kind σ rows = true`, for every certificate: the kernel check computes
  the same bound as the package's check (`ZhangCertX.boundWith` at `ZhangCertX.autoEta`).
-/

namespace Erdos993Lean

namespace ZhangKernel

open ZhangCertX Finset

/-- The residual of `(j, m)` divided by `W_j`: `σ · tgt_{j,m} − Σ w a_{j,m}`. -/
def gRes (n a k : ℕ) (kind : Kind) (σ : ℕ) (rows : List (CLabel × ℕ)) (j m : ℕ) : ℤ :=
  (σ : ℤ) * tgtZ kind k j m - rowSum n a rows j m

theorem list_sum_le {α : Type*} (l : List α) (w g : α → ℕ) (K : ℕ) (h : ∀ p ∈ l, g p ≤ K) :
    (l.map fun p => w p * g p).sum ≤ K * (l.map w).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h1 := h p List.mem_cons_self
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    nlinarith [Nat.zero_le (w p)]

theorem toNat_sub_neg (x : ℤ) : ((x.toNat : ℕ) : ℤ) - ((-x).toNat : ℕ) = x := by
  rcases x with x | x
  · rw [toNat_ofNat', toNat_neg_ofNat]; simp
  · rw [toNat_negSucc', toNat_neg_negSucc]; simp [Int.negSucc_eq]

theorem cast_wsum (l : List (CLabel × ℕ)) (g : CLabel × ℕ → ℕ) :
    (((l.map fun p => p.2 * g p).sum : ℕ) : ℤ) = (l.map fun p => (p.2 : ℤ) * (g p : ℤ)).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, ih, List.map_cons, List.sum_cons]

theorem wsum_split (l : List (CLabel × ℕ)) (c : CLabel × ℕ → ℤ) :
    (l.map fun p => (p.2 : ℤ) * ((-c p).toNat : ℤ)).sum -
      (l.map fun p => (p.2 : ℤ) * ((c p).toNat : ℤ)).sum = -(l.map fun p => (p.2 : ℤ) * c p).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    have := toNat_sub_neg (c p)
    linear_combination ih - (p.2 : ℤ) * this

set_option exponentiation.threshold 400 in
theorem lanes_bound {σ Wsum : ℕ} {t K : ℕ} (hσ : σ ≤ 2 ^ 240) (hW : Wsum ≤ 2 ^ 250) (ht : t ≤ 2 ^ 80)
    (hK : K ≤ 2 ^ 80 * Wsum) : σ * t + K < 2 ^ LB := by
  rw [LB_eq]
  calc σ * t + K ≤ 2 ^ 240 * 2 ^ 80 + 2 ^ 80 * 2 ^ 250 := by
        gcongr
        exact hK.trans (Nat.mul_le_mul_left _ hW)
    _ < 2 ^ 384 := by decide

theorem layerD_spec {n a k : ℕ} {kind : Kind} {σ : ℕ} {rows : List (CLabel × ℕ)} {j : ℕ}
    (hj : 1 ≤ j) (hja : j ≤ a) (hσ : σ ≤ sigBound) (hw : (rows.map (·.2)).sum ≤ wBound)
    (hok : (layerD n a k kind σ rows j).2.2 = true) :
    ((layerD n a k kind σ rows j).1 : ℤ) - (layerD n a k kind σ rows j).2.1 =
      (List.range (a - j)).foldl (fun acc i => max acc (gRes n a k kind σ rows j (i + 1)))
        (gRes n a k kind σ rows j 0) := by
  -- the lanes
  set L := a - j + 1 with hL
  have hL' : Nat.sub (Nat.add a 1) j = L := by simp only [Nat.sub_eq, Nat.add_eq]; omega
  obtain ⟨hA1, hA2, hA3⟩ := accL_spec n a j L rows 0 0 true
  obtain ⟨hP1, hP2⟩ := tgtPS_spec kind k j L
  obtain ⟨hQ1, hQ2⟩ := tgtQS_spec k j L
  -- the flags
  have hflags : (accL n a j L rows 0 0 true).2.2 = true ∧ (tgtPS kind k j L).2.2 = true ∧
      (tgtQS k j L).2.2 = true := by
    have h := hok
    simp only [layerD, hL', Bool.and_eq_true] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hrows := (hA3 hflags.1).2
  -- the lane values
  set xv : ℕ → ℕ := fun i => σ * tpv kind k j i + (rows.map fun p => p.2 * (-coefZ n a p.1 j i).toNat).sum
    with hxv
  set yv : ℕ → ℕ := fun i => σ * tqv k j i + (rows.map fun p => p.2 * (coefZ n a p.1 j i).toNat).sum
    with hyv
  have hrowP : ∀ p ∈ rows, rowVecP n a p.1 j L = ∑ i ∈ range L, (coefZ n a p.1 j i).toNat * 2 ^ (LB * i) :=
    fun p _ => (rowVec_spec p.1 hj L).1
  have hrowN : ∀ p ∈ rows, rowVecN n a p.1 j L = ∑ i ∈ range L, (-coefZ n a p.1 j i).toNat * 2 ^ (LB * i) :=
    fun p _ => (rowVec_spec p.1 hj L).2.1
  have hX : Nat.add (Nat.mul σ (tgtPS kind k j L).1) (accL n a j L rows 0 0 true).2.1 =
      ∑ i ∈ range L, xv i * 2 ^ (LB * i) := by
    rw [hA2, hP1, List.map_congr_left (fun p hp => by rw [hrowN p hp]), list_sum_lanes]
    simp only [Nat.add_eq, Nat.mul_eq, zero_add, hxv, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro i _; ring
  have hY : Nat.add (Nat.mul σ (tgtQS k j L).1) (accL n a j L rows 0 0 true).1 =
      ∑ i ∈ range L, yv i * 2 ^ (LB * i) := by
    rw [hA1, hQ1, List.map_congr_left (fun p hp => by rw [hrowP p hp]), list_sum_lanes]
    simp only [Nat.add_eq, Nat.mul_eq, zero_add, hyv, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro i _; ring
  -- the bounds
  have hWs : (rows.map (·.2)).sum ≤ 2 ^ 250 := by rw [show wBound = 2 ^ 250 from rfl] at hw; exact hw
  have hσ' : σ ≤ 2 ^ 240 := by rw [show sigBound = 2 ^ 240 from rfl] at hσ; exact hσ
  have hxb : ∀ i < L, xv i < 2 ^ LB := by
    intro i hi
    apply lanes_bound hσ' hWs (hP2 hflags.2.1 i hi)
    have := list_sum_le rows (·.2) (fun p => (-coefZ n a p.1 j i).toNat) (2 ^ 80)
      (fun p hp => ((rowVec_spec p.1 hj L).2.2 (hrows p hp) i hi).2)
    simpa using this
  have hyb : ∀ i < L, yv i < 2 ^ LB := by
    intro i hi
    apply lanes_bound hσ' hWs (hQ2 hflags.2.2 i hi)
    have := list_sum_le rows (·.2) (fun p => (coefZ n a p.1 j i).toNat) (2 ^ 80)
      (fun p hp => ((rowVec_spec p.1 hj L).2.2 (hrows p hp) i hi).1)
    simpa using this
  -- the residuals
  have hres : ∀ i, (xv i : ℤ) - yv i = gRes n a k kind σ rows j i := by
    intro i
    simp only [hxv, hyv, gRes, rowSum_eq, Nat.cast_add, Nat.cast_mul, cast_wsum]
    rw [← tpv_sub_tqv]
    have := wsum_split rows (fun p => coefZ n a p.1 j i)
    linear_combination this
  -- the loop
  have hunf : layerD n a k kind σ rows j =
      ((laneMaxL (L - 1) (Nat.shiftRight (∑ i ∈ range L, xv i * 2 ^ (LB * i)) LB)
          (Nat.shiftRight (∑ i ∈ range L, yv i * 2 ^ (LB * i)) LB)
          (Nat.land (∑ i ∈ range L, xv i * 2 ^ (LB * i)) maskB)
          (Nat.land (∑ i ∈ range L, yv i * 2 ^ (LB * i)) maskB)).1,
       (laneMaxL (L - 1) (Nat.shiftRight (∑ i ∈ range L, xv i * 2 ^ (LB * i)) LB)
          (Nat.shiftRight (∑ i ∈ range L, yv i * 2 ^ (LB * i)) LB)
          (Nat.land (∑ i ∈ range L, xv i * 2 ^ (LB * i)) maskB)
          (Nat.land (∑ i ∈ range L, yv i * 2 ^ (LB * i)) maskB)).2,
       and (accL n a j L rows 0 0 true).2.2 (and (tgtPS kind k j L).2.2 (tgtQS k j L).2.2)) := by
    rw [← hX, ← hY]
    simp only [layerD, hL', Nat.sub_eq]
  rw [hunf]
  dsimp only
  simp only [land_maskB, shiftRight_LB, hL, Nat.add_sub_cancel]
  rw [sumB_mod LB xv (a - j) (hxb 0 (by omega)), sumB_mod LB yv (a - j) (hyb 0 (by omega)),
    sumB_div LB xv (a - j) (hxb 0 (by omega)), sumB_div LB yv (a - j) (hyb 0 (by omega))]
  rw [laneMaxL_spec (a - j) (fun i => xv (i + 1)) (fun i => yv (i + 1)) (xv 0) (yv 0)
    (fun i hi => hxb (i + 1) (by omega)) (fun i hi => hyb (i + 1) (by omega))]
  try simp only [hres]


theorem foldl_max_mono {φ : ℤ → ℤ} (hφ : Monotone φ) (g : ℕ → ℤ) (l : List ℕ) (t : ℤ) :
    l.foldl (fun acc m => max acc (φ (g m))) (φ t) = φ (l.foldl (fun acc m => max acc (g m)) t) := by
  induction l generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [← hφ.map_max, ih]

theorem foldl_max_init (h : ℕ → ℤ) (l : List ℕ) (s t : ℤ) :
    l.foldl (fun acc m => max acc (h m)) (max s t) = max s (l.foldl (fun acc m => max acc (h m)) t) := by
  induction l generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [max_assoc, ih]

/-- The largest residual of the layer `j` (divided by `W_j`). -/
def resMax (n a k : ℕ) (kind : Kind) (σ : ℕ) (rows : List (CLabel × ℕ)) (j : ℕ) : ℤ :=
  (List.range (a - j)).foldl (fun acc i => max acc (gRes n a k kind σ rows j (i + 1)))
    (gRes n a k kind σ rows j 0)

theorem preZ_eq (n a k : ℕ) (kind : Kind) (σ : ℕ) (rows : List (CLabel × ℕ)) (j m : ℕ) :
    preZ n a k kind σ (layerRows rows j) j m = (binomN (vP n a) j : ℤ) * gRes n a k kind σ rows j m := by
  simp only [preZ, rowSum_layerRows, gRes]

theorem layerMax_eq {n a k : ℕ} {kind : Kind} {σ : ℕ} {rows : List (CLabel × ℕ)} (e : ℤ) {j : ℕ}
    (hja : j ≤ a) :
    layerMax n a k kind σ rows e j =
      max 0 ((binomN (vP n a) j : ℤ) * resMax n a k kind σ rows j - e) := by
  unfold layerMax resMax
  simp only [preZ_eq]
  rw [show a + 1 - j = (a - j) + 1 by omega, List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
    foldl_max_init]
  congr 1
  have hmono : Monotone (fun t : ℤ => (binomN (vP n a) j : ℤ) * t - e) := fun x y hxy => by
    have : (0 : ℤ) ≤ binomN (vP n a) j := Nat.cast_nonneg _
    simp only; nlinarith
  exact foldl_max_mono hmono (fun i => gRes n a k kind σ rows j (i + 1)) _ _

theorem autoEta_eq {n a k : ℕ} {kind : Kind} {σ : ℕ} {rows : List (CLabel × ℕ)} (ha : 1 ≤ a) :
    autoEta n a k kind σ rows = (binomN (vP n a) 1 : ℤ) * resMax n a k kind σ rows 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  unfold autoEta resMax
  simp only [preZ_eq]
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, max_self, Nat.add_sub_cancel]
  have hmono : Monotone (fun t : ℤ => (binomN (vP n (b + 1)) 1 : ℤ) * t) := fun x y hxy => by
    have : (0 : ℤ) ≤ binomN (vP n (b + 1)) 1 := Nat.cast_nonneg _
    simp only; nlinarith
  exact foldl_max_mono hmono (fun i => gRes n (b + 1) k kind σ rows 1 (i + 1)) _ _


theorem sumLayers_spec (n a k : ℕ) (kind : Kind) (σ : ℕ) (rows : List (CLabel × ℕ)) (c : ℕ) :
    ∀ (j : ℕ) (S : ℤ) (ok : Bool),
      (sumLayers n a k kind σ rows c j S ok).1 = S + ((List.range' j c).map fun i =>
        max 0 ((binomN (vP n a) i : ℤ) *
          (((layerD n a k kind σ rows i).1 : ℤ) - (layerD n a k kind σ rows i).2.1))).sum ∧
      ((sumLayers n a k kind σ rows c j S ok).2 = true →
        ok = true ∧ ∀ i ∈ List.range' j c, (layerD n a k kind σ rows i).2.2 = true) := by
  induction c with
  | zero => intro j S ok; exact ⟨by simp [sumLayers], fun h => ⟨h, by simp⟩⟩
  | succ c ih =>
    intro j S ok
    have hunf : sumLayers n a k kind σ rows (c + 1) j S ok =
        sumLayers n a k kind σ rows c (Nat.add j 1)
          (Int.add S (maxK (Int.ofNat 0) (Int.mul (Int.ofNat (chooseK (vP n a) j))
            (Int.subNatNat (layerD n a k kind σ rows j).1 (layerD n a k kind σ rows j).2.1))))
          (and ok (layerD n a k kind σ rows j).2.2) := rfl
    rw [hunf]
    obtain ⟨h1, h2⟩ := ih (Nat.add j 1) (Int.add S (maxK (Int.ofNat 0) (Int.mul
      (Int.ofNat (chooseK (vP n a) j))
      (Int.subNatNat (layerD n a k kind σ rows j).1 (layerD n a k kind σ rows j).2.1))))
      (and ok (layerD n a k kind σ rows j).2.2)
    refine ⟨?_, fun h => ?_⟩
    · rw [h1, List.range'_succ, List.map_cons, List.sum_cons]
      simp only [Nat.add_eq, Int.add_def, maxK_eq, Int.mul_def, subNatNat_eq, chooseK_eq,
        binomN_eq, Int.ofNat_eq_natCast, Nat.cast_zero]
      ring
    · obtain ⟨hok, hall⟩ := h2 h
      simp only [Bool.and_eq_true] at hok
      refine ⟨hok.1, fun i hi => ?_⟩
      rw [List.range'_succ, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hok.2
      · exact hall i (by simpa [Nat.add_eq] using hi)

theorem rhsSumK_eq (n a : ℕ) (rows : List (CLabel × ℕ)) :
    ∀ acc : ℤ, rhsSumK n a rows acc = acc + (rows.map fun p => (p.2 : ℤ) * rhsZ n a p.1).sum := by
  induction rows with
  | nil => intro acc; simp [rhsSumK]
  | cons p ps ih =>
    intro acc
    have hunf : rhsSumK n a (p :: ps) acc =
        rhsSumK n a ps (Int.add acc (Int.mul (Int.ofNat p.2) (rhsK n a p.1))) := rfl
    rw [hunf, ih, List.map_cons, List.sum_cons, rhsK_eq, Int.add_def, Int.mul_def,
      Int.ofNat_eq_natCast]
    ring

theorem sumW_eq (rows : List (CLabel × ℕ)) : ∀ acc : ℕ, sumW rows acc = acc + (rows.map (·.2)).sum := by
  induction rows with
  | nil => intro acc; simp [sumW]
  | cons p ps ih =>
    intro acc
    have hunf : sumW (p :: ps) acc = sumW ps (Nat.add acc p.2) := rfl
    rw [hunf, ih, List.map_cons, List.sum_cons, Nat.add_eq]
    ring

/-- **Soundness of the kernel form of the generic check**: it implies the package's check
`ZhangCertX.genericOK` (for any certificate data). -/
theorem genericOK_of_genericOKV {n a k : ℕ} {kind : Kind} {σ : ℕ} {rows : List (CLabel × ℕ)}
    (h : genericOKV n a k kind σ rows = true) : genericOK n a k kind σ rows = true := by
  simp only [genericOKV, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hv1, hva⟩, _⟩, hσ1⟩, hσB⟩, hrows⟩, hw⟩, hD1⟩, hS⟩, hsign⟩ := h
  rw [sumW_eq, zero_add] at hw
  have ha : 1 ≤ a := le_trans hv1 hva
  obtain ⟨hS1, hS2⟩ := sumLayers_spec n a k kind σ rows (Nat.sub (vP n a) 1) 2 (Int.ofNat 0) true
  obtain ⟨-, hSok⟩ := hS2 hS
  have hD : ∀ j, 1 ≤ j → j ≤ vP n a → (layerD n a k kind σ rows j).2.2 = true →
      ((layerD n a k kind σ rows j).1 : ℤ) - (layerD n a k kind σ rows j).2.1 =
        resMax n a k kind σ rows j := fun j hj1 hjv hok =>
    layerD_spec hj1 (le_trans hjv hva) hσB hw hok
  simp only [genericOK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hv1, by omega⟩, hrows⟩, ?_⟩
  rw [← signK_eq]
  convert hsign using 2
  -- the bound
  unfold boundWith
  rw [autoEta_eq ha, tgt0K_eq, rhsSumK_eq, rhsSum_eq, hS1, foldl_add_eq]
  rw [show vP n a = (vP n a - 1) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons]
  rw [show vP n a - 1 + 1 = vP n a by omega]
  simp only [if_true, Nat.sub_eq, Int.add_def, Int.mul_def, subNatNat_eq, chooseK_eq, binomN_eq,
    Int.ofNat_eq_natCast, Nat.cast_zero, zero_add]
  rw [hD 1 le_rfl hv1 hD1, layerMax_eq _ ha, ← binomN_eq]
  have hrest : ((List.range' (1 + 1) (vP n a - 1)).map fun j =>
      layerMax n a k kind σ rows (if j = 1 then (binomN (vP n a) 1 : ℤ) * resMax n a k kind σ rows 1
        else 0) j) =
      ((List.range' 2 (vP n a - 1)).map fun i => max 0 ((binomN (vP n a) i : ℤ) *
        (((layerD n a k kind σ rows i).1 : ℤ) - (layerD n a k kind σ rows i).2.1))) := by
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range'_1] at hj
    rw [if_neg (by omega), layerMax_eq _ (by omega), hD j (by omega) (by omega)
      (hSok j (by rw [List.mem_range'_1]; omega)), sub_zero]
  rw [hrest]
  simp only [sub_self, max_self, binomN_eq]
  ring


end ZhangKernel

end Erdos993Lean
