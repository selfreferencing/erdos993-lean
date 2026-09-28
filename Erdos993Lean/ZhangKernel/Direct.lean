import Erdos993Lean.ZhangKernel.Generic

/-!
# Kernel-checked finite part: soundness of the direct criteria

* **`tabLane_fold`**: lane `M` of the packed table row `tabRow h r` is the largest `x_h(r, m)` over
  `m ≤ M` (from the kernel check `tabCheck_eq`, for `r, M < 64`);
* `gRes_direct`: the residual of `(j, m)` of the direct criterion `h` (`directKind`, `directRows`,
  target scale `1`) is `x_h(r − j, m)` with `r = directTop k h` (`k`, or `k + 1` for the upper layer
  rule) if `j ≤ r`, and `0` otherwise; `resMax_direct`: its largest value is a table lane;
* **`genericOK_of_directV`**: `directV n a k h = true` implies
  `ZhangCertX.genericOK n a k (directKind h) 1 (directRows k h) = true`.
-/

namespace Erdos993Lean

namespace ZhangKernel

open ZhangCertX Finset

theorem tabLane_eq_min (h r M : ℕ) : tabLane h r M = tabLane (min h 2) r M := by
  rcases Nat.lt_or_ge h 2 with h2 | h2
  · rw [min_eq_left h2.le]
  · rw [min_eq_right h2]
    unfold tabLane tabRow
    by_cases h0 : h = 0
    · omega
    · by_cases h1 : h = 1
      · omega
      · simp [beq_false h0, beq_false h1, show Nat.beq 2 0 = false from rfl,
          show Nat.beq 2 1 = false from rfl]

theorem xRef_eq_min (h r m : ℕ) : xRef h r m = xRef (min h 2) r m := by
  rcases Nat.lt_or_ge h 2 with h2 | h2
  · rw [min_eq_left h2.le]
  · rw [min_eq_right h2]
    unfold xRef
    by_cases h0 : h = 0
    · omega
    · by_cases h1 : h = 1
      · omega
      · simp [beq_false h0, beq_false h1, show Nat.beq 2 0 = false from rfl,
          show Nat.beq 2 1 = false from rfl]

/-- **The tables** (from the kernel check `tabCheck_eq`): lane `M` of `tabRow h r` is the largest
`x_h(r, m)`, `m ≤ M`. -/
theorem tabLane_fold {h r M : ℕ} (hr : r < 64) (hM : M < 64) :
    tabLane h r M = (List.range M).foldl (fun acc i => max acc (xRef h r (i + 1))) (xRef h r 0) := by
  rw [tabLane_eq_min]
  simp_rw [xRef_eq_min h r]
  have hc := tabCheck_eq
  simp only [tabCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, eqK_eq, maxK_eq,
    decide_eq_true_eq] at hc
  have hh : min h 2 < 3 := by omega
  obtain ⟨h0, hs⟩ := hc (min h 2) hh r hr
  induction M with
  | zero => simpa using h0
  | succ M ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih (by omega)]
    exact hs M (by omega)

/-- The kind of the direct criterion `h`. -/
def directKind (h : ℕ) : Kind := if 2 ≤ h then .neg else .pos

/-- The rows of the direct criterion `h`. -/
def directRows (k h : ℕ) : List (CLabel × ℕ) := if h = 0 then [(.path k, 1)] else []

/-- The top index `r` of the direct criterion `h`: `k`, or `k + 1` for the upper layer rule. -/
def directTop (k h : ℕ) : ℕ := if 2 ≤ h then k + 1 else k

theorem BZ_shift {m j k : ℕ} (hjk : j ≤ k) : BZ m j k = BZ m 0 (k - j) := by
  unfold BZ
  congr 2 <;> push_cast [Nat.cast_sub hjk] <;> ring

theorem BZ_zero_of_lt {m j k : ℕ} (hjk : k < j) : BZ m j k = 0 := by
  unfold BZ
  rw [binomZ_of_neg _ _ (by omega), binomZ_of_neg _ _ (by omega), sub_zero]

theorem gRes_direct (n a k h j m : ℕ) :
    gRes n a k (directKind h) 1 (directRows k h) j m =
      if j ≤ directTop k h then xRef h (directTop k h - j) m else 0 := by
  unfold gRes
  rcases Nat.lt_or_ge h 2 with h2 | h2
  · have hk : directTop k h = k := by rw [directTop, if_neg (by omega)]
    have hkind : directKind h = .pos := by rw [directKind, if_neg (by omega)]
    rw [hk, hkind]
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0
      have hrows : directRows k 0 = [(.path k, 1)] := by rw [directRows, if_pos rfl]
      rw [hrows]
      simp only [rowSum_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tgtZ, coefZ,
        Nat.cast_one, one_mul, add_zero]
      by_cases hjk : j ≤ k
      · rw [BZ_shift hjk, binomZ_sub_nat, if_pos hjk, if_pos hjk]
        simp only [xRef, Nat.beq_refl, cond_true, Int.add_def, ineg_eq, BZK_eq, chooseK_eq,
          Int.ofNat_eq_natCast]
        ring
      · rw [BZ_zero_of_lt (by omega), binomZ_sub_nat, if_neg hjk, if_neg hjk]; simp
    · have hrows : directRows k h = [] := by rw [directRows, if_neg (by omega)]
      rw [hrows]
      simp only [rowSum_eq, List.map_nil, List.sum_nil, tgtZ, Nat.cast_one, one_mul, sub_zero]
      by_cases hjk : j ≤ k
      · rw [BZ_shift hjk, if_pos hjk]
        simp only [xRef, beq_false (show h ≠ 0 by omega), beq_true (show h = 1 by omega), cond_true,
          cond_false, ineg_eq, BZK_eq]
      · rw [BZ_zero_of_lt (by omega), if_neg hjk]; simp
  · have hk : directTop k h = k + 1 := by rw [directTop, if_pos h2]
    have hkind : directKind h = .neg := by rw [directKind, if_pos h2]
    have hrows : directRows k h = [] := by rw [directRows, if_neg (by omega)]
    rw [hk, hkind, hrows]
    simp only [rowSum_eq, List.map_nil, List.sum_nil, tgtZ, Nat.cast_one, one_mul, sub_zero]
    by_cases hjk : j ≤ k + 1
    · rw [BZ_shift hjk, if_pos hjk]
      simp only [xRef, beq_false (show h ≠ 0 by omega), beq_false (show h ≠ 1 by omega), cond_false,
        BZK_eq]
    · rw [BZ_zero_of_lt (by omega), if_neg hjk]


theorem foldl_max_zero (l : List ℕ) : l.foldl (fun acc (_ : ℕ) => max acc (0 : ℤ)) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, max_self, ih]

theorem resMax_direct {n a k h j : ℕ} (htop : directTop k h < 64) (ha : a - j < 64) :
    resMax n a k (directKind h) 1 (directRows k h) j =
      if j ≤ directTop k h then tabLane h (directTop k h - j) (a - j) else 0 := by
  unfold resMax
  simp only [gRes_direct]
  split_ifs with hj
  · rw [tabLane_fold (by omega) ha]
  · exact foldl_max_zero _

theorem sumLoopR_spec (f : ℕ → ℤ) (c : ℕ) :
    ∀ (j : ℕ) (acc : ℤ), sumLoopR f c j acc = acc + ((List.range' j c).map f).sum := by
  induction c with
  | zero => intro j acc; simp [sumLoopR]
  | succ c ih =>
    intro j acc
    have hunf : sumLoopR f (c + 1) j acc = sumLoopR f c (Nat.add j 1) (Int.add acc (f j)) := rfl
    rw [hunf, ih, List.range'_succ, List.map_cons, List.sum_cons, Nat.add_eq, Int.add_def]
    ring

/-- **Soundness of the kernel form of the direct criteria**: `directV n a k h` implies the
package's check of the criterion `h` (`0`: the path row with weight `1`, `1`: the lower layer rule,
otherwise the upper layer rule; target scale `1`). -/
theorem genericOK_of_directV {n a k h : ℕ} (hd : directV n a k h = true) :
    genericOK n a k (directKind h) 1 (directRows k h) = true := by
  have hkind : (bif Nat.ble 2 h then Kind.neg else Kind.pos) = directKind h := by
    unfold directKind; by_cases h2 : 2 ≤ h
    · rw [ble_true h2, if_pos h2]; rfl
    · rw [ble_false h2, if_neg h2]; rfl
  have htop : (bif Nat.ble 2 h then Nat.add k 1 else k) = directTop k h := by
    unfold directTop; by_cases h2 : 2 ≤ h
    · rw [ble_true h2, if_pos h2]; rfl
    · rw [ble_false h2, if_neg h2]; rfl
  simp only [directV, hkind, htop, Bool.and_eq_true, Nat.ble_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨hv1, hva⟩, ha63⟩, hk1⟩, htop63⟩, hpath⟩, hsign⟩ := hd
  have ha : 1 ≤ a := le_trans hv1 hva
  have hktop : 1 ≤ directTop k h := by unfold directTop; split_ifs <;> omega
  simp only [genericOK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hv1, by norm_num⟩, ?_⟩, ?_⟩
  · -- the rows are on their domains
    unfold directRows
    split_ifs with h0
    · subst h0
      simp only [Nat.beq_refl, cond_true, Bool.and_eq_true, Nat.ble_eq] at hpath
      simp [rowOKB, hpath.1, hpath.2]
    · simp
  · rw [← signK_eq]
    convert hsign using 2
    unfold boundWith
    rw [autoEta_eq ha, tgt0K_eq, rhsSum_eq, foldl_add_eq, sumLoopR_spec]
    rw [show vP n a = (vP n a - 1) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons]
    rw [show vP n a - 1 + 1 = vP n a by omega]
    rw [resMax_direct (by omega) (by omega), if_pos hktop, layerMax_eq _ ha,
      resMax_direct (by omega) (by omega), if_pos hktop]
    simp only [if_true, sub_self, max_self, zero_add, Int.add_def, Int.mul_def, chooseK_eq,
      binomN_eq, Int.ofNat_eq_natCast, Nat.sub_eq]
    have hrest : ((List.range' (1 + 1) (vP n a - 1)).map fun j =>
        layerMax n a k (directKind h) 1 (directRows k h)
          (if j = 1 then ((vP n a).choose 1 : ℤ) * tabLane h (directTop k h - 1) (a - 1) else 0) j) =
        ((List.range' 2 (vP n a - 1)).map fun j =>
          bif Nat.ble j (directTop k h) then
            maxK (Int.ofNat 0) (Int.mul (Int.ofNat (chooseK (vP n a) j))
              (tabLane h (Nat.sub (directTop k h) j) (Nat.sub a j)))
          else Int.ofNat 0) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range'_1] at hj
      rw [if_neg (by omega), layerMax_eq _ (by omega), resMax_direct (by omega) (by omega)]
      by_cases hjt : j ≤ directTop k h
      · simp only [if_pos hjt, ble_true hjt, cond_true, maxK_eq, Int.mul_def, chooseK_eq, binomN_eq,
          sub_zero, Int.ofNat_eq_natCast, Nat.sub_eq, Nat.cast_zero]
      · simp only [if_neg hjt, ble_false hjt, cond_false]; simp
    rw [hrest]
    simp only [Int.ofNat_eq_natCast, Int.mul_def, Nat.sub_eq, chooseK_eq, Nat.cast_zero, maxK_eq]
    unfold directRows
    split_ifs with h0
    · subst h0
      simp only [Nat.beq_refl, cond_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        rhsK_eq, Nat.cast_one, one_mul, add_zero, zero_add]
    · simp only [beq_false h0, cond_false, List.map_nil, List.sum_nil, Nat.cast_one,
        one_mul, zero_add]


end ZhangKernel

end Erdos993Lean
