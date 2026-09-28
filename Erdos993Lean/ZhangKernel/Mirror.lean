import Mathlib
import Erdos993Lean.ZhangCert.Bridge
import Erdos993Lean.ZhangKernel.LiteralChecks

/-!
# Kernel-checked finite part: the mirrors are exact

The kernel checker `ZhangKernel/Core.lean` recomputes the integer rows of `ZhangCertX`
(`Erdos993LeanZhangCompute/Checker/Core.lean`) with the kernel's `Nat` primitives.  This module
proves that every mirror is exact (standard axioms only):

* `chooseK_eq`: the packed-table binomial is `Nat.choose` (from the kernel check `bRowCheck_eq` and
  `ZhangCertX.binomF_eq`); `binomZK_eq`: `binomZK = ZhangCertX.binomZ`;
* `leK_eq`, `maxK_eq`, `eqK_eq`, `signK_eq`: the integer comparisons;
* `BZK_eq`, `tgt0K_eq`, `privPos_eq`, `hallCK_eq`, `bStepK_eq`, `sExtK_eq`, `UK_eq`, `VtK_eq`,
  `βK_eq`, `C0K_eq`, `GrK_eq`: the auxiliary functions of the rows;
* **`coefK_eq`**, **`rhsK_eq`**: the coefficients and right sides of every row label are those of
  `ZhangCertX.coefZ`, `ZhangCertX.rhsZ`;
* **`rowFnO_spec`**: on a layer `j ≥ 1`, the coefficient function chosen by `rowFnO` is `none` only
  if the row vanishes on the layer, and otherwise equals `m ↦ coefZ n a ℓ j m`.
-/

namespace Erdos993Lean

namespace ZhangKernel

open ZhangCertX Finset

theorem ble_true {x y : ℕ} (h : x ≤ y) : Nat.ble x y = true := Nat.ble_eq.mpr h

theorem ble_false {x y : ℕ} (h : ¬ x ≤ y) : Nat.ble x y = false := by
  cases hb : Nat.ble x y
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) h

theorem beq_true {x y : ℕ} (h : x = y) : Nat.beq x y = true := by
  subst h; exact Nat.beq_refl x

theorem beq_false {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h


theorem ineg_eq (x : ℤ) : Int.neg x = -x := rfl

theorem ndiv_eq (x y : ℕ) : Nat.div x y = x / y := rfl

theorem nmod_eq (x y : ℕ) : Nat.mod x y = x % y := rfl

theorem nmin_eq (x y : ℕ) : Nat.min x y = min x y := rfl

theorem negOfNat_eq' (x : ℕ) : Int.negOfNat x = -(x : ℤ) := by
  cases x <;> rfl

theorem bLane_eq {m r : ℕ} (hm : m < 64) (hr : r < 64) : bLane m r = binomF m r := by
  have h := bRowCheck_eq
  simp only [bRowCheck, List.all_eq_true, List.mem_range] at h
  exact Nat.eq_of_beq_eq_true (h m hm r hr)

theorem chooseK_eq (m r : ℕ) : chooseK m r = m.choose r := by
  rw [← binomF_eq]
  unfold chooseK
  simp only [Bool.cond_eq_ite, Bool.or_eq_true, Nat.ble_eq]
  split_ifs with h
  · rfl
  · push_neg at h
    exact bLane_eq h.1 h.2

theorem leK_eq (x y : ℤ) : leK x y = decide (x ≤ y) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  rcases x with x | x <;> rcases y with y | y <;> simp [leK, Nat.ble_eq, Int.negSucc_eq] <;> omega

theorem maxK_eq (x y : ℤ) : maxK x y = max x y := by
  unfold maxK
  rw [leK_eq, Bool.cond_decide, max_def]

theorem eqK_eq (x y : ℤ) : eqK x y = decide (x = y) := by
  unfold eqK
  rw [leK_eq, leK_eq, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2
  · rintro rfl; exact ⟨le_refl _, le_refl _⟩

theorem signK_eq (kind : Kind) (b : ℤ) : signK kind b = signOK kind b := by
  cases kind <;> simp only [signK, signOK, leK_eq, Int.ofNat_eq_natCast, Nat.cast_zero]
  rw [Bool.eq_iff_iff]
  simp [not_le]


theorem binomZ_nat (m r : ℕ) : binomZ (m : ℤ) (r : ℤ) = (m.choose r : ℤ) := by
  unfold binomZ
  split_ifs with h
  · simp [binomN_eq]
  · push_neg at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem binomZ_of_neg (b r : ℤ) (h : r < 0) : binomZ b r = 0 := by
  unfold binomZ
  rw [if_neg (by omega)]

theorem binomZ_of_neg_left (b r : ℤ) (h : b < 0) : binomZ b r = 0 := by
  unfold binomZ
  rw [if_neg (by omega)]

theorem binomZK_eq (b r : ℤ) : binomZK b r = binomZ b r := by
  rcases b with b | b <;> rcases r with r | r
  · simp only [binomZK, chooseK_eq, Int.ofNat_eq_natCast]
    exact (binomZ_nat b r).symm
  · simp only [binomZK]
    rw [binomZ_of_neg _ _ (Int.negSucc_lt_zero r)]; rfl
  · simp only [binomZK]
    rw [binomZ_of_neg_left _ _ (Int.negSucc_lt_zero b)]; rfl
  · simp only [binomZK]
    rw [binomZ_of_neg _ _ (Int.negSucc_lt_zero r)]; rfl

theorem subNatNat_eq (x y : ℕ) : Int.subNatNat x y = (x : ℤ) - y := Int.subNatNat_eq_coe

theorem BZK_eq (m j k : ℕ) : BZK m j k = BZ m j k := by
  unfold BZK BZ
  by_cases hjk : j ≤ k
  · have e1 : ((k : ℤ) - j) = ((k - j : ℕ) : ℤ) := by push_cast [Nat.cast_sub hjk]; ring
    rw [e1, binomZ_nat]
    simp only [ble_true hjk, cond_true, subNatNat_eq, Nat.sub_eq, chooseK_eq]
    by_cases hjk' : j = k
    · subst hjk'
      simp only [Nat.beq_refl, cond_true, Nat.sub_self]
      rw [binomZ_of_neg _ _ (by omega)]
      simp
    · have e2 : ((k - j : ℕ) : ℤ) - 1 = ((k - j - 1 : ℕ) : ℤ) := by omega
      simp only [beq_false hjk', cond_false]
      rw [e2, binomZ_nat]
  · simp only [ble_false hjk, cond_false]
    rw [binomZ_of_neg _ _ (by omega), binomZ_of_neg _ _ (by omega)]
    simp

theorem tgt0K_eq (kind : Kind) (a k : ℕ) : tgt0K kind a k = tgt0Z kind a k := by
  cases kind <;> simp only [tgt0K, tgt0Z, BZK_eq, ineg_eq, Nat.add_eq]


theorem posZ_natSub (X Y : ℕ) : posZ ((X : ℤ) - Y) = ((X - Y : ℕ) : ℤ) := by
  unfold posZ; omega

theorem privPos_eq (a r h m : ℕ) :
    (privPos a r h m : ℤ) = posZ (((r : ℤ) - 1) * m + a - r + 1 - r * h) := by
  unfold privPos
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp only [Nat.beq_refl, cond_true, Nat.add_eq, Nat.sub_eq]
    have : ((0 : ℕ) : ℤ) - 1 = -1 := by norm_num
    rw [show (((0:ℕ) : ℤ) - 1) * m + a - (0:ℕ) + 1 - (0:ℕ) * h = ((a + 1 : ℕ) : ℤ) - m by push_cast; ring,
      posZ_natSub]
  · simp only [beq_false (show r ≠ 0 by omega), cond_false, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
    rw [show ((r : ℤ) - 1) * m + a - r + 1 - r * h =
        (((r - 1) * m + (a + 1) : ℕ) : ℤ) - ((r + r * h : ℕ) : ℤ) by
          push_cast [Nat.cast_sub (show 1 ≤ r by omega)]; ring,
      posZ_natSub]

theorem hallCK_eq (n a r l : ℕ) : hallCK n a r l = hallCZ n a r l := by
  unfold hallCK hallCZ
  rw [subNatNat_eq]
  simp only [Nat.add_eq, Nat.sub_eq]
  omega

theorem bStepK_eq (a r h m : ℕ) : (bStepK a r h m : ℤ) = bStepZ a r h m := by
  unfold bStepK bStepZ
  simp only [Bool.cond_eq_ite, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  split_ifs <;> simp

theorem sExtK_eq (n a r : ℕ) : (sExtK n a r : ℤ) = sExtZ n a r := by
  unfold sExtK sExtZ
  simp only [Nat.add_eq, Nat.sub_eq]
  rw [show (vP n a : ℤ) - r + 1 - EP n a = ((vP n a + 1 : ℕ) : ℤ) - ((r + EP n a : ℕ) : ℤ) by
    push_cast; ring, posZ_natSub]

theorem UK_eq (a r h m : ℕ) : (UK a r h m : ℤ) = UZ a r h m := by
  unfold UK UZ
  simp only [Bool.cond_eq_ite, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ndiv_eq, nmod_eq]
  rw [show ((m : ℤ) + ((a - m + 1 - r : ℕ) : ℤ) - h) = (((m + (a - m + 1 - r)) : ℕ) : ℤ) - (h : ℤ) by
    push_cast; ring, posZ_natSub]
  split_ifs with h1 h2 h2
  · omega
  · push_cast; ring
  · rw [show ((m : ℤ) + (((a - m) % (a - m + 1 - r) : ℕ) : ℤ) - h) =
        (((m + (a - m) % (a - m + 1 - r)) : ℕ) : ℤ) - (h : ℤ) by push_cast; ring, posZ_natSub,
      show ((m : ℤ) - h) = ((m : ℕ) : ℤ) - ((h : ℕ) : ℤ) by rfl, posZ_natSub]
    push_cast; ring
  · omega

theorem VtK_eq (a r h m : ℕ) : (VtK a r h m : ℤ) = VtZ a r h m := by
  unfold VtK VtZ
  simp only [Bool.cond_eq_ite, Nat.ble_eq, Nat.add_eq, Nat.sub_eq, ndiv_eq, nmin_eq]
  split_ifs <;> simp_all

theorem βK_eq (n a r : ℕ) : βK n a r = βZ n a r := by
  unfold βK βZ
  simp only [binomZK_eq, subNatNat_eq, Int.add_def, ineg_eq, Int.mul_def]
  push_cast; ring

theorem C0K_eq (n a r : ℕ) : C0K n a r = C0Z n a r := by
  unfold C0K C0Z
  simp only [binomZK_eq, subNatNat_eq, Int.add_def, Int.mul_def, Int.ofNat_eq_natCast, Nat.add_eq]
  push_cast; ring

theorem GrK_eq (n a r : ℕ) : GrK n a r = GrZ n a r := by
  unfold GrK GrZ
  simp only [binomZK_eq, subNatNat_eq, Int.add_def, ineg_eq, Nat.add_eq]
  push_cast; ring_nf


theorem binomZ_sub_nat (m r j : ℕ) :
    binomZ (m : ℤ) ((r : ℤ) - j) = if j ≤ r then ((m.choose (r - j) : ℕ) : ℤ) else 0 := by
  split_ifs with h
  · rw [show ((r : ℤ) - j) = ((r - j : ℕ) : ℤ) by omega, binomZ_nat]
  · exact binomZ_of_neg _ _ (by omega)

theorem coefK_eq (n a : ℕ) (ℓ : CLabel) (j m : ℕ) : coefK n a ℓ j m = coefZ n a ℓ j m := by
  cases ℓ with
  | count r =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq]; split_ifs <;> rfl
  | path r =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.ble_eq, binomZ_sub_nat, negOfNat_eq', chooseK_eq,
      Nat.sub_eq]
    split_ifs <;> simp
  | priv r h =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Int.add_def, ineg_eq, Int.mul_def,
      subNatNat_eq, Nat.add_eq, Nat.sub_eq, Int.ofNat_eq_natCast, privPos_eq]
    have hp : posZ ((m : ℤ) - h) = ((m - h : ℕ) : ℤ) := posZ_natSub m h
    split_ifs <;> (try rw [hp]) <;> push_cast <;> ring
  | hall r l =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, ineg_eq, Int.mul_def, hallCK_eq,
      Int.ofNat_eq_natCast, chooseK_eq, Nat.add_eq, Nat.mul_eq, binomZ_nat]
    split_ifs <;> first | omega | (push_cast; ring)
  | tail r h =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Nat.ble_eq, Bool.and_eq_true, Int.add_def,
      ineg_eq, subNatNat_eq, Nat.add_eq, Nat.sub_eq, Int.ofNat_eq_natCast, bStepK_eq]
    split_ifs <;> push_cast <;> ring
  | releaseUpper r h =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Int.add_def, negOfNat_eq', Int.ofNat_eq_natCast,
      Nat.mul_eq, Nat.sub_eq, UK_eq]
    have hp : posZ ((m : ℤ) - h) = ((m - h : ℕ) : ℤ) := posZ_natSub m h
    split_ifs <;> (try rw [hp]) <;> (try rw [← sExtK_eq]) <;> push_cast <;> ring
  | tailUpper r h =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Nat.ble_eq, Bool.and_eq_true, Int.add_def,
      negOfNat_eq', Int.ofNat_eq_natCast, VtK_eq, sExtK_eq, Nat.sub_eq]
    split_ifs <;> ring
  | mean r =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Int.add_def, negOfNat_eq', ineg_eq, βK_eq]
    split_ifs <;> ring
  | union r =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Int.add_def, Int.mul_def, ineg_eq,
      subNatNat_eq, binomZK_eq, Int.ofNat_eq_natCast]
    split_ifs <;> push_cast <;> ring
  | edgeLower r =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Int.add_def, negOfNat_eq', subNatNat_eq,
      binomZK_eq]
    split_ifs <;> push_cast <;> ring
  | edgeUpper r =>
    simp only [coefK, coefZ, Bool.cond_eq_ite, Nat.beq_eq, Int.add_def, ineg_eq, GrK_eq,
      Int.ofNat_eq_natCast]
    split_ifs <;> ring
  | assumption k => exact BZK_eq m j k

theorem rhsK_eq (n a : ℕ) (ℓ : CLabel) : rhsK n a ℓ = rhsZ n a ℓ := by
  cases ℓ with
  | count r => simp only [rhsK, rhsZ, binomZK_eq, Int.ofNat_eq_natCast]
  | path r =>
    simp only [rhsK, rhsZ, binomZK_eq, Int.add_def, ineg_eq, subNatNat_eq, Int.ofNat_eq_natCast,
      Nat.add_eq]
    push_cast; ring_nf
  | priv r h => rfl
  | hall r l =>
    simp only [rhsK, rhsZ, Bool.cond_eq_ite, Nat.beq_eq, Int.mul_def, hallCK_eq, binomZK_eq,
      Int.ofNat_eq_natCast]
    split_ifs <;> rfl
  | tail r h => rfl
  | releaseUpper r h => rfl
  | tailUpper r h => rfl
  | mean r =>
    simp only [rhsK, rhsZ, Int.add_def, ineg_eq, Int.mul_def, C0K_eq, βK_eq, binomZK_eq,
      Int.ofNat_eq_natCast]
    push_cast; ring
  | union r => rfl
  | edgeLower r =>
    simp only [rhsK, rhsZ, Int.add_def, ineg_eq, Int.mul_def, binomZK_eq, subNatNat_eq,
      Int.ofNat_eq_natCast]
    push_cast; ring
  | edgeUpper r =>
    simp only [rhsK, rhsZ, Int.add_def, ineg_eq, Int.mul_def, GrK_eq, binomZK_eq,
      Int.ofNat_eq_natCast]
    push_cast; ring
  | assumption k => simp only [rhsK, rhsZ, ineg_eq, BZK_eq]


theorem generic_spec {n a : ℕ} (ℓ : CLabel) {j : ℕ} (_hj : 1 ≤ j) (h : rowFnO n a ℓ j = rfGeneric n a ℓ j) :
    (∀ f, rowFnO n a ℓ j = some f → ∀ m, f m = coefK n a ℓ j m) ∧
      (rowFnO n a ℓ j = none → ∀ m, coefK n a ℓ j m = 0) := by
  rw [h]
  unfold rfGeneric
  cases ht : touches ℓ j
  · simp only [cond_false, reduceCtorEq, false_implies, implies_true, true_and]
    intro _ m
    rw [coefK_eq]
    exact coefZ_eq_zero ht m
  · simp only [cond_true, Option.some.injEq, reduceCtorEq, false_implies, and_true]
    rintro f rfl m
    rfl

theorem rowFnO_specK {n a : ℕ} (ℓ : CLabel) {j : ℕ} (hj : 1 ≤ j) :
    (∀ f, rowFnO n a ℓ j = some f → ∀ m, f m = coefK n a ℓ j m) ∧
      (rowFnO n a ℓ j = none → ∀ m, coefK n a ℓ j m = 0) := by
  cases ℓ with
  | count r =>
    simp only [rowFnO, rfCount, coefK]
    by_cases h1 : j = r
    · simp [beq_true h1]
    · simp [beq_false h1]
  | path r =>
    simp only [rowFnO, rfPath, coefK]
    by_cases h1 : j ≤ r
    · simp [ble_true h1]
    · simp [ble_false h1]
  | priv r h =>
    simp only [rowFnO, rfPriv, coefK, Nat.sub_eq, Nat.add_eq]
    by_cases h1 : j = r
    · have h2 : j ≠ r - 1 := by omega
      simp [beq_true h1, beq_false h2]
    · by_cases h2 : j = r - 1
      · by_cases h3 : r ≤ vP n a + 1
        · simp only [beq_false h1, beq_true h2, ble_true h3, cond_true, cond_false,
            Option.some.injEq, reduceCtorEq, false_implies, and_true]
          rintro f rfl m
          simp only [Nat.mul_eq, Int.add_def, Int.mul_def, ineg_eq, subNatNat_eq, negOfNat_eq', Int.ofNat_eq_natCast]
          push_cast [Nat.cast_sub h3]; ring
        · simp only [beq_false h1, beq_true h2, ble_false h3, cond_true, cond_false,
            Option.some.injEq, reduceCtorEq, false_implies, and_true]
          rintro f rfl m
          simp only [Nat.mul_eq, Int.add_def, Int.mul_def, ineg_eq, subNatNat_eq, Int.ofNat_eq_natCast]
          push_cast [Nat.cast_sub (show vP n a + 1 ≤ r by omega)]; ring
      · simp [beq_false h1, beq_false h2]
  | hall r l =>
    simp only [rowFnO, rfHall, coefK, hallCK, Nat.sub_eq, Nat.add_eq]
    by_cases h1 : j = r + 1
    · simp [beq_true h1]
    · by_cases h2 : j = r
      · by_cases h3 : r + (l - δP n a) ≤ vP n a
        · simp only [beq_false h1, beq_true h2, ble_true h3, cond_true, cond_false,
            Option.some.injEq, reduceCtorEq, false_implies, and_true]
          rintro f rfl m
          simp only [Nat.mul_eq, Int.mul_def, ineg_eq, subNatNat_eq, negOfNat_eq', Int.ofNat_eq_natCast]
          push_cast [Nat.cast_sub h3]; ring
        · simp only [beq_false h1, beq_true h2, ble_false h3, cond_true, cond_false,
            Option.some.injEq, reduceCtorEq, false_implies, and_true]
          rintro f rfl m
          simp only [Nat.mul_eq, Int.mul_def, ineg_eq, subNatNat_eq, Int.ofNat_eq_natCast]
          push_cast [Nat.cast_sub (show vP n a ≤ r + (l - δP n a) by omega)]; ring
      · simp [beq_false h1, beq_false h2]
  | tail r h =>
    simp only [rowFnO, rfTail, coefK, Nat.sub_eq, Nat.add_eq]
    by_cases h1 : j = r
    · have h2 : j ≠ r - 1 := by omega
      simp [beq_true h1, beq_false h2]
    · by_cases h2 : j = r - 1
      · by_cases h3 : r ≤ vP n a + 1
        · simp only [beq_false h1, beq_true h2, ble_true h3, cond_true, cond_false,
            Option.some.injEq, reduceCtorEq, false_implies, and_true, Bool.true_and]
          rintro f rfl m
          by_cases hm : h ≤ m
          · simp only [ble_true hm, cond_true, Int.add_def, ineg_eq, subNatNat_eq, negOfNat_eq', Int.ofNat_eq_natCast]
            push_cast [Nat.cast_sub h3]; ring
          · simp only [ble_false hm, cond_false, Int.add_def, ineg_eq, subNatNat_eq, negOfNat_eq', Int.ofNat_eq_natCast]; rfl
        · simp only [beq_false h1, beq_true h2, ble_false h3, cond_true, cond_false,
            Option.some.injEq, reduceCtorEq, false_implies, and_true, Bool.true_and]
          rintro f rfl m
          by_cases hm : h ≤ m
          · simp only [ble_true hm, cond_true, Int.add_def, ineg_eq, subNatNat_eq, Int.ofNat_eq_natCast]
            push_cast [Nat.cast_sub (show vP n a + 1 ≤ r by omega)]; ring
          · simp only [ble_false hm, cond_false, Int.add_def, ineg_eq, subNatNat_eq, Int.ofNat_eq_natCast]; rfl
      · simp [beq_false h1, beq_false h2]
  | assumption k =>
    simp only [rowFnO, rfAssumption, coefK]
    by_cases h1 : j ≤ k
    · simp [ble_true h1]
    · simp [ble_false h1, BZK]
  | releaseUpper r h => exact generic_spec _ hj rfl
  | tailUpper r h => exact generic_spec _ hj rfl
  | mean r => exact generic_spec _ hj rfl
  | union r => exact generic_spec _ hj rfl
  | edgeLower r => exact generic_spec _ hj rfl
  | edgeUpper r => exact generic_spec _ hj rfl


theorem rowFnO_spec {n a : ℕ} (ℓ : CLabel) {j : ℕ} (hj : 1 ≤ j) :
    (∀ f, rowFnO n a ℓ j = some f → ∀ m, f m = coefZ n a ℓ j m) ∧
      (rowFnO n a ℓ j = none → ∀ m, coefZ n a ℓ j m = 0) := by
  obtain ⟨h1, h2⟩ := rowFnO_specK (n := n) (a := a) ℓ hj
  exact ⟨fun f hf m => by rw [h1 f hf m, coefK_eq], fun hf m => by rw [← coefK_eq, h2 hf m]⟩

end ZhangKernel

end Erdos993Lean
