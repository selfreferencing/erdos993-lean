import Erdos993Lean.ZhangKernel.Direct

/-!
# Kernel-checked finite part: soundness of the slices

* `itemOKV_sound`: a passing item (direct criterion or generic certificate) gives
  `Cert.NoRecovery` (through `ZhangCertX.genericOK_sound`);
* **`checkAV_sound`**: `checkAV n a items = true` gives `Cert.NoRecovery n a k` for every
  `1 ≤ k < ⌊(2a+1)/3⌋`, for arbitrary items;
* **`checkOrderV_sound`**: `checkOrderV n a₀ L = true` gives `Cert.NoRecovery n a k` for every
  `a₀ ≤ a < n` and every such `k`.
-/

namespace Erdos993Lean

namespace ZhangKernel

open ZhangCertX Finset

open Zhang.Cert in
/-- A passing item gives no recovery. -/
theorem itemOKV_sound {n a k : ℕ} {it : TItem} (h : itemOKV n a k it = true) : NoRecovery n a k := by
  cases it with
  | direct hh => exact genericOK_sound (genericOK_of_directV h)
  | gen kind σ rows => exact genericOK_sound (genericOK_of_genericOKV h)

open Zhang.Cert in
theorem checkKsV_sound {n a : ℕ} (c : ℕ) : ∀ {k₀ : ℕ} {items : List TItem},
    checkKsV n a k₀ c items = true → ∀ k, k₀ ≤ k → k < k₀ + c → NoRecovery n a k := by
  induction c with
  | zero => intro k₀ items _ k h1 h2; omega
  | succ c ih =>
    intro k₀ items h k h1 h2
    cases items with
    | nil => simp [checkKsV] at h
    | cons it rest =>
      simp only [checkKsV, Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact itemOKV_sound h.1
      · exact ih h.2 k (by simp only [Nat.add_eq]; omega) (by simp only [Nat.add_eq]; omega)

open Zhang.Cert in
/-- **The check of `(n, a)`** gives no recovery on every `1 ≤ k < ⌊(2a+1)/3⌋`. -/
theorem checkAV_sound {n a : ℕ} {items : List TItem} (h : checkAV n a items = true) :
    ∀ k, 1 ≤ k → k < (2 * a + 1) / 3 → NoRecovery n a k := by
  intro k h1 h2
  refine checkKsV_sound _ h k h1 ?_
  simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq, ndiv_eq]
  omega

open Zhang.Cert in
/-- **The check of an order** gives no recovery on every `(a, k)` with `a₀ ≤ a < n`. -/
theorem checkOrderV_sound {n : ℕ} : ∀ {a₀ : ℕ} {L : List (List TItem)},
    checkOrderV n a₀ L = true → ∀ a, a₀ ≤ a → a < n → ∀ k, 1 ≤ k → k < (2 * a + 1) / 3 →
      NoRecovery n a k := by
  intro a₀ L
  induction L generalizing a₀ with
  | nil =>
    intro h a h1 h2
    simp only [checkOrderV] at h
    have := Nat.eq_of_beq_eq_true h
    omega
  | cons items rest ih =>
    intro h a h1 h2
    simp only [checkOrderV, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact checkAV_sound h.1
    · exact ih h.2 a (by simp only [Nat.add_eq]; omega) h2

end ZhangKernel

end Erdos993Lean
