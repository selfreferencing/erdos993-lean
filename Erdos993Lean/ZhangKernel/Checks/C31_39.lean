import Erdos993Lean.ZhangKernel.Data.O31_39

/-!
# Kernel-checked finite part: the checks of the orders 31 to 39

Every `check_n_a` is proved by `decide +kernel`: the Lean kernel evaluates the Boolean check
`checkAV n a items_n_a` itself (no compiled code, no `Lean.ofReduceBool`).  One declaration
per `(n, a)`, so that the kernel's caches (released between declarations) stay small; the
declarations are checked one after another (`Elab.async false`).  `order_n` collects them
by rewriting (no further evaluation).  Soundness: `ZhangKernel/Sound.lean`.
-/

namespace Erdos993Lean

namespace ZhangKernel

set_option Elab.async false

-- Report the kernel's evaluation time of each check ("type checking took ...").
set_option profiler true
set_option profiler.threshold 200

theorem check_31_16 : checkAV 31 16 items_31_16 = true := by decide +kernel

theorem check_31_17 : checkAV 31 17 items_31_17 = true := by decide +kernel

theorem check_31_18 : checkAV 31 18 items_31_18 = true := by decide +kernel

theorem check_31_19 : checkAV 31 19 items_31_19 = true := by decide +kernel

theorem check_31_20 : checkAV 31 20 items_31_20 = true := by decide +kernel

theorem check_31_21 : checkAV 31 21 items_31_21 = true := by decide +kernel

theorem check_31_22 : checkAV 31 22 items_31_22 = true := by decide +kernel

theorem check_31_23 : checkAV 31 23 items_31_23 = true := by decide +kernel

theorem check_31_24 : checkAV 31 24 items_31_24 = true := by decide +kernel

theorem check_31_25 : checkAV 31 25 items_31_25 = true := by decide +kernel

theorem check_31_26 : checkAV 31 26 items_31_26 = true := by decide +kernel

theorem check_31_27 : checkAV 31 27 items_31_27 = true := by decide +kernel

theorem check_31_28 : checkAV 31 28 items_31_28 = true := by decide +kernel

theorem check_31_29 : checkAV 31 29 items_31_29 = true := by decide +kernel

theorem check_31_30 : checkAV 31 30 items_31_30 = true := by decide +kernel

/-- The check of the order 31. -/
theorem order_31 : checkOrderV 31 16 [items_31_16, items_31_17, items_31_18, items_31_19, items_31_20, items_31_21, items_31_22, items_31_23, items_31_24, items_31_25, items_31_26, items_31_27, items_31_28, items_31_29, items_31_30] = true := by
  simp only [checkOrderV, check_31_16, check_31_17, check_31_18, check_31_19, check_31_20, check_31_21, check_31_22, check_31_23, check_31_24, check_31_25, check_31_26, check_31_27, check_31_28, check_31_29, check_31_30, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_32_16 : checkAV 32 16 items_32_16 = true := by decide +kernel

theorem check_32_17 : checkAV 32 17 items_32_17 = true := by decide +kernel

theorem check_32_18 : checkAV 32 18 items_32_18 = true := by decide +kernel

theorem check_32_19 : checkAV 32 19 items_32_19 = true := by decide +kernel

theorem check_32_20 : checkAV 32 20 items_32_20 = true := by decide +kernel

theorem check_32_21 : checkAV 32 21 items_32_21 = true := by decide +kernel

theorem check_32_22 : checkAV 32 22 items_32_22 = true := by decide +kernel

theorem check_32_23 : checkAV 32 23 items_32_23 = true := by decide +kernel

theorem check_32_24 : checkAV 32 24 items_32_24 = true := by decide +kernel

theorem check_32_25 : checkAV 32 25 items_32_25 = true := by decide +kernel

theorem check_32_26 : checkAV 32 26 items_32_26 = true := by decide +kernel

theorem check_32_27 : checkAV 32 27 items_32_27 = true := by decide +kernel

theorem check_32_28 : checkAV 32 28 items_32_28 = true := by decide +kernel

theorem check_32_29 : checkAV 32 29 items_32_29 = true := by decide +kernel

theorem check_32_30 : checkAV 32 30 items_32_30 = true := by decide +kernel

theorem check_32_31 : checkAV 32 31 items_32_31 = true := by decide +kernel

/-- The check of the order 32. -/
theorem order_32 : checkOrderV 32 16 [items_32_16, items_32_17, items_32_18, items_32_19, items_32_20, items_32_21, items_32_22, items_32_23, items_32_24, items_32_25, items_32_26, items_32_27, items_32_28, items_32_29, items_32_30, items_32_31] = true := by
  simp only [checkOrderV, check_32_16, check_32_17, check_32_18, check_32_19, check_32_20, check_32_21, check_32_22, check_32_23, check_32_24, check_32_25, check_32_26, check_32_27, check_32_28, check_32_29, check_32_30, check_32_31, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_33_17 : checkAV 33 17 items_33_17 = true := by decide +kernel

theorem check_33_18 : checkAV 33 18 items_33_18 = true := by decide +kernel

theorem check_33_19 : checkAV 33 19 items_33_19 = true := by decide +kernel

theorem check_33_20 : checkAV 33 20 items_33_20 = true := by decide +kernel

theorem check_33_21 : checkAV 33 21 items_33_21 = true := by decide +kernel

theorem check_33_22 : checkAV 33 22 items_33_22 = true := by decide +kernel

theorem check_33_23 : checkAV 33 23 items_33_23 = true := by decide +kernel

theorem check_33_24 : checkAV 33 24 items_33_24 = true := by decide +kernel

theorem check_33_25 : checkAV 33 25 items_33_25 = true := by decide +kernel

theorem check_33_26 : checkAV 33 26 items_33_26 = true := by decide +kernel

theorem check_33_27 : checkAV 33 27 items_33_27 = true := by decide +kernel

theorem check_33_28 : checkAV 33 28 items_33_28 = true := by decide +kernel

theorem check_33_29 : checkAV 33 29 items_33_29 = true := by decide +kernel

theorem check_33_30 : checkAV 33 30 items_33_30 = true := by decide +kernel

theorem check_33_31 : checkAV 33 31 items_33_31 = true := by decide +kernel

theorem check_33_32 : checkAV 33 32 items_33_32 = true := by decide +kernel

/-- The check of the order 33. -/
theorem order_33 : checkOrderV 33 17 [items_33_17, items_33_18, items_33_19, items_33_20, items_33_21, items_33_22, items_33_23, items_33_24, items_33_25, items_33_26, items_33_27, items_33_28, items_33_29, items_33_30, items_33_31, items_33_32] = true := by
  simp only [checkOrderV, check_33_17, check_33_18, check_33_19, check_33_20, check_33_21, check_33_22, check_33_23, check_33_24, check_33_25, check_33_26, check_33_27, check_33_28, check_33_29, check_33_30, check_33_31, check_33_32, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_34_17 : checkAV 34 17 items_34_17 = true := by decide +kernel

theorem check_34_18 : checkAV 34 18 items_34_18 = true := by decide +kernel

theorem check_34_19 : checkAV 34 19 items_34_19 = true := by decide +kernel

theorem check_34_20 : checkAV 34 20 items_34_20 = true := by decide +kernel

theorem check_34_21 : checkAV 34 21 items_34_21 = true := by decide +kernel

theorem check_34_22 : checkAV 34 22 items_34_22 = true := by decide +kernel

theorem check_34_23 : checkAV 34 23 items_34_23 = true := by decide +kernel

theorem check_34_24 : checkAV 34 24 items_34_24 = true := by decide +kernel

theorem check_34_25 : checkAV 34 25 items_34_25 = true := by decide +kernel

theorem check_34_26 : checkAV 34 26 items_34_26 = true := by decide +kernel

theorem check_34_27 : checkAV 34 27 items_34_27 = true := by decide +kernel

theorem check_34_28 : checkAV 34 28 items_34_28 = true := by decide +kernel

theorem check_34_29 : checkAV 34 29 items_34_29 = true := by decide +kernel

theorem check_34_30 : checkAV 34 30 items_34_30 = true := by decide +kernel

theorem check_34_31 : checkAV 34 31 items_34_31 = true := by decide +kernel

theorem check_34_32 : checkAV 34 32 items_34_32 = true := by decide +kernel

theorem check_34_33 : checkAV 34 33 items_34_33 = true := by decide +kernel

/-- The check of the order 34. -/
theorem order_34 : checkOrderV 34 17 [items_34_17, items_34_18, items_34_19, items_34_20, items_34_21, items_34_22, items_34_23, items_34_24, items_34_25, items_34_26, items_34_27, items_34_28, items_34_29, items_34_30, items_34_31, items_34_32, items_34_33] = true := by
  simp only [checkOrderV, check_34_17, check_34_18, check_34_19, check_34_20, check_34_21, check_34_22, check_34_23, check_34_24, check_34_25, check_34_26, check_34_27, check_34_28, check_34_29, check_34_30, check_34_31, check_34_32, check_34_33, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_35_18 : checkAV 35 18 items_35_18 = true := by decide +kernel

theorem check_35_19 : checkAV 35 19 items_35_19 = true := by decide +kernel

theorem check_35_20 : checkAV 35 20 items_35_20 = true := by decide +kernel

theorem check_35_21 : checkAV 35 21 items_35_21 = true := by decide +kernel

theorem check_35_22 : checkAV 35 22 items_35_22 = true := by decide +kernel

theorem check_35_23 : checkAV 35 23 items_35_23 = true := by decide +kernel

theorem check_35_24 : checkAV 35 24 items_35_24 = true := by decide +kernel

theorem check_35_25 : checkAV 35 25 items_35_25 = true := by decide +kernel

theorem check_35_26 : checkAV 35 26 items_35_26 = true := by decide +kernel

theorem check_35_27 : checkAV 35 27 items_35_27 = true := by decide +kernel

theorem check_35_28 : checkAV 35 28 items_35_28 = true := by decide +kernel

theorem check_35_29 : checkAV 35 29 items_35_29 = true := by decide +kernel

theorem check_35_30 : checkAV 35 30 items_35_30 = true := by decide +kernel

theorem check_35_31 : checkAV 35 31 items_35_31 = true := by decide +kernel

theorem check_35_32 : checkAV 35 32 items_35_32 = true := by decide +kernel

theorem check_35_33 : checkAV 35 33 items_35_33 = true := by decide +kernel

theorem check_35_34 : checkAV 35 34 items_35_34 = true := by decide +kernel

/-- The check of the order 35. -/
theorem order_35 : checkOrderV 35 18 [items_35_18, items_35_19, items_35_20, items_35_21, items_35_22, items_35_23, items_35_24, items_35_25, items_35_26, items_35_27, items_35_28, items_35_29, items_35_30, items_35_31, items_35_32, items_35_33, items_35_34] = true := by
  simp only [checkOrderV, check_35_18, check_35_19, check_35_20, check_35_21, check_35_22, check_35_23, check_35_24, check_35_25, check_35_26, check_35_27, check_35_28, check_35_29, check_35_30, check_35_31, check_35_32, check_35_33, check_35_34, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_36_18 : checkAV 36 18 items_36_18 = true := by decide +kernel

theorem check_36_19 : checkAV 36 19 items_36_19 = true := by decide +kernel

theorem check_36_20 : checkAV 36 20 items_36_20 = true := by decide +kernel

theorem check_36_21 : checkAV 36 21 items_36_21 = true := by decide +kernel

theorem check_36_22 : checkAV 36 22 items_36_22 = true := by decide +kernel

theorem check_36_23 : checkAV 36 23 items_36_23 = true := by decide +kernel

theorem check_36_24 : checkAV 36 24 items_36_24 = true := by decide +kernel

theorem check_36_25 : checkAV 36 25 items_36_25 = true := by decide +kernel

theorem check_36_26 : checkAV 36 26 items_36_26 = true := by decide +kernel

theorem check_36_27 : checkAV 36 27 items_36_27 = true := by decide +kernel

theorem check_36_28 : checkAV 36 28 items_36_28 = true := by decide +kernel

theorem check_36_29 : checkAV 36 29 items_36_29 = true := by decide +kernel

theorem check_36_30 : checkAV 36 30 items_36_30 = true := by decide +kernel

theorem check_36_31 : checkAV 36 31 items_36_31 = true := by decide +kernel

theorem check_36_32 : checkAV 36 32 items_36_32 = true := by decide +kernel

theorem check_36_33 : checkAV 36 33 items_36_33 = true := by decide +kernel

theorem check_36_34 : checkAV 36 34 items_36_34 = true := by decide +kernel

theorem check_36_35 : checkAV 36 35 items_36_35 = true := by decide +kernel

/-- The check of the order 36. -/
theorem order_36 : checkOrderV 36 18 [items_36_18, items_36_19, items_36_20, items_36_21, items_36_22, items_36_23, items_36_24, items_36_25, items_36_26, items_36_27, items_36_28, items_36_29, items_36_30, items_36_31, items_36_32, items_36_33, items_36_34, items_36_35] = true := by
  simp only [checkOrderV, check_36_18, check_36_19, check_36_20, check_36_21, check_36_22, check_36_23, check_36_24, check_36_25, check_36_26, check_36_27, check_36_28, check_36_29, check_36_30, check_36_31, check_36_32, check_36_33, check_36_34, check_36_35, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_37_19 : checkAV 37 19 items_37_19 = true := by decide +kernel

theorem check_37_20 : checkAV 37 20 items_37_20 = true := by decide +kernel

theorem check_37_21 : checkAV 37 21 items_37_21 = true := by decide +kernel

theorem check_37_22 : checkAV 37 22 items_37_22 = true := by decide +kernel

theorem check_37_23 : checkAV 37 23 items_37_23 = true := by decide +kernel

theorem check_37_24 : checkAV 37 24 items_37_24 = true := by decide +kernel

theorem check_37_25 : checkAV 37 25 items_37_25 = true := by decide +kernel

theorem check_37_26 : checkAV 37 26 items_37_26 = true := by decide +kernel

theorem check_37_27 : checkAV 37 27 items_37_27 = true := by decide +kernel

theorem check_37_28 : checkAV 37 28 items_37_28 = true := by decide +kernel

theorem check_37_29 : checkAV 37 29 items_37_29 = true := by decide +kernel

theorem check_37_30 : checkAV 37 30 items_37_30 = true := by decide +kernel

theorem check_37_31 : checkAV 37 31 items_37_31 = true := by decide +kernel

theorem check_37_32 : checkAV 37 32 items_37_32 = true := by decide +kernel

theorem check_37_33 : checkAV 37 33 items_37_33 = true := by decide +kernel

theorem check_37_34 : checkAV 37 34 items_37_34 = true := by decide +kernel

theorem check_37_35 : checkAV 37 35 items_37_35 = true := by decide +kernel

theorem check_37_36 : checkAV 37 36 items_37_36 = true := by decide +kernel

/-- The check of the order 37. -/
theorem order_37 : checkOrderV 37 19 [items_37_19, items_37_20, items_37_21, items_37_22, items_37_23, items_37_24, items_37_25, items_37_26, items_37_27, items_37_28, items_37_29, items_37_30, items_37_31, items_37_32, items_37_33, items_37_34, items_37_35, items_37_36] = true := by
  simp only [checkOrderV, check_37_19, check_37_20, check_37_21, check_37_22, check_37_23, check_37_24, check_37_25, check_37_26, check_37_27, check_37_28, check_37_29, check_37_30, check_37_31, check_37_32, check_37_33, check_37_34, check_37_35, check_37_36, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_38_19 : checkAV 38 19 items_38_19 = true := by decide +kernel

theorem check_38_20 : checkAV 38 20 items_38_20 = true := by decide +kernel

theorem check_38_21 : checkAV 38 21 items_38_21 = true := by decide +kernel

theorem check_38_22 : checkAV 38 22 items_38_22 = true := by decide +kernel

theorem check_38_23 : checkAV 38 23 items_38_23 = true := by decide +kernel

theorem check_38_24 : checkAV 38 24 items_38_24 = true := by decide +kernel

theorem check_38_25 : checkAV 38 25 items_38_25 = true := by decide +kernel

theorem check_38_26 : checkAV 38 26 items_38_26 = true := by decide +kernel

theorem check_38_27 : checkAV 38 27 items_38_27 = true := by decide +kernel

theorem check_38_28 : checkAV 38 28 items_38_28 = true := by decide +kernel

theorem check_38_29 : checkAV 38 29 items_38_29 = true := by decide +kernel

theorem check_38_30 : checkAV 38 30 items_38_30 = true := by decide +kernel

theorem check_38_31 : checkAV 38 31 items_38_31 = true := by decide +kernel

theorem check_38_32 : checkAV 38 32 items_38_32 = true := by decide +kernel

theorem check_38_33 : checkAV 38 33 items_38_33 = true := by decide +kernel

theorem check_38_34 : checkAV 38 34 items_38_34 = true := by decide +kernel

theorem check_38_35 : checkAV 38 35 items_38_35 = true := by decide +kernel

theorem check_38_36 : checkAV 38 36 items_38_36 = true := by decide +kernel

theorem check_38_37 : checkAV 38 37 items_38_37 = true := by decide +kernel

/-- The check of the order 38. -/
theorem order_38 : checkOrderV 38 19 [items_38_19, items_38_20, items_38_21, items_38_22, items_38_23, items_38_24, items_38_25, items_38_26, items_38_27, items_38_28, items_38_29, items_38_30, items_38_31, items_38_32, items_38_33, items_38_34, items_38_35, items_38_36, items_38_37] = true := by
  simp only [checkOrderV, check_38_19, check_38_20, check_38_21, check_38_22, check_38_23, check_38_24, check_38_25, check_38_26, check_38_27, check_38_28, check_38_29, check_38_30, check_38_31, check_38_32, check_38_33, check_38_34, check_38_35, check_38_36, check_38_37, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_39_20 : checkAV 39 20 items_39_20 = true := by decide +kernel

theorem check_39_21 : checkAV 39 21 items_39_21 = true := by decide +kernel

theorem check_39_22 : checkAV 39 22 items_39_22 = true := by decide +kernel

theorem check_39_23 : checkAV 39 23 items_39_23 = true := by decide +kernel

theorem check_39_24 : checkAV 39 24 items_39_24 = true := by decide +kernel

theorem check_39_25 : checkAV 39 25 items_39_25 = true := by decide +kernel

theorem check_39_26 : checkAV 39 26 items_39_26 = true := by decide +kernel

theorem check_39_27 : checkAV 39 27 items_39_27 = true := by decide +kernel

theorem check_39_28 : checkAV 39 28 items_39_28 = true := by decide +kernel

theorem check_39_29 : checkAV 39 29 items_39_29 = true := by decide +kernel

theorem check_39_30 : checkAV 39 30 items_39_30 = true := by decide +kernel

theorem check_39_31 : checkAV 39 31 items_39_31 = true := by decide +kernel

theorem check_39_32 : checkAV 39 32 items_39_32 = true := by decide +kernel

theorem check_39_33 : checkAV 39 33 items_39_33 = true := by decide +kernel

theorem check_39_34 : checkAV 39 34 items_39_34 = true := by decide +kernel

theorem check_39_35 : checkAV 39 35 items_39_35 = true := by decide +kernel

theorem check_39_36 : checkAV 39 36 items_39_36 = true := by decide +kernel

theorem check_39_37 : checkAV 39 37 items_39_37 = true := by decide +kernel

theorem check_39_38 : checkAV 39 38 items_39_38 = true := by decide +kernel

/-- The check of the order 39. -/
theorem order_39 : checkOrderV 39 20 [items_39_20, items_39_21, items_39_22, items_39_23, items_39_24, items_39_25, items_39_26, items_39_27, items_39_28, items_39_29, items_39_30, items_39_31, items_39_32, items_39_33, items_39_34, items_39_35, items_39_36, items_39_37, items_39_38] = true := by
  simp only [checkOrderV, check_39_20, check_39_21, check_39_22, check_39_23, check_39_24, check_39_25, check_39_26, check_39_27, check_39_28, check_39_29, check_39_30, check_39_31, check_39_32, check_39_33, check_39_34, check_39_35, check_39_36, check_39_37, check_39_38, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
