import Erdos993Lean.ZhangKernel.Data.O21_30

/-!
# Kernel-checked finite part: the checks of the orders 21 to 30

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

theorem check_21_11 : checkAV 21 11 items_21_11 = true := by decide +kernel

theorem check_21_12 : checkAV 21 12 items_21_12 = true := by decide +kernel

theorem check_21_13 : checkAV 21 13 items_21_13 = true := by decide +kernel

theorem check_21_14 : checkAV 21 14 items_21_14 = true := by decide +kernel

theorem check_21_15 : checkAV 21 15 items_21_15 = true := by decide +kernel

theorem check_21_16 : checkAV 21 16 items_21_16 = true := by decide +kernel

theorem check_21_17 : checkAV 21 17 items_21_17 = true := by decide +kernel

theorem check_21_18 : checkAV 21 18 items_21_18 = true := by decide +kernel

theorem check_21_19 : checkAV 21 19 items_21_19 = true := by decide +kernel

theorem check_21_20 : checkAV 21 20 items_21_20 = true := by decide +kernel

/-- The check of the order 21. -/
theorem order_21 : checkOrderV 21 11 [items_21_11, items_21_12, items_21_13, items_21_14, items_21_15, items_21_16, items_21_17, items_21_18, items_21_19, items_21_20] = true := by
  simp only [checkOrderV, check_21_11, check_21_12, check_21_13, check_21_14, check_21_15, check_21_16, check_21_17, check_21_18, check_21_19, check_21_20, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_22_11 : checkAV 22 11 items_22_11 = true := by decide +kernel

theorem check_22_12 : checkAV 22 12 items_22_12 = true := by decide +kernel

theorem check_22_13 : checkAV 22 13 items_22_13 = true := by decide +kernel

theorem check_22_14 : checkAV 22 14 items_22_14 = true := by decide +kernel

theorem check_22_15 : checkAV 22 15 items_22_15 = true := by decide +kernel

theorem check_22_16 : checkAV 22 16 items_22_16 = true := by decide +kernel

theorem check_22_17 : checkAV 22 17 items_22_17 = true := by decide +kernel

theorem check_22_18 : checkAV 22 18 items_22_18 = true := by decide +kernel

theorem check_22_19 : checkAV 22 19 items_22_19 = true := by decide +kernel

theorem check_22_20 : checkAV 22 20 items_22_20 = true := by decide +kernel

theorem check_22_21 : checkAV 22 21 items_22_21 = true := by decide +kernel

/-- The check of the order 22. -/
theorem order_22 : checkOrderV 22 11 [items_22_11, items_22_12, items_22_13, items_22_14, items_22_15, items_22_16, items_22_17, items_22_18, items_22_19, items_22_20, items_22_21] = true := by
  simp only [checkOrderV, check_22_11, check_22_12, check_22_13, check_22_14, check_22_15, check_22_16, check_22_17, check_22_18, check_22_19, check_22_20, check_22_21, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_23_12 : checkAV 23 12 items_23_12 = true := by decide +kernel

theorem check_23_13 : checkAV 23 13 items_23_13 = true := by decide +kernel

theorem check_23_14 : checkAV 23 14 items_23_14 = true := by decide +kernel

theorem check_23_15 : checkAV 23 15 items_23_15 = true := by decide +kernel

theorem check_23_16 : checkAV 23 16 items_23_16 = true := by decide +kernel

theorem check_23_17 : checkAV 23 17 items_23_17 = true := by decide +kernel

theorem check_23_18 : checkAV 23 18 items_23_18 = true := by decide +kernel

theorem check_23_19 : checkAV 23 19 items_23_19 = true := by decide +kernel

theorem check_23_20 : checkAV 23 20 items_23_20 = true := by decide +kernel

theorem check_23_21 : checkAV 23 21 items_23_21 = true := by decide +kernel

theorem check_23_22 : checkAV 23 22 items_23_22 = true := by decide +kernel

/-- The check of the order 23. -/
theorem order_23 : checkOrderV 23 12 [items_23_12, items_23_13, items_23_14, items_23_15, items_23_16, items_23_17, items_23_18, items_23_19, items_23_20, items_23_21, items_23_22] = true := by
  simp only [checkOrderV, check_23_12, check_23_13, check_23_14, check_23_15, check_23_16, check_23_17, check_23_18, check_23_19, check_23_20, check_23_21, check_23_22, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_24_12 : checkAV 24 12 items_24_12 = true := by decide +kernel

theorem check_24_13 : checkAV 24 13 items_24_13 = true := by decide +kernel

theorem check_24_14 : checkAV 24 14 items_24_14 = true := by decide +kernel

theorem check_24_15 : checkAV 24 15 items_24_15 = true := by decide +kernel

theorem check_24_16 : checkAV 24 16 items_24_16 = true := by decide +kernel

theorem check_24_17 : checkAV 24 17 items_24_17 = true := by decide +kernel

theorem check_24_18 : checkAV 24 18 items_24_18 = true := by decide +kernel

theorem check_24_19 : checkAV 24 19 items_24_19 = true := by decide +kernel

theorem check_24_20 : checkAV 24 20 items_24_20 = true := by decide +kernel

theorem check_24_21 : checkAV 24 21 items_24_21 = true := by decide +kernel

theorem check_24_22 : checkAV 24 22 items_24_22 = true := by decide +kernel

theorem check_24_23 : checkAV 24 23 items_24_23 = true := by decide +kernel

/-- The check of the order 24. -/
theorem order_24 : checkOrderV 24 12 [items_24_12, items_24_13, items_24_14, items_24_15, items_24_16, items_24_17, items_24_18, items_24_19, items_24_20, items_24_21, items_24_22, items_24_23] = true := by
  simp only [checkOrderV, check_24_12, check_24_13, check_24_14, check_24_15, check_24_16, check_24_17, check_24_18, check_24_19, check_24_20, check_24_21, check_24_22, check_24_23, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_25_13 : checkAV 25 13 items_25_13 = true := by decide +kernel

theorem check_25_14 : checkAV 25 14 items_25_14 = true := by decide +kernel

theorem check_25_15 : checkAV 25 15 items_25_15 = true := by decide +kernel

theorem check_25_16 : checkAV 25 16 items_25_16 = true := by decide +kernel

theorem check_25_17 : checkAV 25 17 items_25_17 = true := by decide +kernel

theorem check_25_18 : checkAV 25 18 items_25_18 = true := by decide +kernel

theorem check_25_19 : checkAV 25 19 items_25_19 = true := by decide +kernel

theorem check_25_20 : checkAV 25 20 items_25_20 = true := by decide +kernel

theorem check_25_21 : checkAV 25 21 items_25_21 = true := by decide +kernel

theorem check_25_22 : checkAV 25 22 items_25_22 = true := by decide +kernel

theorem check_25_23 : checkAV 25 23 items_25_23 = true := by decide +kernel

theorem check_25_24 : checkAV 25 24 items_25_24 = true := by decide +kernel

/-- The check of the order 25. -/
theorem order_25 : checkOrderV 25 13 [items_25_13, items_25_14, items_25_15, items_25_16, items_25_17, items_25_18, items_25_19, items_25_20, items_25_21, items_25_22, items_25_23, items_25_24] = true := by
  simp only [checkOrderV, check_25_13, check_25_14, check_25_15, check_25_16, check_25_17, check_25_18, check_25_19, check_25_20, check_25_21, check_25_22, check_25_23, check_25_24, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_26_13 : checkAV 26 13 items_26_13 = true := by decide +kernel

theorem check_26_14 : checkAV 26 14 items_26_14 = true := by decide +kernel

theorem check_26_15 : checkAV 26 15 items_26_15 = true := by decide +kernel

theorem check_26_16 : checkAV 26 16 items_26_16 = true := by decide +kernel

theorem check_26_17 : checkAV 26 17 items_26_17 = true := by decide +kernel

theorem check_26_18 : checkAV 26 18 items_26_18 = true := by decide +kernel

theorem check_26_19 : checkAV 26 19 items_26_19 = true := by decide +kernel

theorem check_26_20 : checkAV 26 20 items_26_20 = true := by decide +kernel

theorem check_26_21 : checkAV 26 21 items_26_21 = true := by decide +kernel

theorem check_26_22 : checkAV 26 22 items_26_22 = true := by decide +kernel

theorem check_26_23 : checkAV 26 23 items_26_23 = true := by decide +kernel

theorem check_26_24 : checkAV 26 24 items_26_24 = true := by decide +kernel

theorem check_26_25 : checkAV 26 25 items_26_25 = true := by decide +kernel

/-- The check of the order 26. -/
theorem order_26 : checkOrderV 26 13 [items_26_13, items_26_14, items_26_15, items_26_16, items_26_17, items_26_18, items_26_19, items_26_20, items_26_21, items_26_22, items_26_23, items_26_24, items_26_25] = true := by
  simp only [checkOrderV, check_26_13, check_26_14, check_26_15, check_26_16, check_26_17, check_26_18, check_26_19, check_26_20, check_26_21, check_26_22, check_26_23, check_26_24, check_26_25, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_27_14 : checkAV 27 14 items_27_14 = true := by decide +kernel

theorem check_27_15 : checkAV 27 15 items_27_15 = true := by decide +kernel

theorem check_27_16 : checkAV 27 16 items_27_16 = true := by decide +kernel

theorem check_27_17 : checkAV 27 17 items_27_17 = true := by decide +kernel

theorem check_27_18 : checkAV 27 18 items_27_18 = true := by decide +kernel

theorem check_27_19 : checkAV 27 19 items_27_19 = true := by decide +kernel

theorem check_27_20 : checkAV 27 20 items_27_20 = true := by decide +kernel

theorem check_27_21 : checkAV 27 21 items_27_21 = true := by decide +kernel

theorem check_27_22 : checkAV 27 22 items_27_22 = true := by decide +kernel

theorem check_27_23 : checkAV 27 23 items_27_23 = true := by decide +kernel

theorem check_27_24 : checkAV 27 24 items_27_24 = true := by decide +kernel

theorem check_27_25 : checkAV 27 25 items_27_25 = true := by decide +kernel

theorem check_27_26 : checkAV 27 26 items_27_26 = true := by decide +kernel

/-- The check of the order 27. -/
theorem order_27 : checkOrderV 27 14 [items_27_14, items_27_15, items_27_16, items_27_17, items_27_18, items_27_19, items_27_20, items_27_21, items_27_22, items_27_23, items_27_24, items_27_25, items_27_26] = true := by
  simp only [checkOrderV, check_27_14, check_27_15, check_27_16, check_27_17, check_27_18, check_27_19, check_27_20, check_27_21, check_27_22, check_27_23, check_27_24, check_27_25, check_27_26, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_28_14 : checkAV 28 14 items_28_14 = true := by decide +kernel

theorem check_28_15 : checkAV 28 15 items_28_15 = true := by decide +kernel

theorem check_28_16 : checkAV 28 16 items_28_16 = true := by decide +kernel

theorem check_28_17 : checkAV 28 17 items_28_17 = true := by decide +kernel

theorem check_28_18 : checkAV 28 18 items_28_18 = true := by decide +kernel

theorem check_28_19 : checkAV 28 19 items_28_19 = true := by decide +kernel

theorem check_28_20 : checkAV 28 20 items_28_20 = true := by decide +kernel

theorem check_28_21 : checkAV 28 21 items_28_21 = true := by decide +kernel

theorem check_28_22 : checkAV 28 22 items_28_22 = true := by decide +kernel

theorem check_28_23 : checkAV 28 23 items_28_23 = true := by decide +kernel

theorem check_28_24 : checkAV 28 24 items_28_24 = true := by decide +kernel

theorem check_28_25 : checkAV 28 25 items_28_25 = true := by decide +kernel

theorem check_28_26 : checkAV 28 26 items_28_26 = true := by decide +kernel

theorem check_28_27 : checkAV 28 27 items_28_27 = true := by decide +kernel

/-- The check of the order 28. -/
theorem order_28 : checkOrderV 28 14 [items_28_14, items_28_15, items_28_16, items_28_17, items_28_18, items_28_19, items_28_20, items_28_21, items_28_22, items_28_23, items_28_24, items_28_25, items_28_26, items_28_27] = true := by
  simp only [checkOrderV, check_28_14, check_28_15, check_28_16, check_28_17, check_28_18, check_28_19, check_28_20, check_28_21, check_28_22, check_28_23, check_28_24, check_28_25, check_28_26, check_28_27, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_29_15 : checkAV 29 15 items_29_15 = true := by decide +kernel

theorem check_29_16 : checkAV 29 16 items_29_16 = true := by decide +kernel

theorem check_29_17 : checkAV 29 17 items_29_17 = true := by decide +kernel

theorem check_29_18 : checkAV 29 18 items_29_18 = true := by decide +kernel

theorem check_29_19 : checkAV 29 19 items_29_19 = true := by decide +kernel

theorem check_29_20 : checkAV 29 20 items_29_20 = true := by decide +kernel

theorem check_29_21 : checkAV 29 21 items_29_21 = true := by decide +kernel

theorem check_29_22 : checkAV 29 22 items_29_22 = true := by decide +kernel

theorem check_29_23 : checkAV 29 23 items_29_23 = true := by decide +kernel

theorem check_29_24 : checkAV 29 24 items_29_24 = true := by decide +kernel

theorem check_29_25 : checkAV 29 25 items_29_25 = true := by decide +kernel

theorem check_29_26 : checkAV 29 26 items_29_26 = true := by decide +kernel

theorem check_29_27 : checkAV 29 27 items_29_27 = true := by decide +kernel

theorem check_29_28 : checkAV 29 28 items_29_28 = true := by decide +kernel

/-- The check of the order 29. -/
theorem order_29 : checkOrderV 29 15 [items_29_15, items_29_16, items_29_17, items_29_18, items_29_19, items_29_20, items_29_21, items_29_22, items_29_23, items_29_24, items_29_25, items_29_26, items_29_27, items_29_28] = true := by
  simp only [checkOrderV, check_29_15, check_29_16, check_29_17, check_29_18, check_29_19, check_29_20, check_29_21, check_29_22, check_29_23, check_29_24, check_29_25, check_29_26, check_29_27, check_29_28, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_30_15 : checkAV 30 15 items_30_15 = true := by decide +kernel

theorem check_30_16 : checkAV 30 16 items_30_16 = true := by decide +kernel

theorem check_30_17 : checkAV 30 17 items_30_17 = true := by decide +kernel

theorem check_30_18 : checkAV 30 18 items_30_18 = true := by decide +kernel

theorem check_30_19 : checkAV 30 19 items_30_19 = true := by decide +kernel

theorem check_30_20 : checkAV 30 20 items_30_20 = true := by decide +kernel

theorem check_30_21 : checkAV 30 21 items_30_21 = true := by decide +kernel

theorem check_30_22 : checkAV 30 22 items_30_22 = true := by decide +kernel

theorem check_30_23 : checkAV 30 23 items_30_23 = true := by decide +kernel

theorem check_30_24 : checkAV 30 24 items_30_24 = true := by decide +kernel

theorem check_30_25 : checkAV 30 25 items_30_25 = true := by decide +kernel

theorem check_30_26 : checkAV 30 26 items_30_26 = true := by decide +kernel

theorem check_30_27 : checkAV 30 27 items_30_27 = true := by decide +kernel

theorem check_30_28 : checkAV 30 28 items_30_28 = true := by decide +kernel

theorem check_30_29 : checkAV 30 29 items_30_29 = true := by decide +kernel

/-- The check of the order 30. -/
theorem order_30 : checkOrderV 30 15 [items_30_15, items_30_16, items_30_17, items_30_18, items_30_19, items_30_20, items_30_21, items_30_22, items_30_23, items_30_24, items_30_25, items_30_26, items_30_27, items_30_28, items_30_29] = true := by
  simp only [checkOrderV, check_30_15, check_30_16, check_30_17, check_30_18, check_30_19, check_30_20, check_30_21, check_30_22, check_30_23, check_30_24, check_30_25, check_30_26, check_30_27, check_30_28, check_30_29, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
