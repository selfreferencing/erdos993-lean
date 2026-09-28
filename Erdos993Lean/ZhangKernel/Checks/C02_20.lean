import Erdos993Lean.ZhangKernel.Data.O02_20

/-!
# Kernel-checked finite part: the checks of the orders 2 to 20

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

theorem check_2_1 : checkAV 2 1 items_2_1 = true := by decide +kernel

/-- The check of the order 2. -/
theorem order_2 : checkOrderV 2 1 [items_2_1] = true := by
  simp only [checkOrderV, check_2_1, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_3_2 : checkAV 3 2 items_3_2 = true := by decide +kernel

/-- The check of the order 3. -/
theorem order_3 : checkOrderV 3 2 [items_3_2] = true := by
  simp only [checkOrderV, check_3_2, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_4_2 : checkAV 4 2 items_4_2 = true := by decide +kernel

theorem check_4_3 : checkAV 4 3 items_4_3 = true := by decide +kernel

/-- The check of the order 4. -/
theorem order_4 : checkOrderV 4 2 [items_4_2, items_4_3] = true := by
  simp only [checkOrderV, check_4_2, check_4_3, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_5_3 : checkAV 5 3 items_5_3 = true := by decide +kernel

theorem check_5_4 : checkAV 5 4 items_5_4 = true := by decide +kernel

/-- The check of the order 5. -/
theorem order_5 : checkOrderV 5 3 [items_5_3, items_5_4] = true := by
  simp only [checkOrderV, check_5_3, check_5_4, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_6_3 : checkAV 6 3 items_6_3 = true := by decide +kernel

theorem check_6_4 : checkAV 6 4 items_6_4 = true := by decide +kernel

theorem check_6_5 : checkAV 6 5 items_6_5 = true := by decide +kernel

/-- The check of the order 6. -/
theorem order_6 : checkOrderV 6 3 [items_6_3, items_6_4, items_6_5] = true := by
  simp only [checkOrderV, check_6_3, check_6_4, check_6_5, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_7_4 : checkAV 7 4 items_7_4 = true := by decide +kernel

theorem check_7_5 : checkAV 7 5 items_7_5 = true := by decide +kernel

theorem check_7_6 : checkAV 7 6 items_7_6 = true := by decide +kernel

/-- The check of the order 7. -/
theorem order_7 : checkOrderV 7 4 [items_7_4, items_7_5, items_7_6] = true := by
  simp only [checkOrderV, check_7_4, check_7_5, check_7_6, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_8_4 : checkAV 8 4 items_8_4 = true := by decide +kernel

theorem check_8_5 : checkAV 8 5 items_8_5 = true := by decide +kernel

theorem check_8_6 : checkAV 8 6 items_8_6 = true := by decide +kernel

theorem check_8_7 : checkAV 8 7 items_8_7 = true := by decide +kernel

/-- The check of the order 8. -/
theorem order_8 : checkOrderV 8 4 [items_8_4, items_8_5, items_8_6, items_8_7] = true := by
  simp only [checkOrderV, check_8_4, check_8_5, check_8_6, check_8_7, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_9_5 : checkAV 9 5 items_9_5 = true := by decide +kernel

theorem check_9_6 : checkAV 9 6 items_9_6 = true := by decide +kernel

theorem check_9_7 : checkAV 9 7 items_9_7 = true := by decide +kernel

theorem check_9_8 : checkAV 9 8 items_9_8 = true := by decide +kernel

/-- The check of the order 9. -/
theorem order_9 : checkOrderV 9 5 [items_9_5, items_9_6, items_9_7, items_9_8] = true := by
  simp only [checkOrderV, check_9_5, check_9_6, check_9_7, check_9_8, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_10_5 : checkAV 10 5 items_10_5 = true := by decide +kernel

theorem check_10_6 : checkAV 10 6 items_10_6 = true := by decide +kernel

theorem check_10_7 : checkAV 10 7 items_10_7 = true := by decide +kernel

theorem check_10_8 : checkAV 10 8 items_10_8 = true := by decide +kernel

theorem check_10_9 : checkAV 10 9 items_10_9 = true := by decide +kernel

/-- The check of the order 10. -/
theorem order_10 : checkOrderV 10 5 [items_10_5, items_10_6, items_10_7, items_10_8, items_10_9] = true := by
  simp only [checkOrderV, check_10_5, check_10_6, check_10_7, check_10_8, check_10_9, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_11_6 : checkAV 11 6 items_11_6 = true := by decide +kernel

theorem check_11_7 : checkAV 11 7 items_11_7 = true := by decide +kernel

theorem check_11_8 : checkAV 11 8 items_11_8 = true := by decide +kernel

theorem check_11_9 : checkAV 11 9 items_11_9 = true := by decide +kernel

theorem check_11_10 : checkAV 11 10 items_11_10 = true := by decide +kernel

/-- The check of the order 11. -/
theorem order_11 : checkOrderV 11 6 [items_11_6, items_11_7, items_11_8, items_11_9, items_11_10] = true := by
  simp only [checkOrderV, check_11_6, check_11_7, check_11_8, check_11_9, check_11_10, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_12_6 : checkAV 12 6 items_12_6 = true := by decide +kernel

theorem check_12_7 : checkAV 12 7 items_12_7 = true := by decide +kernel

theorem check_12_8 : checkAV 12 8 items_12_8 = true := by decide +kernel

theorem check_12_9 : checkAV 12 9 items_12_9 = true := by decide +kernel

theorem check_12_10 : checkAV 12 10 items_12_10 = true := by decide +kernel

theorem check_12_11 : checkAV 12 11 items_12_11 = true := by decide +kernel

/-- The check of the order 12. -/
theorem order_12 : checkOrderV 12 6 [items_12_6, items_12_7, items_12_8, items_12_9, items_12_10, items_12_11] = true := by
  simp only [checkOrderV, check_12_6, check_12_7, check_12_8, check_12_9, check_12_10, check_12_11, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_13_7 : checkAV 13 7 items_13_7 = true := by decide +kernel

theorem check_13_8 : checkAV 13 8 items_13_8 = true := by decide +kernel

theorem check_13_9 : checkAV 13 9 items_13_9 = true := by decide +kernel

theorem check_13_10 : checkAV 13 10 items_13_10 = true := by decide +kernel

theorem check_13_11 : checkAV 13 11 items_13_11 = true := by decide +kernel

theorem check_13_12 : checkAV 13 12 items_13_12 = true := by decide +kernel

/-- The check of the order 13. -/
theorem order_13 : checkOrderV 13 7 [items_13_7, items_13_8, items_13_9, items_13_10, items_13_11, items_13_12] = true := by
  simp only [checkOrderV, check_13_7, check_13_8, check_13_9, check_13_10, check_13_11, check_13_12, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_14_7 : checkAV 14 7 items_14_7 = true := by decide +kernel

theorem check_14_8 : checkAV 14 8 items_14_8 = true := by decide +kernel

theorem check_14_9 : checkAV 14 9 items_14_9 = true := by decide +kernel

theorem check_14_10 : checkAV 14 10 items_14_10 = true := by decide +kernel

theorem check_14_11 : checkAV 14 11 items_14_11 = true := by decide +kernel

theorem check_14_12 : checkAV 14 12 items_14_12 = true := by decide +kernel

theorem check_14_13 : checkAV 14 13 items_14_13 = true := by decide +kernel

/-- The check of the order 14. -/
theorem order_14 : checkOrderV 14 7 [items_14_7, items_14_8, items_14_9, items_14_10, items_14_11, items_14_12, items_14_13] = true := by
  simp only [checkOrderV, check_14_7, check_14_8, check_14_9, check_14_10, check_14_11, check_14_12, check_14_13, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_15_8 : checkAV 15 8 items_15_8 = true := by decide +kernel

theorem check_15_9 : checkAV 15 9 items_15_9 = true := by decide +kernel

theorem check_15_10 : checkAV 15 10 items_15_10 = true := by decide +kernel

theorem check_15_11 : checkAV 15 11 items_15_11 = true := by decide +kernel

theorem check_15_12 : checkAV 15 12 items_15_12 = true := by decide +kernel

theorem check_15_13 : checkAV 15 13 items_15_13 = true := by decide +kernel

theorem check_15_14 : checkAV 15 14 items_15_14 = true := by decide +kernel

/-- The check of the order 15. -/
theorem order_15 : checkOrderV 15 8 [items_15_8, items_15_9, items_15_10, items_15_11, items_15_12, items_15_13, items_15_14] = true := by
  simp only [checkOrderV, check_15_8, check_15_9, check_15_10, check_15_11, check_15_12, check_15_13, check_15_14, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_16_8 : checkAV 16 8 items_16_8 = true := by decide +kernel

theorem check_16_9 : checkAV 16 9 items_16_9 = true := by decide +kernel

theorem check_16_10 : checkAV 16 10 items_16_10 = true := by decide +kernel

theorem check_16_11 : checkAV 16 11 items_16_11 = true := by decide +kernel

theorem check_16_12 : checkAV 16 12 items_16_12 = true := by decide +kernel

theorem check_16_13 : checkAV 16 13 items_16_13 = true := by decide +kernel

theorem check_16_14 : checkAV 16 14 items_16_14 = true := by decide +kernel

theorem check_16_15 : checkAV 16 15 items_16_15 = true := by decide +kernel

/-- The check of the order 16. -/
theorem order_16 : checkOrderV 16 8 [items_16_8, items_16_9, items_16_10, items_16_11, items_16_12, items_16_13, items_16_14, items_16_15] = true := by
  simp only [checkOrderV, check_16_8, check_16_9, check_16_10, check_16_11, check_16_12, check_16_13, check_16_14, check_16_15, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_17_9 : checkAV 17 9 items_17_9 = true := by decide +kernel

theorem check_17_10 : checkAV 17 10 items_17_10 = true := by decide +kernel

theorem check_17_11 : checkAV 17 11 items_17_11 = true := by decide +kernel

theorem check_17_12 : checkAV 17 12 items_17_12 = true := by decide +kernel

theorem check_17_13 : checkAV 17 13 items_17_13 = true := by decide +kernel

theorem check_17_14 : checkAV 17 14 items_17_14 = true := by decide +kernel

theorem check_17_15 : checkAV 17 15 items_17_15 = true := by decide +kernel

theorem check_17_16 : checkAV 17 16 items_17_16 = true := by decide +kernel

/-- The check of the order 17. -/
theorem order_17 : checkOrderV 17 9 [items_17_9, items_17_10, items_17_11, items_17_12, items_17_13, items_17_14, items_17_15, items_17_16] = true := by
  simp only [checkOrderV, check_17_9, check_17_10, check_17_11, check_17_12, check_17_13, check_17_14, check_17_15, check_17_16, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_18_9 : checkAV 18 9 items_18_9 = true := by decide +kernel

theorem check_18_10 : checkAV 18 10 items_18_10 = true := by decide +kernel

theorem check_18_11 : checkAV 18 11 items_18_11 = true := by decide +kernel

theorem check_18_12 : checkAV 18 12 items_18_12 = true := by decide +kernel

theorem check_18_13 : checkAV 18 13 items_18_13 = true := by decide +kernel

theorem check_18_14 : checkAV 18 14 items_18_14 = true := by decide +kernel

theorem check_18_15 : checkAV 18 15 items_18_15 = true := by decide +kernel

theorem check_18_16 : checkAV 18 16 items_18_16 = true := by decide +kernel

theorem check_18_17 : checkAV 18 17 items_18_17 = true := by decide +kernel

/-- The check of the order 18. -/
theorem order_18 : checkOrderV 18 9 [items_18_9, items_18_10, items_18_11, items_18_12, items_18_13, items_18_14, items_18_15, items_18_16, items_18_17] = true := by
  simp only [checkOrderV, check_18_9, check_18_10, check_18_11, check_18_12, check_18_13, check_18_14, check_18_15, check_18_16, check_18_17, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_19_10 : checkAV 19 10 items_19_10 = true := by decide +kernel

theorem check_19_11 : checkAV 19 11 items_19_11 = true := by decide +kernel

theorem check_19_12 : checkAV 19 12 items_19_12 = true := by decide +kernel

theorem check_19_13 : checkAV 19 13 items_19_13 = true := by decide +kernel

theorem check_19_14 : checkAV 19 14 items_19_14 = true := by decide +kernel

theorem check_19_15 : checkAV 19 15 items_19_15 = true := by decide +kernel

theorem check_19_16 : checkAV 19 16 items_19_16 = true := by decide +kernel

theorem check_19_17 : checkAV 19 17 items_19_17 = true := by decide +kernel

theorem check_19_18 : checkAV 19 18 items_19_18 = true := by decide +kernel

/-- The check of the order 19. -/
theorem order_19 : checkOrderV 19 10 [items_19_10, items_19_11, items_19_12, items_19_13, items_19_14, items_19_15, items_19_16, items_19_17, items_19_18] = true := by
  simp only [checkOrderV, check_19_10, check_19_11, check_19_12, check_19_13, check_19_14, check_19_15, check_19_16, check_19_17, check_19_18, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

theorem check_20_10 : checkAV 20 10 items_20_10 = true := by decide +kernel

theorem check_20_11 : checkAV 20 11 items_20_11 = true := by decide +kernel

theorem check_20_12 : checkAV 20 12 items_20_12 = true := by decide +kernel

theorem check_20_13 : checkAV 20 13 items_20_13 = true := by decide +kernel

theorem check_20_14 : checkAV 20 14 items_20_14 = true := by decide +kernel

theorem check_20_15 : checkAV 20 15 items_20_15 = true := by decide +kernel

theorem check_20_16 : checkAV 20 16 items_20_16 = true := by decide +kernel

theorem check_20_17 : checkAV 20 17 items_20_17 = true := by decide +kernel

theorem check_20_18 : checkAV 20 18 items_20_18 = true := by decide +kernel

theorem check_20_19 : checkAV 20 19 items_20_19 = true := by decide +kernel

/-- The check of the order 20. -/
theorem order_20 : checkOrderV 20 10 [items_20_10, items_20_11, items_20_12, items_20_13, items_20_14, items_20_15, items_20_16, items_20_17, items_20_18, items_20_19] = true := by
  simp only [checkOrderV, check_20_10, check_20_11, check_20_12, check_20_13, check_20_14, check_20_15, check_20_16, check_20_17, check_20_18, check_20_19, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
