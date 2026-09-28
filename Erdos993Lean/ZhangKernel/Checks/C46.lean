import Erdos993Lean.ZhangKernel.Data.O46

/-!
# Kernel-checked finite part: the checks of the orders 46

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

theorem check_46_23 : checkAV 46 23 items_46_23 = true := by decide +kernel

theorem check_46_24 : checkAV 46 24 items_46_24 = true := by decide +kernel

theorem check_46_25 : checkAV 46 25 items_46_25 = true := by decide +kernel

theorem check_46_26 : checkAV 46 26 items_46_26 = true := by decide +kernel

theorem check_46_27 : checkAV 46 27 items_46_27 = true := by decide +kernel

theorem check_46_28 : checkAV 46 28 items_46_28 = true := by decide +kernel

theorem check_46_29 : checkAV 46 29 items_46_29 = true := by decide +kernel

theorem check_46_30 : checkAV 46 30 items_46_30 = true := by decide +kernel

theorem check_46_31 : checkAV 46 31 items_46_31 = true := by decide +kernel

theorem check_46_32 : checkAV 46 32 items_46_32 = true := by decide +kernel

theorem check_46_33 : checkAV 46 33 items_46_33 = true := by decide +kernel

theorem check_46_34 : checkAV 46 34 items_46_34 = true := by decide +kernel

theorem check_46_35 : checkAV 46 35 items_46_35 = true := by decide +kernel

theorem check_46_36 : checkAV 46 36 items_46_36 = true := by decide +kernel

theorem check_46_37 : checkAV 46 37 items_46_37 = true := by decide +kernel

theorem check_46_38 : checkAV 46 38 items_46_38 = true := by decide +kernel

theorem check_46_39 : checkAV 46 39 items_46_39 = true := by decide +kernel

theorem check_46_40 : checkAV 46 40 items_46_40 = true := by decide +kernel

theorem check_46_41 : checkAV 46 41 items_46_41 = true := by decide +kernel

theorem check_46_42 : checkAV 46 42 items_46_42 = true := by decide +kernel

theorem check_46_43 : checkAV 46 43 items_46_43 = true := by decide +kernel

theorem check_46_44 : checkAV 46 44 items_46_44 = true := by decide +kernel

theorem check_46_45 : checkAV 46 45 items_46_45 = true := by decide +kernel

/-- The check of the order 46. -/
theorem order_46 : checkOrderV 46 23 [items_46_23, items_46_24, items_46_25, items_46_26, items_46_27, items_46_28, items_46_29, items_46_30, items_46_31, items_46_32, items_46_33, items_46_34, items_46_35, items_46_36, items_46_37, items_46_38, items_46_39, items_46_40, items_46_41, items_46_42, items_46_43, items_46_44, items_46_45] = true := by
  simp only [checkOrderV, check_46_23, check_46_24, check_46_25, check_46_26, check_46_27, check_46_28, check_46_29, check_46_30, check_46_31, check_46_32, check_46_33, check_46_34, check_46_35, check_46_36, check_46_37, check_46_38, check_46_39, check_46_40, check_46_41, check_46_42, check_46_43, check_46_44, check_46_45, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
