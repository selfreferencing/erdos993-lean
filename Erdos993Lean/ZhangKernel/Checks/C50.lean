import Erdos993Lean.ZhangKernel.Data.O50

/-!
# Kernel-checked finite part: the checks of the orders 50

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

theorem check_50_25 : checkAV 50 25 items_50_25 = true := by decide +kernel

theorem check_50_26 : checkAV 50 26 items_50_26 = true := by decide +kernel

theorem check_50_27 : checkAV 50 27 items_50_27 = true := by decide +kernel

theorem check_50_28 : checkAV 50 28 items_50_28 = true := by decide +kernel

theorem check_50_29 : checkAV 50 29 items_50_29 = true := by decide +kernel

theorem check_50_30 : checkAV 50 30 items_50_30 = true := by decide +kernel

theorem check_50_31 : checkAV 50 31 items_50_31 = true := by decide +kernel

theorem check_50_32 : checkAV 50 32 items_50_32 = true := by decide +kernel

theorem check_50_33 : checkAV 50 33 items_50_33 = true := by decide +kernel

theorem check_50_34 : checkAV 50 34 items_50_34 = true := by decide +kernel

theorem check_50_35 : checkAV 50 35 items_50_35 = true := by decide +kernel

theorem check_50_36 : checkAV 50 36 items_50_36 = true := by decide +kernel

theorem check_50_37 : checkAV 50 37 items_50_37 = true := by decide +kernel

theorem check_50_38 : checkAV 50 38 items_50_38 = true := by decide +kernel

theorem check_50_39 : checkAV 50 39 items_50_39 = true := by decide +kernel

theorem check_50_40 : checkAV 50 40 items_50_40 = true := by decide +kernel

theorem check_50_41 : checkAV 50 41 items_50_41 = true := by decide +kernel

theorem check_50_42 : checkAV 50 42 items_50_42 = true := by decide +kernel

theorem check_50_43 : checkAV 50 43 items_50_43 = true := by decide +kernel

theorem check_50_44 : checkAV 50 44 items_50_44 = true := by decide +kernel

theorem check_50_45 : checkAV 50 45 items_50_45 = true := by decide +kernel

theorem check_50_46 : checkAV 50 46 items_50_46 = true := by decide +kernel

theorem check_50_47 : checkAV 50 47 items_50_47 = true := by decide +kernel

theorem check_50_48 : checkAV 50 48 items_50_48 = true := by decide +kernel

theorem check_50_49 : checkAV 50 49 items_50_49 = true := by decide +kernel

/-- The check of the order 50. -/
theorem order_50 : checkOrderV 50 25 [items_50_25, items_50_26, items_50_27, items_50_28, items_50_29, items_50_30, items_50_31, items_50_32, items_50_33, items_50_34, items_50_35, items_50_36, items_50_37, items_50_38, items_50_39, items_50_40, items_50_41, items_50_42, items_50_43, items_50_44, items_50_45, items_50_46, items_50_47, items_50_48, items_50_49] = true := by
  simp only [checkOrderV, check_50_25, check_50_26, check_50_27, check_50_28, check_50_29, check_50_30, check_50_31, check_50_32, check_50_33, check_50_34, check_50_35, check_50_36, check_50_37, check_50_38, check_50_39, check_50_40, check_50_41, check_50_42, check_50_43, check_50_44, check_50_45, check_50_46, check_50_47, check_50_48, check_50_49, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
