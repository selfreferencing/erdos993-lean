import Erdos993Lean.ZhangKernel.Data.O51

/-!
# Kernel-checked finite part: the checks of the orders 51

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

theorem check_51_26 : checkAV 51 26 items_51_26 = true := by decide +kernel

theorem check_51_27 : checkAV 51 27 items_51_27 = true := by decide +kernel

theorem check_51_28 : checkAV 51 28 items_51_28 = true := by decide +kernel

theorem check_51_29 : checkAV 51 29 items_51_29 = true := by decide +kernel

theorem check_51_30 : checkAV 51 30 items_51_30 = true := by decide +kernel

theorem check_51_31 : checkAV 51 31 items_51_31 = true := by decide +kernel

theorem check_51_32 : checkAV 51 32 items_51_32 = true := by decide +kernel

theorem check_51_33 : checkAV 51 33 items_51_33 = true := by decide +kernel

theorem check_51_34 : checkAV 51 34 items_51_34 = true := by decide +kernel

theorem check_51_35 : checkAV 51 35 items_51_35 = true := by decide +kernel

theorem check_51_36 : checkAV 51 36 items_51_36 = true := by decide +kernel

theorem check_51_37 : checkAV 51 37 items_51_37 = true := by decide +kernel

theorem check_51_38 : checkAV 51 38 items_51_38 = true := by decide +kernel

theorem check_51_39 : checkAV 51 39 items_51_39 = true := by decide +kernel

theorem check_51_40 : checkAV 51 40 items_51_40 = true := by decide +kernel

theorem check_51_41 : checkAV 51 41 items_51_41 = true := by decide +kernel

theorem check_51_42 : checkAV 51 42 items_51_42 = true := by decide +kernel

theorem check_51_43 : checkAV 51 43 items_51_43 = true := by decide +kernel

theorem check_51_44 : checkAV 51 44 items_51_44 = true := by decide +kernel

theorem check_51_45 : checkAV 51 45 items_51_45 = true := by decide +kernel

theorem check_51_46 : checkAV 51 46 items_51_46 = true := by decide +kernel

theorem check_51_47 : checkAV 51 47 items_51_47 = true := by decide +kernel

theorem check_51_48 : checkAV 51 48 items_51_48 = true := by decide +kernel

theorem check_51_49 : checkAV 51 49 items_51_49 = true := by decide +kernel

theorem check_51_50 : checkAV 51 50 items_51_50 = true := by decide +kernel

/-- The check of the order 51. -/
theorem order_51 : checkOrderV 51 26 [items_51_26, items_51_27, items_51_28, items_51_29, items_51_30, items_51_31, items_51_32, items_51_33, items_51_34, items_51_35, items_51_36, items_51_37, items_51_38, items_51_39, items_51_40, items_51_41, items_51_42, items_51_43, items_51_44, items_51_45, items_51_46, items_51_47, items_51_48, items_51_49, items_51_50] = true := by
  simp only [checkOrderV, check_51_26, check_51_27, check_51_28, check_51_29, check_51_30, check_51_31, check_51_32, check_51_33, check_51_34, check_51_35, check_51_36, check_51_37, check_51_38, check_51_39, check_51_40, check_51_41, check_51_42, check_51_43, check_51_44, check_51_45, check_51_46, check_51_47, check_51_48, check_51_49, check_51_50, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
