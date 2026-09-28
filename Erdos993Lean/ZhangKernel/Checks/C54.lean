import Erdos993Lean.ZhangKernel.Data.O54

/-!
# Kernel-checked finite part: the checks of the orders 54

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

theorem check_54_27 : checkAV 54 27 items_54_27 = true := by decide +kernel

theorem check_54_28 : checkAV 54 28 items_54_28 = true := by decide +kernel

theorem check_54_29 : checkAV 54 29 items_54_29 = true := by decide +kernel

theorem check_54_30 : checkAV 54 30 items_54_30 = true := by decide +kernel

theorem check_54_31 : checkAV 54 31 items_54_31 = true := by decide +kernel

theorem check_54_32 : checkAV 54 32 items_54_32 = true := by decide +kernel

theorem check_54_33 : checkAV 54 33 items_54_33 = true := by decide +kernel

theorem check_54_34 : checkAV 54 34 items_54_34 = true := by decide +kernel

theorem check_54_35 : checkAV 54 35 items_54_35 = true := by decide +kernel

theorem check_54_36 : checkAV 54 36 items_54_36 = true := by decide +kernel

theorem check_54_37 : checkAV 54 37 items_54_37 = true := by decide +kernel

theorem check_54_38 : checkAV 54 38 items_54_38 = true := by decide +kernel

theorem check_54_39 : checkAV 54 39 items_54_39 = true := by decide +kernel

theorem check_54_40 : checkAV 54 40 items_54_40 = true := by decide +kernel

theorem check_54_41 : checkAV 54 41 items_54_41 = true := by decide +kernel

theorem check_54_42 : checkAV 54 42 items_54_42 = true := by decide +kernel

theorem check_54_43 : checkAV 54 43 items_54_43 = true := by decide +kernel

theorem check_54_44 : checkAV 54 44 items_54_44 = true := by decide +kernel

theorem check_54_45 : checkAV 54 45 items_54_45 = true := by decide +kernel

theorem check_54_46 : checkAV 54 46 items_54_46 = true := by decide +kernel

theorem check_54_47 : checkAV 54 47 items_54_47 = true := by decide +kernel

theorem check_54_48 : checkAV 54 48 items_54_48 = true := by decide +kernel

theorem check_54_49 : checkAV 54 49 items_54_49 = true := by decide +kernel

theorem check_54_50 : checkAV 54 50 items_54_50 = true := by decide +kernel

theorem check_54_51 : checkAV 54 51 items_54_51 = true := by decide +kernel

theorem check_54_52 : checkAV 54 52 items_54_52 = true := by decide +kernel

theorem check_54_53 : checkAV 54 53 items_54_53 = true := by decide +kernel

/-- The check of the order 54. -/
theorem order_54 : checkOrderV 54 27 [items_54_27, items_54_28, items_54_29, items_54_30, items_54_31, items_54_32, items_54_33, items_54_34, items_54_35, items_54_36, items_54_37, items_54_38, items_54_39, items_54_40, items_54_41, items_54_42, items_54_43, items_54_44, items_54_45, items_54_46, items_54_47, items_54_48, items_54_49, items_54_50, items_54_51, items_54_52, items_54_53] = true := by
  simp only [checkOrderV, check_54_27, check_54_28, check_54_29, check_54_30, check_54_31, check_54_32, check_54_33, check_54_34, check_54_35, check_54_36, check_54_37, check_54_38, check_54_39, check_54_40, check_54_41, check_54_42, check_54_43, check_54_44, check_54_45, check_54_46, check_54_47, check_54_48, check_54_49, check_54_50, check_54_51, check_54_52, check_54_53, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
