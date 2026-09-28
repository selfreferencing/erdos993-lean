import Erdos993Lean.ZhangKernel.Data.O56

/-!
# Kernel-checked finite part: the checks of the orders 56

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

theorem check_56_28 : checkAV 56 28 items_56_28 = true := by decide +kernel

theorem check_56_29 : checkAV 56 29 items_56_29 = true := by decide +kernel

theorem check_56_30 : checkAV 56 30 items_56_30 = true := by decide +kernel

theorem check_56_31 : checkAV 56 31 items_56_31 = true := by decide +kernel

theorem check_56_32 : checkAV 56 32 items_56_32 = true := by decide +kernel

theorem check_56_33 : checkAV 56 33 items_56_33 = true := by decide +kernel

theorem check_56_34 : checkAV 56 34 items_56_34 = true := by decide +kernel

theorem check_56_35 : checkAV 56 35 items_56_35 = true := by decide +kernel

theorem check_56_36 : checkAV 56 36 items_56_36 = true := by decide +kernel

theorem check_56_37 : checkAV 56 37 items_56_37 = true := by decide +kernel

theorem check_56_38 : checkAV 56 38 items_56_38 = true := by decide +kernel

theorem check_56_39 : checkAV 56 39 items_56_39 = true := by decide +kernel

theorem check_56_40 : checkAV 56 40 items_56_40 = true := by decide +kernel

theorem check_56_41 : checkAV 56 41 items_56_41 = true := by decide +kernel

theorem check_56_42 : checkAV 56 42 items_56_42 = true := by decide +kernel

theorem check_56_43 : checkAV 56 43 items_56_43 = true := by decide +kernel

theorem check_56_44 : checkAV 56 44 items_56_44 = true := by decide +kernel

theorem check_56_45 : checkAV 56 45 items_56_45 = true := by decide +kernel

theorem check_56_46 : checkAV 56 46 items_56_46 = true := by decide +kernel

theorem check_56_47 : checkAV 56 47 items_56_47 = true := by decide +kernel

theorem check_56_48 : checkAV 56 48 items_56_48 = true := by decide +kernel

theorem check_56_49 : checkAV 56 49 items_56_49 = true := by decide +kernel

theorem check_56_50 : checkAV 56 50 items_56_50 = true := by decide +kernel

theorem check_56_51 : checkAV 56 51 items_56_51 = true := by decide +kernel

theorem check_56_52 : checkAV 56 52 items_56_52 = true := by decide +kernel

theorem check_56_53 : checkAV 56 53 items_56_53 = true := by decide +kernel

theorem check_56_54 : checkAV 56 54 items_56_54 = true := by decide +kernel

theorem check_56_55 : checkAV 56 55 items_56_55 = true := by decide +kernel

/-- The check of the order 56. -/
theorem order_56 : checkOrderV 56 28 [items_56_28, items_56_29, items_56_30, items_56_31, items_56_32, items_56_33, items_56_34, items_56_35, items_56_36, items_56_37, items_56_38, items_56_39, items_56_40, items_56_41, items_56_42, items_56_43, items_56_44, items_56_45, items_56_46, items_56_47, items_56_48, items_56_49, items_56_50, items_56_51, items_56_52, items_56_53, items_56_54, items_56_55] = true := by
  simp only [checkOrderV, check_56_28, check_56_29, check_56_30, check_56_31, check_56_32, check_56_33, check_56_34, check_56_35, check_56_36, check_56_37, check_56_38, check_56_39, check_56_40, check_56_41, check_56_42, check_56_43, check_56_44, check_56_45, check_56_46, check_56_47, check_56_48, check_56_49, check_56_50, check_56_51, check_56_52, check_56_53, check_56_54, check_56_55, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
