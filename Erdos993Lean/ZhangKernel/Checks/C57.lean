import Erdos993Lean.ZhangKernel.Data.O57

/-!
# Kernel-checked finite part: the checks of the orders 57

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

theorem check_57_29 : checkAV 57 29 items_57_29 = true := by decide +kernel

theorem check_57_30 : checkAV 57 30 items_57_30 = true := by decide +kernel

theorem check_57_31 : checkAV 57 31 items_57_31 = true := by decide +kernel

theorem check_57_32 : checkAV 57 32 items_57_32 = true := by decide +kernel

theorem check_57_33 : checkAV 57 33 items_57_33 = true := by decide +kernel

theorem check_57_34 : checkAV 57 34 items_57_34 = true := by decide +kernel

theorem check_57_35 : checkAV 57 35 items_57_35 = true := by decide +kernel

theorem check_57_36 : checkAV 57 36 items_57_36 = true := by decide +kernel

theorem check_57_37 : checkAV 57 37 items_57_37 = true := by decide +kernel

theorem check_57_38 : checkAV 57 38 items_57_38 = true := by decide +kernel

theorem check_57_39 : checkAV 57 39 items_57_39 = true := by decide +kernel

theorem check_57_40 : checkAV 57 40 items_57_40 = true := by decide +kernel

theorem check_57_41 : checkAV 57 41 items_57_41 = true := by decide +kernel

theorem check_57_42 : checkAV 57 42 items_57_42 = true := by decide +kernel

theorem check_57_43 : checkAV 57 43 items_57_43 = true := by decide +kernel

theorem check_57_44 : checkAV 57 44 items_57_44 = true := by decide +kernel

theorem check_57_45 : checkAV 57 45 items_57_45 = true := by decide +kernel

theorem check_57_46 : checkAV 57 46 items_57_46 = true := by decide +kernel

theorem check_57_47 : checkAV 57 47 items_57_47 = true := by decide +kernel

theorem check_57_48 : checkAV 57 48 items_57_48 = true := by decide +kernel

theorem check_57_49 : checkAV 57 49 items_57_49 = true := by decide +kernel

theorem check_57_50 : checkAV 57 50 items_57_50 = true := by decide +kernel

theorem check_57_51 : checkAV 57 51 items_57_51 = true := by decide +kernel

theorem check_57_52 : checkAV 57 52 items_57_52 = true := by decide +kernel

theorem check_57_53 : checkAV 57 53 items_57_53 = true := by decide +kernel

theorem check_57_54 : checkAV 57 54 items_57_54 = true := by decide +kernel

theorem check_57_55 : checkAV 57 55 items_57_55 = true := by decide +kernel

theorem check_57_56 : checkAV 57 56 items_57_56 = true := by decide +kernel

/-- The check of the order 57. -/
theorem order_57 : checkOrderV 57 29 [items_57_29, items_57_30, items_57_31, items_57_32, items_57_33, items_57_34, items_57_35, items_57_36, items_57_37, items_57_38, items_57_39, items_57_40, items_57_41, items_57_42, items_57_43, items_57_44, items_57_45, items_57_46, items_57_47, items_57_48, items_57_49, items_57_50, items_57_51, items_57_52, items_57_53, items_57_54, items_57_55, items_57_56] = true := by
  simp only [checkOrderV, check_57_29, check_57_30, check_57_31, check_57_32, check_57_33, check_57_34, check_57_35, check_57_36, check_57_37, check_57_38, check_57_39, check_57_40, check_57_41, check_57_42, check_57_43, check_57_44, check_57_45, check_57_46, check_57_47, check_57_48, check_57_49, check_57_50, check_57_51, check_57_52, check_57_53, check_57_54, check_57_55, check_57_56, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
