import Erdos993Lean.ZhangKernel.Data.O59

/-!
# Kernel-checked finite part: the checks of the orders 59

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

theorem check_59_30 : checkAV 59 30 items_59_30 = true := by decide +kernel

theorem check_59_31 : checkAV 59 31 items_59_31 = true := by decide +kernel

theorem check_59_32 : checkAV 59 32 items_59_32 = true := by decide +kernel

theorem check_59_33 : checkAV 59 33 items_59_33 = true := by decide +kernel

theorem check_59_34 : checkAV 59 34 items_59_34 = true := by decide +kernel

theorem check_59_35 : checkAV 59 35 items_59_35 = true := by decide +kernel

theorem check_59_36 : checkAV 59 36 items_59_36 = true := by decide +kernel

theorem check_59_37 : checkAV 59 37 items_59_37 = true := by decide +kernel

theorem check_59_38 : checkAV 59 38 items_59_38 = true := by decide +kernel

theorem check_59_39 : checkAV 59 39 items_59_39 = true := by decide +kernel

theorem check_59_40 : checkAV 59 40 items_59_40 = true := by decide +kernel

theorem check_59_41 : checkAV 59 41 items_59_41 = true := by decide +kernel

theorem check_59_42 : checkAV 59 42 items_59_42 = true := by decide +kernel

theorem check_59_43 : checkAV 59 43 items_59_43 = true := by decide +kernel

theorem check_59_44 : checkAV 59 44 items_59_44 = true := by decide +kernel

theorem check_59_45 : checkAV 59 45 items_59_45 = true := by decide +kernel

theorem check_59_46 : checkAV 59 46 items_59_46 = true := by decide +kernel

theorem check_59_47 : checkAV 59 47 items_59_47 = true := by decide +kernel

theorem check_59_48 : checkAV 59 48 items_59_48 = true := by decide +kernel

theorem check_59_49 : checkAV 59 49 items_59_49 = true := by decide +kernel

theorem check_59_50 : checkAV 59 50 items_59_50 = true := by decide +kernel

theorem check_59_51 : checkAV 59 51 items_59_51 = true := by decide +kernel

theorem check_59_52 : checkAV 59 52 items_59_52 = true := by decide +kernel

theorem check_59_53 : checkAV 59 53 items_59_53 = true := by decide +kernel

theorem check_59_54 : checkAV 59 54 items_59_54 = true := by decide +kernel

theorem check_59_55 : checkAV 59 55 items_59_55 = true := by decide +kernel

theorem check_59_56 : checkAV 59 56 items_59_56 = true := by decide +kernel

theorem check_59_57 : checkAV 59 57 items_59_57 = true := by decide +kernel

theorem check_59_58 : checkAV 59 58 items_59_58 = true := by decide +kernel

/-- The check of the order 59. -/
theorem order_59 : checkOrderV 59 30 [items_59_30, items_59_31, items_59_32, items_59_33, items_59_34, items_59_35, items_59_36, items_59_37, items_59_38, items_59_39, items_59_40, items_59_41, items_59_42, items_59_43, items_59_44, items_59_45, items_59_46, items_59_47, items_59_48, items_59_49, items_59_50, items_59_51, items_59_52, items_59_53, items_59_54, items_59_55, items_59_56, items_59_57, items_59_58] = true := by
  simp only [checkOrderV, check_59_30, check_59_31, check_59_32, check_59_33, check_59_34, check_59_35, check_59_36, check_59_37, check_59_38, check_59_39, check_59_40, check_59_41, check_59_42, check_59_43, check_59_44, check_59_45, check_59_46, check_59_47, check_59_48, check_59_49, check_59_50, check_59_51, check_59_52, check_59_53, check_59_54, check_59_55, check_59_56, check_59_57, check_59_58, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
