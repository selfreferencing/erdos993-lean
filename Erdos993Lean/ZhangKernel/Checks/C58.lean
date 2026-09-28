import Erdos993Lean.ZhangKernel.Data.O58

/-!
# Kernel-checked finite part: the checks of the orders 58

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

theorem check_58_29 : checkAV 58 29 items_58_29 = true := by decide +kernel

theorem check_58_30 : checkAV 58 30 items_58_30 = true := by decide +kernel

theorem check_58_31 : checkAV 58 31 items_58_31 = true := by decide +kernel

theorem check_58_32 : checkAV 58 32 items_58_32 = true := by decide +kernel

theorem check_58_33 : checkAV 58 33 items_58_33 = true := by decide +kernel

theorem check_58_34 : checkAV 58 34 items_58_34 = true := by decide +kernel

theorem check_58_35 : checkAV 58 35 items_58_35 = true := by decide +kernel

theorem check_58_36 : checkAV 58 36 items_58_36 = true := by decide +kernel

theorem check_58_37 : checkAV 58 37 items_58_37 = true := by decide +kernel

theorem check_58_38 : checkAV 58 38 items_58_38 = true := by decide +kernel

theorem check_58_39 : checkAV 58 39 items_58_39 = true := by decide +kernel

theorem check_58_40 : checkAV 58 40 items_58_40 = true := by decide +kernel

theorem check_58_41 : checkAV 58 41 items_58_41 = true := by decide +kernel

theorem check_58_42 : checkAV 58 42 items_58_42 = true := by decide +kernel

theorem check_58_43 : checkAV 58 43 items_58_43 = true := by decide +kernel

theorem check_58_44 : checkAV 58 44 items_58_44 = true := by decide +kernel

theorem check_58_45 : checkAV 58 45 items_58_45 = true := by decide +kernel

theorem check_58_46 : checkAV 58 46 items_58_46 = true := by decide +kernel

theorem check_58_47 : checkAV 58 47 items_58_47 = true := by decide +kernel

theorem check_58_48 : checkAV 58 48 items_58_48 = true := by decide +kernel

theorem check_58_49 : checkAV 58 49 items_58_49 = true := by decide +kernel

theorem check_58_50 : checkAV 58 50 items_58_50 = true := by decide +kernel

theorem check_58_51 : checkAV 58 51 items_58_51 = true := by decide +kernel

theorem check_58_52 : checkAV 58 52 items_58_52 = true := by decide +kernel

theorem check_58_53 : checkAV 58 53 items_58_53 = true := by decide +kernel

theorem check_58_54 : checkAV 58 54 items_58_54 = true := by decide +kernel

theorem check_58_55 : checkAV 58 55 items_58_55 = true := by decide +kernel

theorem check_58_56 : checkAV 58 56 items_58_56 = true := by decide +kernel

theorem check_58_57 : checkAV 58 57 items_58_57 = true := by decide +kernel

/-- The check of the order 58. -/
theorem order_58 : checkOrderV 58 29 [items_58_29, items_58_30, items_58_31, items_58_32, items_58_33, items_58_34, items_58_35, items_58_36, items_58_37, items_58_38, items_58_39, items_58_40, items_58_41, items_58_42, items_58_43, items_58_44, items_58_45, items_58_46, items_58_47, items_58_48, items_58_49, items_58_50, items_58_51, items_58_52, items_58_53, items_58_54, items_58_55, items_58_56, items_58_57] = true := by
  simp only [checkOrderV, check_58_29, check_58_30, check_58_31, check_58_32, check_58_33, check_58_34, check_58_35, check_58_36, check_58_37, check_58_38, check_58_39, check_58_40, check_58_41, check_58_42, check_58_43, check_58_44, check_58_45, check_58_46, check_58_47, check_58_48, check_58_49, check_58_50, check_58_51, check_58_52, check_58_53, check_58_54, check_58_55, check_58_56, check_58_57, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
