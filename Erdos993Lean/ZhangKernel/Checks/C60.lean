import Erdos993Lean.ZhangKernel.Data.O60

/-!
# Kernel-checked finite part: the checks of the orders 60

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

theorem check_60_30 : checkAV 60 30 items_60_30 = true := by decide +kernel

theorem check_60_31 : checkAV 60 31 items_60_31 = true := by decide +kernel

theorem check_60_32 : checkAV 60 32 items_60_32 = true := by decide +kernel

theorem check_60_33 : checkAV 60 33 items_60_33 = true := by decide +kernel

theorem check_60_34 : checkAV 60 34 items_60_34 = true := by decide +kernel

theorem check_60_35 : checkAV 60 35 items_60_35 = true := by decide +kernel

theorem check_60_36 : checkAV 60 36 items_60_36 = true := by decide +kernel

theorem check_60_37 : checkAV 60 37 items_60_37 = true := by decide +kernel

theorem check_60_38 : checkAV 60 38 items_60_38 = true := by decide +kernel

theorem check_60_39 : checkAV 60 39 items_60_39 = true := by decide +kernel

theorem check_60_40 : checkAV 60 40 items_60_40 = true := by decide +kernel

theorem check_60_41 : checkAV 60 41 items_60_41 = true := by decide +kernel

theorem check_60_42 : checkAV 60 42 items_60_42 = true := by decide +kernel

theorem check_60_43 : checkAV 60 43 items_60_43 = true := by decide +kernel

theorem check_60_44 : checkAV 60 44 items_60_44 = true := by decide +kernel

theorem check_60_45 : checkAV 60 45 items_60_45 = true := by decide +kernel

theorem check_60_46 : checkAV 60 46 items_60_46 = true := by decide +kernel

theorem check_60_47 : checkAV 60 47 items_60_47 = true := by decide +kernel

theorem check_60_48 : checkAV 60 48 items_60_48 = true := by decide +kernel

theorem check_60_49 : checkAV 60 49 items_60_49 = true := by decide +kernel

theorem check_60_50 : checkAV 60 50 items_60_50 = true := by decide +kernel

theorem check_60_51 : checkAV 60 51 items_60_51 = true := by decide +kernel

theorem check_60_52 : checkAV 60 52 items_60_52 = true := by decide +kernel

theorem check_60_53 : checkAV 60 53 items_60_53 = true := by decide +kernel

theorem check_60_54 : checkAV 60 54 items_60_54 = true := by decide +kernel

theorem check_60_55 : checkAV 60 55 items_60_55 = true := by decide +kernel

theorem check_60_56 : checkAV 60 56 items_60_56 = true := by decide +kernel

theorem check_60_57 : checkAV 60 57 items_60_57 = true := by decide +kernel

theorem check_60_58 : checkAV 60 58 items_60_58 = true := by decide +kernel

theorem check_60_59 : checkAV 60 59 items_60_59 = true := by decide +kernel

/-- The check of the order 60. -/
theorem order_60 : checkOrderV 60 30 [items_60_30, items_60_31, items_60_32, items_60_33, items_60_34, items_60_35, items_60_36, items_60_37, items_60_38, items_60_39, items_60_40, items_60_41, items_60_42, items_60_43, items_60_44, items_60_45, items_60_46, items_60_47, items_60_48, items_60_49, items_60_50, items_60_51, items_60_52, items_60_53, items_60_54, items_60_55, items_60_56, items_60_57, items_60_58, items_60_59] = true := by
  simp only [checkOrderV, check_60_30, check_60_31, check_60_32, check_60_33, check_60_34, check_60_35, check_60_36, check_60_37, check_60_38, check_60_39, check_60_40, check_60_41, check_60_42, check_60_43, check_60_44, check_60_45, check_60_46, check_60_47, check_60_48, check_60_49, check_60_50, check_60_51, check_60_52, check_60_53, check_60_54, check_60_55, check_60_56, check_60_57, check_60_58, check_60_59, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
