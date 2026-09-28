import Erdos993Lean.ZhangKernel.Data.O55

/-!
# Kernel-checked finite part: the checks of the orders 55

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

theorem check_55_28 : checkAV 55 28 items_55_28 = true := by decide +kernel

theorem check_55_29 : checkAV 55 29 items_55_29 = true := by decide +kernel

theorem check_55_30 : checkAV 55 30 items_55_30 = true := by decide +kernel

theorem check_55_31 : checkAV 55 31 items_55_31 = true := by decide +kernel

theorem check_55_32 : checkAV 55 32 items_55_32 = true := by decide +kernel

theorem check_55_33 : checkAV 55 33 items_55_33 = true := by decide +kernel

theorem check_55_34 : checkAV 55 34 items_55_34 = true := by decide +kernel

theorem check_55_35 : checkAV 55 35 items_55_35 = true := by decide +kernel

theorem check_55_36 : checkAV 55 36 items_55_36 = true := by decide +kernel

theorem check_55_37 : checkAV 55 37 items_55_37 = true := by decide +kernel

theorem check_55_38 : checkAV 55 38 items_55_38 = true := by decide +kernel

theorem check_55_39 : checkAV 55 39 items_55_39 = true := by decide +kernel

theorem check_55_40 : checkAV 55 40 items_55_40 = true := by decide +kernel

theorem check_55_41 : checkAV 55 41 items_55_41 = true := by decide +kernel

theorem check_55_42 : checkAV 55 42 items_55_42 = true := by decide +kernel

theorem check_55_43 : checkAV 55 43 items_55_43 = true := by decide +kernel

theorem check_55_44 : checkAV 55 44 items_55_44 = true := by decide +kernel

theorem check_55_45 : checkAV 55 45 items_55_45 = true := by decide +kernel

theorem check_55_46 : checkAV 55 46 items_55_46 = true := by decide +kernel

theorem check_55_47 : checkAV 55 47 items_55_47 = true := by decide +kernel

theorem check_55_48 : checkAV 55 48 items_55_48 = true := by decide +kernel

theorem check_55_49 : checkAV 55 49 items_55_49 = true := by decide +kernel

theorem check_55_50 : checkAV 55 50 items_55_50 = true := by decide +kernel

theorem check_55_51 : checkAV 55 51 items_55_51 = true := by decide +kernel

theorem check_55_52 : checkAV 55 52 items_55_52 = true := by decide +kernel

theorem check_55_53 : checkAV 55 53 items_55_53 = true := by decide +kernel

theorem check_55_54 : checkAV 55 54 items_55_54 = true := by decide +kernel

/-- The check of the order 55. -/
theorem order_55 : checkOrderV 55 28 [items_55_28, items_55_29, items_55_30, items_55_31, items_55_32, items_55_33, items_55_34, items_55_35, items_55_36, items_55_37, items_55_38, items_55_39, items_55_40, items_55_41, items_55_42, items_55_43, items_55_44, items_55_45, items_55_46, items_55_47, items_55_48, items_55_49, items_55_50, items_55_51, items_55_52, items_55_53, items_55_54] = true := by
  simp only [checkOrderV, check_55_28, check_55_29, check_55_30, check_55_31, check_55_32, check_55_33, check_55_34, check_55_35, check_55_36, check_55_37, check_55_38, check_55_39, check_55_40, check_55_41, check_55_42, check_55_43, check_55_44, check_55_45, check_55_46, check_55_47, check_55_48, check_55_49, check_55_50, check_55_51, check_55_52, check_55_53, check_55_54, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
