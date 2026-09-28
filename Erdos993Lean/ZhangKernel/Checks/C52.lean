import Erdos993Lean.ZhangKernel.Data.O52

/-!
# Kernel-checked finite part: the checks of the orders 52

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

theorem check_52_26 : checkAV 52 26 items_52_26 = true := by decide +kernel

theorem check_52_27 : checkAV 52 27 items_52_27 = true := by decide +kernel

theorem check_52_28 : checkAV 52 28 items_52_28 = true := by decide +kernel

theorem check_52_29 : checkAV 52 29 items_52_29 = true := by decide +kernel

theorem check_52_30 : checkAV 52 30 items_52_30 = true := by decide +kernel

theorem check_52_31 : checkAV 52 31 items_52_31 = true := by decide +kernel

theorem check_52_32 : checkAV 52 32 items_52_32 = true := by decide +kernel

theorem check_52_33 : checkAV 52 33 items_52_33 = true := by decide +kernel

theorem check_52_34 : checkAV 52 34 items_52_34 = true := by decide +kernel

theorem check_52_35 : checkAV 52 35 items_52_35 = true := by decide +kernel

theorem check_52_36 : checkAV 52 36 items_52_36 = true := by decide +kernel

theorem check_52_37 : checkAV 52 37 items_52_37 = true := by decide +kernel

theorem check_52_38 : checkAV 52 38 items_52_38 = true := by decide +kernel

theorem check_52_39 : checkAV 52 39 items_52_39 = true := by decide +kernel

theorem check_52_40 : checkAV 52 40 items_52_40 = true := by decide +kernel

theorem check_52_41 : checkAV 52 41 items_52_41 = true := by decide +kernel

theorem check_52_42 : checkAV 52 42 items_52_42 = true := by decide +kernel

theorem check_52_43 : checkAV 52 43 items_52_43 = true := by decide +kernel

theorem check_52_44 : checkAV 52 44 items_52_44 = true := by decide +kernel

theorem check_52_45 : checkAV 52 45 items_52_45 = true := by decide +kernel

theorem check_52_46 : checkAV 52 46 items_52_46 = true := by decide +kernel

theorem check_52_47 : checkAV 52 47 items_52_47 = true := by decide +kernel

theorem check_52_48 : checkAV 52 48 items_52_48 = true := by decide +kernel

theorem check_52_49 : checkAV 52 49 items_52_49 = true := by decide +kernel

theorem check_52_50 : checkAV 52 50 items_52_50 = true := by decide +kernel

theorem check_52_51 : checkAV 52 51 items_52_51 = true := by decide +kernel

/-- The check of the order 52. -/
theorem order_52 : checkOrderV 52 26 [items_52_26, items_52_27, items_52_28, items_52_29, items_52_30, items_52_31, items_52_32, items_52_33, items_52_34, items_52_35, items_52_36, items_52_37, items_52_38, items_52_39, items_52_40, items_52_41, items_52_42, items_52_43, items_52_44, items_52_45, items_52_46, items_52_47, items_52_48, items_52_49, items_52_50, items_52_51] = true := by
  simp only [checkOrderV, check_52_26, check_52_27, check_52_28, check_52_29, check_52_30, check_52_31, check_52_32, check_52_33, check_52_34, check_52_35, check_52_36, check_52_37, check_52_38, check_52_39, check_52_40, check_52_41, check_52_42, check_52_43, check_52_44, check_52_45, check_52_46, check_52_47, check_52_48, check_52_49, check_52_50, check_52_51, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
