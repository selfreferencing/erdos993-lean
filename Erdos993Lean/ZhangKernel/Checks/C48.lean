import Erdos993Lean.ZhangKernel.Data.O48

/-!
# Kernel-checked finite part: the checks of the orders 48

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

theorem check_48_24 : checkAV 48 24 items_48_24 = true := by decide +kernel

theorem check_48_25 : checkAV 48 25 items_48_25 = true := by decide +kernel

theorem check_48_26 : checkAV 48 26 items_48_26 = true := by decide +kernel

theorem check_48_27 : checkAV 48 27 items_48_27 = true := by decide +kernel

theorem check_48_28 : checkAV 48 28 items_48_28 = true := by decide +kernel

theorem check_48_29 : checkAV 48 29 items_48_29 = true := by decide +kernel

theorem check_48_30 : checkAV 48 30 items_48_30 = true := by decide +kernel

theorem check_48_31 : checkAV 48 31 items_48_31 = true := by decide +kernel

theorem check_48_32 : checkAV 48 32 items_48_32 = true := by decide +kernel

theorem check_48_33 : checkAV 48 33 items_48_33 = true := by decide +kernel

theorem check_48_34 : checkAV 48 34 items_48_34 = true := by decide +kernel

theorem check_48_35 : checkAV 48 35 items_48_35 = true := by decide +kernel

theorem check_48_36 : checkAV 48 36 items_48_36 = true := by decide +kernel

theorem check_48_37 : checkAV 48 37 items_48_37 = true := by decide +kernel

theorem check_48_38 : checkAV 48 38 items_48_38 = true := by decide +kernel

theorem check_48_39 : checkAV 48 39 items_48_39 = true := by decide +kernel

theorem check_48_40 : checkAV 48 40 items_48_40 = true := by decide +kernel

theorem check_48_41 : checkAV 48 41 items_48_41 = true := by decide +kernel

theorem check_48_42 : checkAV 48 42 items_48_42 = true := by decide +kernel

theorem check_48_43 : checkAV 48 43 items_48_43 = true := by decide +kernel

theorem check_48_44 : checkAV 48 44 items_48_44 = true := by decide +kernel

theorem check_48_45 : checkAV 48 45 items_48_45 = true := by decide +kernel

theorem check_48_46 : checkAV 48 46 items_48_46 = true := by decide +kernel

theorem check_48_47 : checkAV 48 47 items_48_47 = true := by decide +kernel

/-- The check of the order 48. -/
theorem order_48 : checkOrderV 48 24 [items_48_24, items_48_25, items_48_26, items_48_27, items_48_28, items_48_29, items_48_30, items_48_31, items_48_32, items_48_33, items_48_34, items_48_35, items_48_36, items_48_37, items_48_38, items_48_39, items_48_40, items_48_41, items_48_42, items_48_43, items_48_44, items_48_45, items_48_46, items_48_47] = true := by
  simp only [checkOrderV, check_48_24, check_48_25, check_48_26, check_48_27, check_48_28, check_48_29, check_48_30, check_48_31, check_48_32, check_48_33, check_48_34, check_48_35, check_48_36, check_48_37, check_48_38, check_48_39, check_48_40, check_48_41, check_48_42, check_48_43, check_48_44, check_48_45, check_48_46, check_48_47, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
