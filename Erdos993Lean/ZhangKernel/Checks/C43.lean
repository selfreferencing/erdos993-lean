import Erdos993Lean.ZhangKernel.Data.O43

/-!
# Kernel-checked finite part: the checks of the orders 43

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

theorem check_43_22 : checkAV 43 22 items_43_22 = true := by decide +kernel

theorem check_43_23 : checkAV 43 23 items_43_23 = true := by decide +kernel

theorem check_43_24 : checkAV 43 24 items_43_24 = true := by decide +kernel

theorem check_43_25 : checkAV 43 25 items_43_25 = true := by decide +kernel

theorem check_43_26 : checkAV 43 26 items_43_26 = true := by decide +kernel

theorem check_43_27 : checkAV 43 27 items_43_27 = true := by decide +kernel

theorem check_43_28 : checkAV 43 28 items_43_28 = true := by decide +kernel

theorem check_43_29 : checkAV 43 29 items_43_29 = true := by decide +kernel

theorem check_43_30 : checkAV 43 30 items_43_30 = true := by decide +kernel

theorem check_43_31 : checkAV 43 31 items_43_31 = true := by decide +kernel

theorem check_43_32 : checkAV 43 32 items_43_32 = true := by decide +kernel

theorem check_43_33 : checkAV 43 33 items_43_33 = true := by decide +kernel

theorem check_43_34 : checkAV 43 34 items_43_34 = true := by decide +kernel

theorem check_43_35 : checkAV 43 35 items_43_35 = true := by decide +kernel

theorem check_43_36 : checkAV 43 36 items_43_36 = true := by decide +kernel

theorem check_43_37 : checkAV 43 37 items_43_37 = true := by decide +kernel

theorem check_43_38 : checkAV 43 38 items_43_38 = true := by decide +kernel

theorem check_43_39 : checkAV 43 39 items_43_39 = true := by decide +kernel

theorem check_43_40 : checkAV 43 40 items_43_40 = true := by decide +kernel

theorem check_43_41 : checkAV 43 41 items_43_41 = true := by decide +kernel

theorem check_43_42 : checkAV 43 42 items_43_42 = true := by decide +kernel

/-- The check of the order 43. -/
theorem order_43 : checkOrderV 43 22 [items_43_22, items_43_23, items_43_24, items_43_25, items_43_26, items_43_27, items_43_28, items_43_29, items_43_30, items_43_31, items_43_32, items_43_33, items_43_34, items_43_35, items_43_36, items_43_37, items_43_38, items_43_39, items_43_40, items_43_41, items_43_42] = true := by
  simp only [checkOrderV, check_43_22, check_43_23, check_43_24, check_43_25, check_43_26, check_43_27, check_43_28, check_43_29, check_43_30, check_43_31, check_43_32, check_43_33, check_43_34, check_43_35, check_43_36, check_43_37, check_43_38, check_43_39, check_43_40, check_43_41, check_43_42, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
