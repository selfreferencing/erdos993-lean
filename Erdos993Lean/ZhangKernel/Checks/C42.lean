import Erdos993Lean.ZhangKernel.Data.O42

/-!
# Kernel-checked finite part: the checks of the orders 42

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

theorem check_42_21 : checkAV 42 21 items_42_21 = true := by decide +kernel

theorem check_42_22 : checkAV 42 22 items_42_22 = true := by decide +kernel

theorem check_42_23 : checkAV 42 23 items_42_23 = true := by decide +kernel

theorem check_42_24 : checkAV 42 24 items_42_24 = true := by decide +kernel

theorem check_42_25 : checkAV 42 25 items_42_25 = true := by decide +kernel

theorem check_42_26 : checkAV 42 26 items_42_26 = true := by decide +kernel

theorem check_42_27 : checkAV 42 27 items_42_27 = true := by decide +kernel

theorem check_42_28 : checkAV 42 28 items_42_28 = true := by decide +kernel

theorem check_42_29 : checkAV 42 29 items_42_29 = true := by decide +kernel

theorem check_42_30 : checkAV 42 30 items_42_30 = true := by decide +kernel

theorem check_42_31 : checkAV 42 31 items_42_31 = true := by decide +kernel

theorem check_42_32 : checkAV 42 32 items_42_32 = true := by decide +kernel

theorem check_42_33 : checkAV 42 33 items_42_33 = true := by decide +kernel

theorem check_42_34 : checkAV 42 34 items_42_34 = true := by decide +kernel

theorem check_42_35 : checkAV 42 35 items_42_35 = true := by decide +kernel

theorem check_42_36 : checkAV 42 36 items_42_36 = true := by decide +kernel

theorem check_42_37 : checkAV 42 37 items_42_37 = true := by decide +kernel

theorem check_42_38 : checkAV 42 38 items_42_38 = true := by decide +kernel

theorem check_42_39 : checkAV 42 39 items_42_39 = true := by decide +kernel

theorem check_42_40 : checkAV 42 40 items_42_40 = true := by decide +kernel

theorem check_42_41 : checkAV 42 41 items_42_41 = true := by decide +kernel

/-- The check of the order 42. -/
theorem order_42 : checkOrderV 42 21 [items_42_21, items_42_22, items_42_23, items_42_24, items_42_25, items_42_26, items_42_27, items_42_28, items_42_29, items_42_30, items_42_31, items_42_32, items_42_33, items_42_34, items_42_35, items_42_36, items_42_37, items_42_38, items_42_39, items_42_40, items_42_41] = true := by
  simp only [checkOrderV, check_42_21, check_42_22, check_42_23, check_42_24, check_42_25, check_42_26, check_42_27, check_42_28, check_42_29, check_42_30, check_42_31, check_42_32, check_42_33, check_42_34, check_42_35, check_42_36, check_42_37, check_42_38, check_42_39, check_42_40, check_42_41, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
