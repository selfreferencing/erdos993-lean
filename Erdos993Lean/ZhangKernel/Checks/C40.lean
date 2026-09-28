import Erdos993Lean.ZhangKernel.Data.O40

/-!
# Kernel-checked finite part: the checks of the orders 40

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

theorem check_40_20 : checkAV 40 20 items_40_20 = true := by decide +kernel

theorem check_40_21 : checkAV 40 21 items_40_21 = true := by decide +kernel

theorem check_40_22 : checkAV 40 22 items_40_22 = true := by decide +kernel

theorem check_40_23 : checkAV 40 23 items_40_23 = true := by decide +kernel

theorem check_40_24 : checkAV 40 24 items_40_24 = true := by decide +kernel

theorem check_40_25 : checkAV 40 25 items_40_25 = true := by decide +kernel

theorem check_40_26 : checkAV 40 26 items_40_26 = true := by decide +kernel

theorem check_40_27 : checkAV 40 27 items_40_27 = true := by decide +kernel

theorem check_40_28 : checkAV 40 28 items_40_28 = true := by decide +kernel

theorem check_40_29 : checkAV 40 29 items_40_29 = true := by decide +kernel

theorem check_40_30 : checkAV 40 30 items_40_30 = true := by decide +kernel

theorem check_40_31 : checkAV 40 31 items_40_31 = true := by decide +kernel

theorem check_40_32 : checkAV 40 32 items_40_32 = true := by decide +kernel

theorem check_40_33 : checkAV 40 33 items_40_33 = true := by decide +kernel

theorem check_40_34 : checkAV 40 34 items_40_34 = true := by decide +kernel

theorem check_40_35 : checkAV 40 35 items_40_35 = true := by decide +kernel

theorem check_40_36 : checkAV 40 36 items_40_36 = true := by decide +kernel

theorem check_40_37 : checkAV 40 37 items_40_37 = true := by decide +kernel

theorem check_40_38 : checkAV 40 38 items_40_38 = true := by decide +kernel

theorem check_40_39 : checkAV 40 39 items_40_39 = true := by decide +kernel

/-- The check of the order 40. -/
theorem order_40 : checkOrderV 40 20 [items_40_20, items_40_21, items_40_22, items_40_23, items_40_24, items_40_25, items_40_26, items_40_27, items_40_28, items_40_29, items_40_30, items_40_31, items_40_32, items_40_33, items_40_34, items_40_35, items_40_36, items_40_37, items_40_38, items_40_39] = true := by
  simp only [checkOrderV, check_40_20, check_40_21, check_40_22, check_40_23, check_40_24, check_40_25, check_40_26, check_40_27, check_40_28, check_40_29, check_40_30, check_40_31, check_40_32, check_40_33, check_40_34, check_40_35, check_40_36, check_40_37, check_40_38, check_40_39, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
