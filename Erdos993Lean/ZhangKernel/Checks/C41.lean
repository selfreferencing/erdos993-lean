import Erdos993Lean.ZhangKernel.Data.O41

/-!
# Kernel-checked finite part: the checks of the orders 41

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

theorem check_41_21 : checkAV 41 21 items_41_21 = true := by decide +kernel

theorem check_41_22 : checkAV 41 22 items_41_22 = true := by decide +kernel

theorem check_41_23 : checkAV 41 23 items_41_23 = true := by decide +kernel

theorem check_41_24 : checkAV 41 24 items_41_24 = true := by decide +kernel

theorem check_41_25 : checkAV 41 25 items_41_25 = true := by decide +kernel

theorem check_41_26 : checkAV 41 26 items_41_26 = true := by decide +kernel

theorem check_41_27 : checkAV 41 27 items_41_27 = true := by decide +kernel

theorem check_41_28 : checkAV 41 28 items_41_28 = true := by decide +kernel

theorem check_41_29 : checkAV 41 29 items_41_29 = true := by decide +kernel

theorem check_41_30 : checkAV 41 30 items_41_30 = true := by decide +kernel

theorem check_41_31 : checkAV 41 31 items_41_31 = true := by decide +kernel

theorem check_41_32 : checkAV 41 32 items_41_32 = true := by decide +kernel

theorem check_41_33 : checkAV 41 33 items_41_33 = true := by decide +kernel

theorem check_41_34 : checkAV 41 34 items_41_34 = true := by decide +kernel

theorem check_41_35 : checkAV 41 35 items_41_35 = true := by decide +kernel

theorem check_41_36 : checkAV 41 36 items_41_36 = true := by decide +kernel

theorem check_41_37 : checkAV 41 37 items_41_37 = true := by decide +kernel

theorem check_41_38 : checkAV 41 38 items_41_38 = true := by decide +kernel

theorem check_41_39 : checkAV 41 39 items_41_39 = true := by decide +kernel

theorem check_41_40 : checkAV 41 40 items_41_40 = true := by decide +kernel

/-- The check of the order 41. -/
theorem order_41 : checkOrderV 41 21 [items_41_21, items_41_22, items_41_23, items_41_24, items_41_25, items_41_26, items_41_27, items_41_28, items_41_29, items_41_30, items_41_31, items_41_32, items_41_33, items_41_34, items_41_35, items_41_36, items_41_37, items_41_38, items_41_39, items_41_40] = true := by
  simp only [checkOrderV, check_41_21, check_41_22, check_41_23, check_41_24, check_41_25, check_41_26, check_41_27, check_41_28, check_41_29, check_41_30, check_41_31, check_41_32, check_41_33, check_41_34, check_41_35, check_41_36, check_41_37, check_41_38, check_41_39, check_41_40, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
