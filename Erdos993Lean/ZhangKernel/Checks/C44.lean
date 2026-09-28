import Erdos993Lean.ZhangKernel.Data.O44

/-!
# Kernel-checked finite part: the checks of the orders 44

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

theorem check_44_22 : checkAV 44 22 items_44_22 = true := by decide +kernel

theorem check_44_23 : checkAV 44 23 items_44_23 = true := by decide +kernel

theorem check_44_24 : checkAV 44 24 items_44_24 = true := by decide +kernel

theorem check_44_25 : checkAV 44 25 items_44_25 = true := by decide +kernel

theorem check_44_26 : checkAV 44 26 items_44_26 = true := by decide +kernel

theorem check_44_27 : checkAV 44 27 items_44_27 = true := by decide +kernel

theorem check_44_28 : checkAV 44 28 items_44_28 = true := by decide +kernel

theorem check_44_29 : checkAV 44 29 items_44_29 = true := by decide +kernel

theorem check_44_30 : checkAV 44 30 items_44_30 = true := by decide +kernel

theorem check_44_31 : checkAV 44 31 items_44_31 = true := by decide +kernel

theorem check_44_32 : checkAV 44 32 items_44_32 = true := by decide +kernel

theorem check_44_33 : checkAV 44 33 items_44_33 = true := by decide +kernel

theorem check_44_34 : checkAV 44 34 items_44_34 = true := by decide +kernel

theorem check_44_35 : checkAV 44 35 items_44_35 = true := by decide +kernel

theorem check_44_36 : checkAV 44 36 items_44_36 = true := by decide +kernel

theorem check_44_37 : checkAV 44 37 items_44_37 = true := by decide +kernel

theorem check_44_38 : checkAV 44 38 items_44_38 = true := by decide +kernel

theorem check_44_39 : checkAV 44 39 items_44_39 = true := by decide +kernel

theorem check_44_40 : checkAV 44 40 items_44_40 = true := by decide +kernel

theorem check_44_41 : checkAV 44 41 items_44_41 = true := by decide +kernel

theorem check_44_42 : checkAV 44 42 items_44_42 = true := by decide +kernel

theorem check_44_43 : checkAV 44 43 items_44_43 = true := by decide +kernel

/-- The check of the order 44. -/
theorem order_44 : checkOrderV 44 22 [items_44_22, items_44_23, items_44_24, items_44_25, items_44_26, items_44_27, items_44_28, items_44_29, items_44_30, items_44_31, items_44_32, items_44_33, items_44_34, items_44_35, items_44_36, items_44_37, items_44_38, items_44_39, items_44_40, items_44_41, items_44_42, items_44_43] = true := by
  simp only [checkOrderV, check_44_22, check_44_23, check_44_24, check_44_25, check_44_26, check_44_27, check_44_28, check_44_29, check_44_30, check_44_31, check_44_32, check_44_33, check_44_34, check_44_35, check_44_36, check_44_37, check_44_38, check_44_39, check_44_40, check_44_41, check_44_42, check_44_43, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
