import Erdos993Lean.ZhangKernel.Data.O45

/-!
# Kernel-checked finite part: the checks of the orders 45

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

theorem check_45_23 : checkAV 45 23 items_45_23 = true := by decide +kernel

theorem check_45_24 : checkAV 45 24 items_45_24 = true := by decide +kernel

theorem check_45_25 : checkAV 45 25 items_45_25 = true := by decide +kernel

theorem check_45_26 : checkAV 45 26 items_45_26 = true := by decide +kernel

theorem check_45_27 : checkAV 45 27 items_45_27 = true := by decide +kernel

theorem check_45_28 : checkAV 45 28 items_45_28 = true := by decide +kernel

theorem check_45_29 : checkAV 45 29 items_45_29 = true := by decide +kernel

theorem check_45_30 : checkAV 45 30 items_45_30 = true := by decide +kernel

theorem check_45_31 : checkAV 45 31 items_45_31 = true := by decide +kernel

theorem check_45_32 : checkAV 45 32 items_45_32 = true := by decide +kernel

theorem check_45_33 : checkAV 45 33 items_45_33 = true := by decide +kernel

theorem check_45_34 : checkAV 45 34 items_45_34 = true := by decide +kernel

theorem check_45_35 : checkAV 45 35 items_45_35 = true := by decide +kernel

theorem check_45_36 : checkAV 45 36 items_45_36 = true := by decide +kernel

theorem check_45_37 : checkAV 45 37 items_45_37 = true := by decide +kernel

theorem check_45_38 : checkAV 45 38 items_45_38 = true := by decide +kernel

theorem check_45_39 : checkAV 45 39 items_45_39 = true := by decide +kernel

theorem check_45_40 : checkAV 45 40 items_45_40 = true := by decide +kernel

theorem check_45_41 : checkAV 45 41 items_45_41 = true := by decide +kernel

theorem check_45_42 : checkAV 45 42 items_45_42 = true := by decide +kernel

theorem check_45_43 : checkAV 45 43 items_45_43 = true := by decide +kernel

theorem check_45_44 : checkAV 45 44 items_45_44 = true := by decide +kernel

/-- The check of the order 45. -/
theorem order_45 : checkOrderV 45 23 [items_45_23, items_45_24, items_45_25, items_45_26, items_45_27, items_45_28, items_45_29, items_45_30, items_45_31, items_45_32, items_45_33, items_45_34, items_45_35, items_45_36, items_45_37, items_45_38, items_45_39, items_45_40, items_45_41, items_45_42, items_45_43, items_45_44] = true := by
  simp only [checkOrderV, check_45_23, check_45_24, check_45_25, check_45_26, check_45_27, check_45_28, check_45_29, check_45_30, check_45_31, check_45_32, check_45_33, check_45_34, check_45_35, check_45_36, check_45_37, check_45_38, check_45_39, check_45_40, check_45_41, check_45_42, check_45_43, check_45_44, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
