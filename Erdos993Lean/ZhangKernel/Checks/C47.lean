import Erdos993Lean.ZhangKernel.Data.O47

/-!
# Kernel-checked finite part: the checks of the orders 47

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

theorem check_47_24 : checkAV 47 24 items_47_24 = true := by decide +kernel

theorem check_47_25 : checkAV 47 25 items_47_25 = true := by decide +kernel

theorem check_47_26 : checkAV 47 26 items_47_26 = true := by decide +kernel

theorem check_47_27 : checkAV 47 27 items_47_27 = true := by decide +kernel

theorem check_47_28 : checkAV 47 28 items_47_28 = true := by decide +kernel

theorem check_47_29 : checkAV 47 29 items_47_29 = true := by decide +kernel

theorem check_47_30 : checkAV 47 30 items_47_30 = true := by decide +kernel

theorem check_47_31 : checkAV 47 31 items_47_31 = true := by decide +kernel

theorem check_47_32 : checkAV 47 32 items_47_32 = true := by decide +kernel

theorem check_47_33 : checkAV 47 33 items_47_33 = true := by decide +kernel

theorem check_47_34 : checkAV 47 34 items_47_34 = true := by decide +kernel

theorem check_47_35 : checkAV 47 35 items_47_35 = true := by decide +kernel

theorem check_47_36 : checkAV 47 36 items_47_36 = true := by decide +kernel

theorem check_47_37 : checkAV 47 37 items_47_37 = true := by decide +kernel

theorem check_47_38 : checkAV 47 38 items_47_38 = true := by decide +kernel

theorem check_47_39 : checkAV 47 39 items_47_39 = true := by decide +kernel

theorem check_47_40 : checkAV 47 40 items_47_40 = true := by decide +kernel

theorem check_47_41 : checkAV 47 41 items_47_41 = true := by decide +kernel

theorem check_47_42 : checkAV 47 42 items_47_42 = true := by decide +kernel

theorem check_47_43 : checkAV 47 43 items_47_43 = true := by decide +kernel

theorem check_47_44 : checkAV 47 44 items_47_44 = true := by decide +kernel

theorem check_47_45 : checkAV 47 45 items_47_45 = true := by decide +kernel

theorem check_47_46 : checkAV 47 46 items_47_46 = true := by decide +kernel

/-- The check of the order 47. -/
theorem order_47 : checkOrderV 47 24 [items_47_24, items_47_25, items_47_26, items_47_27, items_47_28, items_47_29, items_47_30, items_47_31, items_47_32, items_47_33, items_47_34, items_47_35, items_47_36, items_47_37, items_47_38, items_47_39, items_47_40, items_47_41, items_47_42, items_47_43, items_47_44, items_47_45, items_47_46] = true := by
  simp only [checkOrderV, check_47_24, check_47_25, check_47_26, check_47_27, check_47_28, check_47_29, check_47_30, check_47_31, check_47_32, check_47_33, check_47_34, check_47_35, check_47_36, check_47_37, check_47_38, check_47_39, check_47_40, check_47_41, check_47_42, check_47_43, check_47_44, check_47_45, check_47_46, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
