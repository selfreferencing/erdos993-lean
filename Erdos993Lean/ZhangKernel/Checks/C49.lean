import Erdos993Lean.ZhangKernel.Data.O49

/-!
# Kernel-checked finite part: the checks of the orders 49

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

theorem check_49_25 : checkAV 49 25 items_49_25 = true := by decide +kernel

theorem check_49_26 : checkAV 49 26 items_49_26 = true := by decide +kernel

theorem check_49_27 : checkAV 49 27 items_49_27 = true := by decide +kernel

theorem check_49_28 : checkAV 49 28 items_49_28 = true := by decide +kernel

theorem check_49_29 : checkAV 49 29 items_49_29 = true := by decide +kernel

theorem check_49_30 : checkAV 49 30 items_49_30 = true := by decide +kernel

theorem check_49_31 : checkAV 49 31 items_49_31 = true := by decide +kernel

theorem check_49_32 : checkAV 49 32 items_49_32 = true := by decide +kernel

theorem check_49_33 : checkAV 49 33 items_49_33 = true := by decide +kernel

theorem check_49_34 : checkAV 49 34 items_49_34 = true := by decide +kernel

theorem check_49_35 : checkAV 49 35 items_49_35 = true := by decide +kernel

theorem check_49_36 : checkAV 49 36 items_49_36 = true := by decide +kernel

theorem check_49_37 : checkAV 49 37 items_49_37 = true := by decide +kernel

theorem check_49_38 : checkAV 49 38 items_49_38 = true := by decide +kernel

theorem check_49_39 : checkAV 49 39 items_49_39 = true := by decide +kernel

theorem check_49_40 : checkAV 49 40 items_49_40 = true := by decide +kernel

theorem check_49_41 : checkAV 49 41 items_49_41 = true := by decide +kernel

theorem check_49_42 : checkAV 49 42 items_49_42 = true := by decide +kernel

theorem check_49_43 : checkAV 49 43 items_49_43 = true := by decide +kernel

theorem check_49_44 : checkAV 49 44 items_49_44 = true := by decide +kernel

theorem check_49_45 : checkAV 49 45 items_49_45 = true := by decide +kernel

theorem check_49_46 : checkAV 49 46 items_49_46 = true := by decide +kernel

theorem check_49_47 : checkAV 49 47 items_49_47 = true := by decide +kernel

theorem check_49_48 : checkAV 49 48 items_49_48 = true := by decide +kernel

/-- The check of the order 49. -/
theorem order_49 : checkOrderV 49 25 [items_49_25, items_49_26, items_49_27, items_49_28, items_49_29, items_49_30, items_49_31, items_49_32, items_49_33, items_49_34, items_49_35, items_49_36, items_49_37, items_49_38, items_49_39, items_49_40, items_49_41, items_49_42, items_49_43, items_49_44, items_49_45, items_49_46, items_49_47, items_49_48] = true := by
  simp only [checkOrderV, check_49_25, check_49_26, check_49_27, check_49_28, check_49_29, check_49_30, check_49_31, check_49_32, check_49_33, check_49_34, check_49_35, check_49_36, check_49_37, check_49_38, check_49_39, check_49_40, check_49_41, check_49_42, check_49_43, check_49_44, check_49_45, check_49_46, check_49_47, check_49_48, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
