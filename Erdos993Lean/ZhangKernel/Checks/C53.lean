import Erdos993Lean.ZhangKernel.Data.O53

/-!
# Kernel-checked finite part: the checks of the orders 53

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

theorem check_53_27 : checkAV 53 27 items_53_27 = true := by decide +kernel

theorem check_53_28 : checkAV 53 28 items_53_28 = true := by decide +kernel

theorem check_53_29 : checkAV 53 29 items_53_29 = true := by decide +kernel

theorem check_53_30 : checkAV 53 30 items_53_30 = true := by decide +kernel

theorem check_53_31 : checkAV 53 31 items_53_31 = true := by decide +kernel

theorem check_53_32 : checkAV 53 32 items_53_32 = true := by decide +kernel

theorem check_53_33 : checkAV 53 33 items_53_33 = true := by decide +kernel

theorem check_53_34 : checkAV 53 34 items_53_34 = true := by decide +kernel

theorem check_53_35 : checkAV 53 35 items_53_35 = true := by decide +kernel

theorem check_53_36 : checkAV 53 36 items_53_36 = true := by decide +kernel

theorem check_53_37 : checkAV 53 37 items_53_37 = true := by decide +kernel

theorem check_53_38 : checkAV 53 38 items_53_38 = true := by decide +kernel

theorem check_53_39 : checkAV 53 39 items_53_39 = true := by decide +kernel

theorem check_53_40 : checkAV 53 40 items_53_40 = true := by decide +kernel

theorem check_53_41 : checkAV 53 41 items_53_41 = true := by decide +kernel

theorem check_53_42 : checkAV 53 42 items_53_42 = true := by decide +kernel

theorem check_53_43 : checkAV 53 43 items_53_43 = true := by decide +kernel

theorem check_53_44 : checkAV 53 44 items_53_44 = true := by decide +kernel

theorem check_53_45 : checkAV 53 45 items_53_45 = true := by decide +kernel

theorem check_53_46 : checkAV 53 46 items_53_46 = true := by decide +kernel

theorem check_53_47 : checkAV 53 47 items_53_47 = true := by decide +kernel

theorem check_53_48 : checkAV 53 48 items_53_48 = true := by decide +kernel

theorem check_53_49 : checkAV 53 49 items_53_49 = true := by decide +kernel

theorem check_53_50 : checkAV 53 50 items_53_50 = true := by decide +kernel

theorem check_53_51 : checkAV 53 51 items_53_51 = true := by decide +kernel

theorem check_53_52 : checkAV 53 52 items_53_52 = true := by decide +kernel

/-- The check of the order 53. -/
theorem order_53 : checkOrderV 53 27 [items_53_27, items_53_28, items_53_29, items_53_30, items_53_31, items_53_32, items_53_33, items_53_34, items_53_35, items_53_36, items_53_37, items_53_38, items_53_39, items_53_40, items_53_41, items_53_42, items_53_43, items_53_44, items_53_45, items_53_46, items_53_47, items_53_48, items_53_49, items_53_50, items_53_51, items_53_52] = true := by
  simp only [checkOrderV, check_53_27, check_53_28, check_53_29, check_53_30, check_53_31, check_53_32, check_53_33, check_53_34, check_53_35, check_53_36, check_53_37, check_53_38, check_53_39, check_53_40, check_53_41, check_53_42, check_53_43, check_53_44, check_53_45, check_53_46, check_53_47, check_53_48, check_53_49, check_53_50, check_53_51, check_53_52, Bool.true_and, Nat.add_eq, Nat.reduceAdd, Nat.beq_refl]

end ZhangKernel

end Erdos993Lean
