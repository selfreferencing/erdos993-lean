import Erdos993Lean.ZhangKernel.Core

/-!
# Kernel-checked finite part: the literals, re-verified by the kernel

The packed literals of `ZhangKernel/Literals.lean` are generated data; this module recomputes every
lane by kernel evaluation (`decide +kernel`), so that nothing about them is trusted:

* `bRowCheck_eq`: lane `r` of `bRow m` is `ZhangCertX.binomF m r` (the falling-factorial formula,
  proved equal to `Nat.choose` in `ZhangCert/Bridge.lean`) for all `m, r < 64`;
* `tabCheck_eq`: the table lanes satisfy `T_h(r, 0) = x_h(r, 0)` and
  `T_h(r, M + 1) = max(T_h(r, M), x_h(r, M + 1))` for `h < 3` and `r, M + 1 < 64`
  (`tabLane`, `xRef` in `ZhangKernel/Core.lean`), i.e. `T_h(r, M)` is the largest `x_h(r, m)`,
  `m ≤ M`.

The consequences (`chooseK = Nat.choose`, `tabLane` is the maximum) are drawn in
`ZhangKernel/Mirror.lean` and `ZhangKernel/Direct.lean`.
-/

namespace Erdos993Lean

namespace ZhangKernel

open ZhangCertX

/-- Lane `r` of the packed binomial row `bRow m`. -/
def bLane (m r : Nat) : Nat := Nat.land (Nat.shiftRight (bRow m) (Nat.mul 64 r)) mask64

/-- Every lane of `bRow` is the falling-factorial binomial `binomF`. -/
def bRowCheck : Bool :=
  (List.range 64).all fun m => (List.range 64).all fun r => Nat.beq (bLane m r) (binomF m r)

/-- The recurrence of the tables: `T_h(r, 0) = x_h(r, 0)`,
`T_h(r, M + 1) = max(T_h(r, M), x_h(r, M + 1))`. -/
def tabCheck : Bool :=
  (List.range 3).all fun h => (List.range 64).all fun r =>
    eqK (tabLane h r 0) (xRef h r 0) &&
      (List.range 63).all fun M =>
        eqK (tabLane h r (M + 1)) (maxK (tabLane h r M) (xRef h r (M + 1)))

set_option Elab.async false

-- Report the kernel's evaluation time of each check ("type checking took ...").
set_option profiler true
set_option profiler.threshold 100

/-- The packed binomial rows, checked by the kernel. -/
theorem bRowCheck_eq : bRowCheck = true := by decide +kernel

/-- The packed tables, checked by the kernel. -/
theorem tabCheck_eq : tabCheck = true := by decide +kernel

end ZhangKernel

end Erdos993Lean
