import Erdos993LeanZhangCompute.Checker

/-!
# Zhang's finite-part certificates: the check

`checkRange_2_60 : checkRange 2 60 = true`, by `native_decide`: for every order `2 ≤ n ≤ 60`
and every `(a, k)` with `⌈n/2⌉ ≤ a ≤ n − 1`, `1 ≤ k < ⌊(2a+1)/3⌋` (the 17,100 triples of the
domain `P60`), the triple passes `tripleOK`: its stored certificate (2,577 triples: 670 separators,
1,907 linear certificates with 142,017 weighted rows) or one of the direct criteria (14,523
triples).  The Boolean check is defined in `Erdos993LeanZhangCompute/Checker.lean` and
`Erdos993LeanZhangCompute/Checker/Core.lean` and is evaluated as natively compiled code (library
`Erdos993LeanZhangCompute`, `precompileModules = true`); this trusts the Lean compiler
(`Lean.ofReduceBool`, `Lean.trustCompiler`).  What the check means is proved with the standard
axioms in `ZhangCert/Bridge.lean` (`checkRange_sound`); the assembly is `ZhangCert/Main.lean`.

It imports only the computational core (not Mathlib).  Run time: see `ZhangCert/Main.lean`.
-/

namespace Erdos993Lean.ZhangCertX

-- Report the evaluation time of the check (it appears as "type checking took ...").
set_option profiler true
set_option profiler.threshold 500

theorem checkRange_2_60 : checkRange 2 60 = true := by native_decide

end Erdos993Lean.ZhangCertX
