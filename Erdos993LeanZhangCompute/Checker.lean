import Erdos993LeanZhangCompute.Checker.Core
import Erdos993LeanZhangCompute.Checker.Data1
import Erdos993LeanZhangCompute.Checker.Data2
import Erdos993LeanZhangCompute.Checker.Data3
import Erdos993LeanZhangCompute.Checker.Data4
import Erdos993LeanZhangCompute.Checker.Data5

/-!
# Zhang's finite-part certificates: the checks

Root of the library `Erdos993LeanZhangCompute` (`precompileModules = true`; imports only Lean's
core and the modules `Checker/Core.lean`, `Checker/Data1.lean` … `Checker/Data5.lean`).

* `dataFor n`: the stored certificates of order `n` (the empty string for `n < 12`, where the direct
  criteria cover every triple).
* `checkRange lo hi`: `checkN n (dataFor n)` for every `lo ≤ n ≤ hi`, that is, every triple
  `(n, a, k)` of the domain `P60` with `lo ≤ n ≤ hi` passes `tripleOK` (its stored certificate, or
  a direct criterion).

`Erdos993Lean/ZhangCert/Bridge.lean` proves (standard axioms only) that `checkRange lo hi = true`
implies `Cert.NoRecovery n a k` for every triple of `P60` with `lo ≤ n ≤ hi`; the checks
themselves are the `native_decide` theorems of `Erdos993Lean/ZhangCert/Checks*.lean`.

The only compiler hint is `@[noinline]` on `checkRange`, which keeps each check a single call into
the precompiled library when a downstream `native_decide` evaluates it.
-/

namespace Erdos993Lean

namespace ZhangCertX

/-- The stored certificates of order `n` (see `Checker/Data*.lean`). -/
def dataFor : Nat → String
  | 12 => data12
  | 13 => data13
  | 14 => data14
  | 15 => data15
  | 16 => data16
  | 17 => data17
  | 18 => data18
  | 19 => data19
  | 20 => data20
  | 21 => data21
  | 22 => data22
  | 23 => data23
  | 24 => data24
  | 25 => data25
  | 26 => data26
  | 27 => data27
  | 28 => data28
  | 29 => data29
  | 30 => data30
  | 31 => data31
  | 32 => data32
  | 33 => data33
  | 34 => data34
  | 35 => data35
  | 36 => data36
  | 37 => data37
  | 38 => data38
  | 39 => data39
  | 40 => data40
  | 41 => data41
  | 42 => data42
  | 43 => data43
  | 44 => data44
  | 45 => data45
  | 46 => data46
  | 47 => data47
  | 48 => data48
  | 49 => data49
  | 50 => data50
  | 51 => data51
  | 52 => data52
  | 53 => data53
  | 54 => data54
  | 55 => data55
  | 56 => data56
  | 57 => data57
  | 58 => data58
  | 59 => data59
  | 60 => data60
  | _ => ""

/-- **The check of the orders `lo ≤ n ≤ hi`.** -/
@[noinline] def checkRange (lo hi : Nat) : Bool :=
  (List.range' lo (hi + 1 - lo)).all fun n => checkN n (dataFor n)

end ZhangCertX

end Erdos993Lean
