import Erdos993Lean.ZhangCert.Checks
import Erdos993Lean.ZhangCert.Bridge
import Erdos993Lean.Zhang.Finite60

/-!
# Zhang's finite-part certificates checked in Lean (optional target `Erdos993LeanZhangCert`)

**Theorems.**
* `Erdos993Lean.Zhang.certificatesSound : Cert.CertificatesSound`: the certificate layer of
  T. Zhang's finite part (*Exact Certificates for Unimodality of Forest Independence Polynomials*,
  v1.1, Table 1): for every triple `(n, a, k)` of the domain `P60` (35) (17,100 triples), every
  feasible array of the relaxation of Section 2.9 (`Cert.Feasible`: the basic constraints (5) and
  the eleven row families on their domains) with `Δ_k ≤ 0` has `Δ_{k+1} ≤ 0` (`Cert.NoRecovery`).
* `Erdos993Lean.Zhang.finite60_of_rows : RowsSound → ∀ F : FiniteForest, F.n ≤ 60 →
  independenceSequenceUnimodal F`: Zhang's Theorem 2.1 (every forest with at most 60 vertices is
  unimodal) from row soundness alone (`Zhang.RowsSound`, the named hypothesis of
  `Zhang/Finite60.lean`: Lemmas 2.3–2.10 with the choice of Lemma 2.5), through
  `Zhang.finite60_of_sound`.

**Method.**  The author's data (`certificates.json`, SHA-256
`a77f4fc43aec1b8eecab91c4418b6990f72dee69d802129c78efd67d2e1bcc5a`) is stored as one string of
numbers per order in `Erdos993LeanZhangCompute/Checker/Data1.lean` … `Data5.lean`.  The checker
(`Erdos993LeanZhangCompute/Checker.lean`, `Checker/Core.lean`; Lean core only, exact `Int`/`Nat`
arithmetic) regenerates the domain `P60`, and for each triple checks its stored certificate
(separator, or linear certificate with the author's normalization (39)) or else the direct
criteria (path row against the matching bound, lower and upper layer rules), each as an instance
of the certificate principle (40) with integer data; the free constant `η` is the largest layer-1
residual.  `ZhangCert/Bridge.lean` proves with the standard axioms that a passing check gives
`Cert.NoRecovery` (`checkRange_sound`): the checker's integer rows are exactly the rows of
`Zhang/Relaxation.lean` (`coefZ_cast`, `rhsZ_cast`), and the bound it computes is the right side of
`Cert.certificate_bound` for the aggregated row (`genericOK_sound`).  Nothing about the data, the
parsing, the normalization or the choice of certificate needs to be trusted: the bridge holds for
every stored data string.

**Trust.**  `native_decide` is used exactly once, in `ZhangCert/Checks.lean`:
`checkRange_2_60 : checkRange 2 60 = true`.  It trusts the Lean compiler (`Lean.ofReduceBool`,
`Lean.trustCompiler`), here including the natively compiled code of the library
`Erdos993LeanZhangCompute` (`precompileModules = true`) and the C compiler used by Lake.
`Bridge.lean` and the Zhang files it builds on use only `propext`, `Classical.choice`,
`Quot.sound`.  No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `extern` or `partial` in
these files or in the checker.

**Coverage** (informational, from the checker's own functions): of the 17,100 triples, 2,577
use their stored certificate (670 separators, 603 positive, 158 negative and 1,146 conditional
linear certificates, 142,017 weighted rows; every stored entry lies in `P60` and is used), and
14,523 a direct criterion (5,827 the path row against the matching bound, 6,606 the lower layer
rule, 2,090 the upper layer rule).  The stored part is the paper's Table 1; in the direct part the
897 triples with `k = 1` (Table 1: path-vs-matching) go to the lower layer rule, because the row
`path(1)` is outside its domain (`2 ≤ r`); there `Δ_1 = n − 1 > 0`.  The free constant `η` of each
linear certificate is recomputed (the largest layer-1 residual), which never gives a larger bound
than the stored `η`; the stored `η` is not read.

**Build.**  `lake build Erdos993LeanZhangCert` (not part of the default target).  Run times
(measured 2026-09-27 on the development machine, 10-core Apple Silicon, 32 GB, under a load average
of about 9 from other jobs): library `Erdos993LeanZhangCompute` (seven modules, 1.6 MB of data
strings, C compilation included) 3–5 s; `Bridge.lean` 23–56 s (mostly importing Mathlib);
`Checks.lean` 3–11 s, of which the `native_decide` evaluation is 2.8–6.0 s ("type checking took",
`set_option profiler true`), peak memory about 680 MB; `Main.lean` 27–56 s.  The same check also
passes in Lean's IR interpreter, without the natively compiled library (`lake env lean
Erdos993Lean/ZhangCert/Checks.lean`, evaluation 28 s), i.e. without the C compiler.  A Python
prototype of the same checker (exact integers, same normalization) takes 16 s.

**What remains** for a Lean proof that every forest with at most 60 vertices is unimodal:
`Zhang.RowsSound` (the row families `private`, `hall`, `tail`, `release_upper`, `tail_upper`,
`union`, `mean`, `edge_lower`, `edge_upper` for the maximum independent set of Lemma 2.5; `count`
and `path` are proved in `Zhang/Finite60.lean`).
-/

namespace Erdos993Lean

namespace Zhang

/-- **The certificate layer of Zhang's finite part** (Table 1): no feasible array of the
relaxation recovers after a nonpositive difference, on every triple of `P60`.  From the single
`native_decide` check `ZhangCertX.checkRange_2_60` and the bridge `ZhangCertX.checkRange_sound`. -/
theorem certificatesSound : Cert.CertificatesSound := by
  intro n a k hP
  exact ZhangCertX.checkRange_sound ZhangCertX.checkRange_2_60 n a k hP.1 hP.2.1 hP

/-- **Zhang's Theorem 2.1 from row soundness**: if every forest with an edge has a maximum
independent set whose count array satisfies the row families of Section 2.9 (`RowsSound`), then
every forest with at most 60 vertices is unimodal. -/
theorem finite60_of_rows (h : RowsSound) :
    ∀ F : FiniteForest, F.n ≤ 60 → independenceSequenceUnimodal F :=
  fun F hn => finite60_of_sound h certificatesSound F hn

end Zhang

end Erdos993Lean
