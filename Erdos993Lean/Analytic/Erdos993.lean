import Erdos993Lean.Analytic.Reserve.UpperCert.Final
import Erdos993Lean.Analytic.O2.Final
import Erdos993Lean.Analytic.O2.Cert.Main

/-!
# Erdős Problem #993: every finite forest has a unimodal independence sequence

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  This file states the unconditional theorem.

* **Forests with at most 60 vertices.** T. Zhang's finite-order theorem (*Exact Certificates for Unimodality of Forest
  Independence Polynomials*, v1.1, Proposition 1.2), formalized with all 17,100 of his certificates checked by the Lean
  kernel (lane K, `Erdos993Lean/ZhangKernel/`).
* **Forests with at least 61 vertices.** The analytic route built on Zhang's conditional binomial mixture over a
  maximum-weight independent set:
  - O1 (`VarianceBound Profile30.P`, `Reserve/UpperCert/Final.lean`);
  - O2 (`VarianceRatioBound Profile30.P`, below);
  - the lower tail O3, the no-valley atlas and large-mean theorem O4, the density floor O5 and the activity window O6
    (all used inside `erdos993_of_O2`).

O2 comes from the 14 certified rows. `O2.varianceRatioBound_profile30_of_certs` (lane A16) reduces it to the local
payment and the leaf endpoint of each row, and `O2.Cert.localPaymentOK_all` and `O2.Cert.leafOK_all` (lane A18) prove
those two from the certificates.

Trust.  Every soundness theorem uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).  The
certificate evaluations of the analytic route are done by `native_decide`, and they add `Lean.ofReduceBool` and
`Lean.trustCompiler`.  There are 271 such evaluations: 30 tail bands, 60 atlas bands, 13 O1 checks and 168 O2 root
boxes.  The finite part uses the kernel-checked certificates.  Check with `#print axioms erdos993`.
-/

namespace Erdos993Lean.Analytic

/-- **O2 on the Lean profile.** `Var K ≤ (1 + θ)(1 − q) W` on the whole activity window, from the 14 certified rows. -/
theorem varianceRatioBound_profile30 : VarianceRatioBound Profile30.P :=
  O2.varianceRatioBound_profile30_of_certs O2.Cert.localPaymentOK_all O2.Cert.leafOK_all

/-- **Erdős Problem #993.** Every finite forest has a unimodal independence sequence. -/
theorem erdos993 : Erdos993Statement :=
  Reserve.UpperCert.erdos993_of_O2 varianceRatioBound_profile30

end Erdos993Lean.Analytic
