import Erdos993Lean.Analytic.Top
import Erdos993Lean.Analytic.HardCore.Mixture

/-!
# The conditional top theorem with the mixture facts discharged

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  The facts about the conditional
binomial mixture (`MixtureFacts`, Zhang (45)–(46)) are proved in Lean (`mixtureFacts`, lane A1), so the
top theorem of the analytic route rests on Zhang's certificate layer for forests with at most 60
vertices (`Zhang.Cert.CertificatesSound`) and on the analytic inputs O1–O5 (`AnalyticInputs P`) only.
This file uses no `native_decide`; the certificate layer is a hypothesis here and is discharged in the
optional library `Erdos993LeanAnalyticFinal` (`Analytic/TopFinal.lean`).
-/

namespace Erdos993Lean.Analytic

/-- **Erdős #993 from the analytic inputs and Zhang's certificate layer.**  Every finite forest has a
unimodal independence sequence, given Zhang's certificate claim on `P60` and the analytic inputs O1–O5
for some profile `P`. -/
theorem erdos993_of_analytic_inputs_cert (hcert : Zhang.Cert.CertificatesSound) {P : Profile}
    (h : AnalyticInputs P) : Erdos993Statement :=
  erdos993_of_analytic_inputs_pending mixtureFacts hcert h

end Erdos993Lean.Analytic
