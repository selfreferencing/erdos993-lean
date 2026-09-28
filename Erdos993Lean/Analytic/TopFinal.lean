import Erdos993Lean.Analytic.TopCert
import Erdos993Lean.ZhangCert.Main

/-!
# The conditional top theorem of the analytic route (Phase 1 target)

Optional library `Erdos993LeanAnalyticFinal`.  Zhang's certificate layer is discharged by
`Zhang.certificatesSound` (optional target `Erdos993LeanZhangCert`, one `native_decide`:
`ZhangCertX.checkRange_2_60`), so this theorem also depends on `Lean.ofReduceBool` and
`Lean.trustCompiler` until the certificate check is re-done by the kernel (lane K).  The open content
of the route is exactly `AnalyticInputs P`.
-/

namespace Erdos993Lean.Analytic

/-- **Erdős #993 from the analytic inputs** (the Phase 1 target of the Lean campaign): every finite
forest has a unimodal independence sequence, given the analytic inputs O1–O5 for some profile `P`. -/
theorem erdos993_of_analytic_inputs {P : Profile} (h : AnalyticInputs P) : Erdos993Statement :=
  erdos993_of_analytic_inputs_cert Zhang.certificatesSound h

end Erdos993Lean.Analytic
