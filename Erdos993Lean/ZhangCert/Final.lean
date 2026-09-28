import Erdos993Lean.ZhangCert.Main
import Erdos993Lean.Zhang.Rows.Main

/-!
# Every forest with at most 60 vertices is unimodal

T. Zhang's finite-order theorem (manuscript "Exact Certificates for Unimodality of Forest
Independence Polynomials", v1.1, 2026, Proposition 1.2), proved in Lean: the reduction
`Zhang.finite60_of_sound` (default target), the inequality families `Zhang.Rows.rowsSound`
(default target, standard axioms), and the certificate claim `Zhang.certificatesSound` (this
optional target; one `native_decide`, `ZhangCertX.checkRange_2_60`, evaluated on the author's data
by a checker whose soundness is proved for any data).
-/

namespace Erdos993Lean.Zhang

/-- **Every forest with at most 60 vertices has a unimodal independence sequence** (in the
semantics of the pinned #993 statement).  Uses one `native_decide` (the certificate check). -/
theorem forest_unimodal_of_card_le_sixty (F : FiniteForest) (hn : F.n ≤ 60) :
    independenceSequenceUnimodal F :=
  finite60_of_rows Rows.rowsSound F hn

end Erdos993Lean.Zhang
