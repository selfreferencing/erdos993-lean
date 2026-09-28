import Mathlib
import Erdos993Lean.Zhang.Rows.Selection
import Erdos993Lean.Zhang.Rows.EdgeCount
import Erdos993Lean.Zhang.Rows.Coverage
import Erdos993Lean.Zhang.Rows.Mean
import Erdos993Lean.Zhang.Rows.Private
import Erdos993Lean.Zhang.Rows.Deletion
import Erdos993Lean.Zhang.Rows.Hall

/-!
# Zhang's finite part, row soundness 10: `RowsSound`

Source: T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*
(v1.1, 26 Sep 2026), Lemmas 2.2–2.10 with the choice of Lemma 2.5, and Theorem 2.1.

* **`rowsSound : RowsSound`**: every forest with an edge has a maximum independent set (the one
  of Lemma 2.5, `e(F[Y]) ≤ E`, `exists_sparse_maxIndep`) whose count array satisfies all eleven
  row families of Section 2.9 on their domains: `count`, `path` (`Zhang/Finite60.lean`),
  `private` (`Rows/Private.lean`), `hall` (`Rows/Hall.lean`), `tail`, `release_upper`,
  `tail_upper` (`Rows/Deletion.lean`), `mean` (`Rows/Mean.lean`), `union` (`Rows/Coverage.lean`),
  `edge_lower`, `edge_upper` (`Rows/EdgeCount.lean`).
* **`finite60_of_certificates`**: every forest with at most `60` vertices is unimodal, given the
  certificate layer's no-recovery claims on `P60` (`Cert.CertificatesSound`, Table 1).

Grade: PROVED IN LEAN (complete proofs, standard axioms only); `finite60_of_certificates` has
`Cert.CertificatesSound` as its only hypothesis.
-/

namespace Erdos993Lean
namespace Zhang
namespace Rows

open Finset



/-! ### Row soundness -/

/-- **Row soundness** (`Zhang.RowsSound`): every forest with an edge has a maximum independent set
(the one of Lemma 2.5, `e(F[Y]) ≤ E`) whose count array satisfies all eleven row families of
Section 2.9 on their domains (Zhang, Lemmas 2.2–2.10). -/
theorem rowsSound : RowsSound := by
  intro V _ _ G _ hG _
  obtain ⟨I, hI, hIc, he, -⟩ := exists_sparse_maxIndep hG
  refine ⟨I, hI, hIc, ?_⟩
  intro ρ hρ
  cases ρ with
  | count r => exact count_row_holds hI hIc hρ
  | path r => exact path_row_holds hG hI hIc r
  | priv r h => exact priv_row_holds hG hI hIc hρ
  | hall r l => exact hall_row_holds hG hI hIc hρ
  | tail r h => exact tail_row_holds hG hI hIc hρ
  | releaseUpper r h => exact releaseUpper_row_holds hI hIc he hρ
  | tailUpper r h => exact tailUpper_row_holds hI hIc he hρ
  | mean r => exact mean_row_holds hG hI hIc hρ
  | union r => exact union_row_holds hI hIc hρ
  | edgeLower r => exact edgeLower_row_holds hI hIc hρ
  | edgeUpper r => exact edgeUpper_row_holds hG hI hIc he hρ

/-- **Zhang's Theorem 2.1 reduced to the certificate layer alone**: if the no-recovery claims hold
on `P60` (Table 1), every forest with at most `60` vertices has a unimodal independence
sequence. -/
theorem finite60_of_certificates (hcert : Cert.CertificatesSound) (F : FiniteForest)
    (hn : F.n ≤ 60) : independenceSequenceUnimodal F :=
  finite60_of_sound rowsSound hcert F hn

end Rows
end Zhang
end Erdos993Lean
