import Erdos993Lean.ZhangKernel.Sound
import Erdos993Lean.ZhangKernel.Checks.C02_20
import Erdos993Lean.ZhangKernel.Checks.C21_30
import Erdos993Lean.ZhangKernel.Checks.C31_39
import Erdos993Lean.ZhangKernel.Checks.C40
import Erdos993Lean.ZhangKernel.Checks.C41
import Erdos993Lean.ZhangKernel.Checks.C42
import Erdos993Lean.ZhangKernel.Checks.C43
import Erdos993Lean.ZhangKernel.Checks.C44
import Erdos993Lean.ZhangKernel.Checks.C45
import Erdos993Lean.ZhangKernel.Checks.C46
import Erdos993Lean.ZhangKernel.Checks.C47
import Erdos993Lean.ZhangKernel.Checks.C48
import Erdos993Lean.ZhangKernel.Checks.C49
import Erdos993Lean.ZhangKernel.Checks.C50
import Erdos993Lean.ZhangKernel.Checks.C51
import Erdos993Lean.ZhangKernel.Checks.C52
import Erdos993Lean.ZhangKernel.Checks.C53
import Erdos993Lean.ZhangKernel.Checks.C54
import Erdos993Lean.ZhangKernel.Checks.C55
import Erdos993Lean.ZhangKernel.Checks.C56
import Erdos993Lean.ZhangKernel.Checks.C57
import Erdos993Lean.ZhangKernel.Checks.C58
import Erdos993Lean.ZhangKernel.Checks.C59
import Erdos993Lean.ZhangKernel.Checks.C60
import Erdos993Lean.Zhang.Rows.Main

/-!
# T. Zhang's finite part checked by the Lean kernel (optional target `Erdos993LeanZhangKernel`)

**Theorems** (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`; see
`ZhangKernel/Audit.lean`).
* **`Erdos993Lean.Zhang.certificatesSound_kernel : Cert.CertificatesSound`**: the certificate layer
  of T. Zhang's finite part (*Exact Certificates for Unimodality of Forest Independence
  Polynomials*, v1.1, Table 1): on every triple `(n, a, k)` of the domain `P60` (35), no feasible
  array of the relaxation of Section 2.9 recovers after a nonpositive difference.  The same claim as
  `Zhang.certificatesSound` (`ZhangCert/Main.lean`), without its `native_decide`.
* **`Erdos993Lean.Zhang.forest_unimodal_of_card_le_sixty_kernel`**: every forest with at most 60
  vertices has a unimodal independence sequence (`Zhang.Rows.finite60_of_certificates`).

**Method.**  The check of `ZhangCert/Checks.lean` (`native_decide` on `ZhangCertX.checkRange 2 60`)
cannot be evaluated by the kernel as it stands: its data are strings, and in Lean 4.28 the kernel
cannot reduce `String.foldl` (measured: `decide +kernel` fails at once on `ZhangCertX.tokens ""`).
Here the same certificates, decoded and normalized by the package's own functions
(`ZhangCertX.parseEntries`, `ZhangCertX.linearToGeneric`, `ZhangCertX.directOK`; generator
`scratch/gen_all.lean` of lane K), are stored as Lean terms (`ZhangKernel/Data/`), one list of check
items per `(n, a)`, and checked by a kernel-friendly checker (`ZhangKernel/Core.lean`): one
`decide +kernel` per `(n, a)` (`ZhangKernel/Checks/`), collected per order by rewriting
(`order_n`).  The soundness proof holds for arbitrary items: a passing kernel check implies the
package's `ZhangCertX.genericOK` (`genericOK_of_genericOKV`, `genericOK_of_directV`), whose soundness
is `ZhangCertX.genericOK_sound` (`ZhangCert/Bridge.lean`); `checkOrderV_sound` then covers `P60`.

**Build.**  Build the modules one at a time, by name (`lake build Erdos993Lean.ZhangKernel.Main`
builds the check modules in parallel, which needs memory); timings and memory are recorded in
`ProofRuns/2026-09-28_analytic_large_n/LEAN/lanes/K/NOTES.md`.
-/

namespace Erdos993Lean

namespace Zhang

/-- **The certificate layer of Zhang's finite part, checked by the kernel**: no feasible array of
the relaxation recovers after a nonpositive difference, on every triple of `P60`.  From the kernel
checks `ZhangKernel.order_n` (`decide +kernel`, no `native_decide`) and `checkOrderV_sound`. -/
theorem certificatesSound_kernel : Cert.CertificatesSound := by
  intro n a k hP
  obtain ⟨hn2, hn60, h2a, han, hk1, hk⟩ := hP
  interval_cases n
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_2 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_3 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_4 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_5 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_6 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_7 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_8 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_9 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_10 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_11 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_12 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_13 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_14 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_15 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_16 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_17 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_18 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_19 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_20 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_21 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_22 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_23 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_24 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_25 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_26 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_27 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_28 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_29 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_30 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_31 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_32 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_33 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_34 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_35 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_36 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_37 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_38 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_39 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_40 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_41 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_42 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_43 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_44 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_45 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_46 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_47 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_48 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_49 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_50 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_51 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_52 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_53 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_54 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_55 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_56 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_57 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_58 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_59 a (by omega) (by omega) k hk1 hk
  · exact ZhangKernel.checkOrderV_sound ZhangKernel.order_60 a (by omega) (by omega) k hk1 hk

/-- **Every forest with at most 60 vertices has a unimodal independence sequence**, with the
certificate layer checked by the kernel (standard axioms only). -/
theorem forest_unimodal_of_card_le_sixty_kernel (F : FiniteForest) (hn : F.n ≤ 60) :
    independenceSequenceUnimodal F :=
  Rows.finite60_of_certificates certificatesSound_kernel F hn

end Zhang

end Erdos993Lean
