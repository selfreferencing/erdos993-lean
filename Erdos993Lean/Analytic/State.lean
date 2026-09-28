import Erdos993Lean.Analytic.Glue30
import Erdos993Lean.Analytic.TailCert.Main
import Erdos993Lean.Analytic.Atlas.Main
import Erdos993Lean.Analytic.Reserve.Cert.Bands

/-!
# The state of the analytic route (optional library `Erdos993LeanAnalyticState`)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  With the finite part (kernel-checked, lane K),
the window and O6 (lane A5), the mixture (A1), T1 (A2), the large-mean no-valley theorem (F1, F2), O5 (A8)
and O3 (A10: the verified interval cell checker of the repaired T3 potential; 30 `native_decide` checks, one
per activity band) all proved, Erdős #993 rests on three inputs: O1, O2 for the certified profile, and the
O4 atlas numerics on `m < 400` (lane A9, now proved: `Atlas.explicitThreshold_small`), so
`erdos993_of_O1_O2` rests on O1 and O2 alone.

Trust: `native_decide` enters only through `TailCert.tailBound_profile30` (the 30 band checks
`TailCert.Checks.band_00` … `band_29`) and `Atlas.explicitThreshold_small` (the 60 band checks
`Atlas.Checks.checkL01` … `checkU30`); everything else uses `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.State

/-- **Erdős #993 from O1, O2 and the atlas numerics.** -/
theorem erdos993_of_O1_O2_atlas (h1 : VarianceBound Profile30.P) (h2 : VarianceRatioBound Profile30.P)
    (hsmall : ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m)) :
    Erdos993Statement :=
  Glue30.erdos993_of_profile30 h1 h2 TailCert.tailBound_profile30 hsmall

/-- **Sol's core-union family**: every forest of the family is unimodal, from the family O1/O2 and the
atlas numerics. -/
theorem coreUnion_unimodal_of_O1_O2_atlas
    (h1 : VarianceBoundOn CoreUnion Profile30.P) (h2 : VarianceRatioBoundOn CoreUnion Profile30.P)
    (hsmall : ∀ t, InRange t → ∀ m, Profile30.P.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (Profile30.P.θb t) (Profile30.P.Db t) (Profile30.P.Tb t m)
        (Profile30.P.M1b t m))
    (F : FiniteForest) (hF : CoreUnion F) : independenceSequenceUnimodal F :=
  Glue30.coreUnion_unimodal_of_profile30 h1 h2 TailCert.tailBound_profile30 hsmall F hF

/-- **Erdős #993 from O1 and O2 alone.** O3 (`TailCert.tailBound_profile30`, lane A10), O4's atlas on
`m < 400` (`Atlas.explicitThreshold_small`, lane A9), O4 on `m ≥ 400` (lanes F1, F2) and O5 (lane A8) are
all proved; the two hypotheses are the variance inputs for the certified profile. -/
theorem erdos993_of_O1_O2 (h1 : VarianceBound Profile30.P) (h2 : VarianceRatioBound Profile30.P) :
    Erdos993Statement :=
  erdos993_of_O1_O2_atlas h1 h2 Atlas.explicitThreshold_small

/-- **Sol's core-union family** from the family O1 and O2 alone. -/
theorem coreUnion_unimodal_of_O1_O2
    (h1 : VarianceBoundOn CoreUnion Profile30.P) (h2 : VarianceRatioBoundOn CoreUnion Profile30.P)
    (F : FiniteForest) (hF : CoreUnion F) : independenceSequenceUnimodal F :=
  coreUnion_unimodal_of_O1_O2_atlas h1 h2 Atlas.explicitThreshold_small F hF

/-- **Erdős #993 from the upper O1 box and O2.** O1 is proved for `Profile30.P` except the finite box of its upper
band (`Reserve.varianceBound_profile30_of_upperBox`: lanes A11–A14; the box is lane A15's checker). -/
theorem erdos993_of_upperBox_O2 (hU : Reserve.UpperBoxOK) (h2 : VarianceRatioBound Profile30.P) :
    Erdos993Statement :=
  erdos993_of_O1_O2 (Reserve.varianceBound_profile30_of_upperBox hU) h2

end Erdos993Lean.Analytic.State
