import Erdos993Lean.Analytic.Reserve.UpperCert.Main
import Erdos993Lean.Analytic.State

/-!
# O1 for the certified profile, and Erdős #993 from O2 alone (lane A15, optional target)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A15.  The upper band's finite box `UpperBoxOK` is proved
(`UpperCert.upperBoxOK`, `Erdos993Lean/Analytic/Reserve/UpperCert/Main.lean`), so the two consumers of the lead's state
file discharge it:

* **`varianceBound_profile30 : VarianceBound Profile30.P`** (O1 for the certified profile):
  `Reserve.varianceBound_profile30_of_upperBox upperBoxOK` (lanes A11–A14, `Reserve/Cert/Bands.lean`);
* **`erdos993_of_O2`**: Erdős #993 from O2 (`VarianceRatioBound Profile30.P`) alone:
  `State.erdos993_of_upperBox_O2 upperBoxOK` (`Erdos993Lean/Analytic/State.lean`).

Trust: the `native_decide` checks inherited from the imports — the 9 piece checks of this lane
(`UpperCert.Checks.piece_0` … `piece_8`), lane A12's 4 box checks (`Cert.Checks.box_0` … `box_3`), and, for
`erdos993_of_O2`, lane A10's 30 band checks of O3 and lane A9's 60 atlas checks; everything else uses `propext`,
`Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.Reserve.UpperCert

open Erdos993Lean.Analytic

/-- **O1 for the certified profile**: `Var M ≤ D(λ) m` for every forest with `n ≥ 61`, every activity in range at an
interior rank and every maximum-weight independent set (the four lower bands by lane A12's boxes, the upper band by
this lane's box). -/
theorem varianceBound_profile30 : VarianceBound Profile30.P :=
  Reserve.varianceBound_profile30_of_upperBox upperBoxOK

/-- **Erdős #993 from O2 alone** (the variance-ratio bound for the certified profile). -/
theorem erdos993_of_O2 (h2 : VarianceRatioBound Profile30.P) : Erdos993Statement :=
  State.erdos993_of_upperBox_O2 upperBoxOK h2

end Erdos993Lean.Analytic.Reserve.UpperCert
