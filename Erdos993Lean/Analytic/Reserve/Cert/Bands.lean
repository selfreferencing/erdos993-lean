import Erdos993Lean.Analytic.Reserve.Cert.Main
import Erdos993Lean.Analytic.Reserve.Assembly
import Erdos993Lean.Analytic.Reserve.Tail
import Erdos993Lean.Analytic.Reserve.Entropy
import Erdos993Lean.Analytic.Reserve.O1Profile30

/-!
# O1 on `[1/3, 8/5]` in Lean (optional library `Erdos993LeanReserveCert`)

Campaign `ProofRuns/2026-09-28_analytic_large_n` (Lean lead).  The sharp O1 bound `Var M ≤ D m` for every forest,
every activity of the four closed bands `[1/3, 3/5]` (D = 8/5), `[3/5, 4/5]` (7/5), `[4/5, 13/10]` (6/5),
`[13/10, 8/5]` (7/5) and every maximum-weight independent set: lane A11's induction (`bandVar_bandK`), lane A13's
entropy facts and tails (`entropyOK`, `tailOK_bandK`), lane A12's box and leaf checks (`Cert.boxOK_bandK`,
`Cert.leafOK_bandK`).  Trust: the four `native_decide` box checks `Cert.Checks.box_0 … box_3`; everything else
standard axioms.
-/

namespace Erdos993Lean.Analytic.Reserve

/-- **O1 on `[1/3, 3/5]`**, `D = 8/5`. -/
theorem bandVar_band0_proved : BandVar band0 :=
  bandVar_band0 entropyOK Cert.boxOK_band0 tailOK_band0 Cert.leafOK_band0
/-- **O1 on `[3/5, 4/5]`**, `D = 7/5`. -/
theorem bandVar_band1_proved : BandVar band1 :=
  bandVar_band1 entropyOK Cert.boxOK_band1 tailOK_band1 Cert.leafOK_band1
/-- **O1 on `[4/5, 13/10]`**, `D = 6/5`. -/
theorem bandVar_band2_proved : BandVar band2 :=
  bandVar_band2 entropyOK Cert.boxOK_band2 tailOK_band2 Cert.leafOK_band2
/-- **O1 on `[13/10, 8/5]`**, `D = 7/5`. -/
theorem bandVar_band3_proved : BandVar band3 :=
  bandVar_band3 entropyOK Cert.boxOK_band3 tailOK_band3 Cert.leafOK_band3

/-- **O1 for the certified profile from the upper band's finite box alone**: the four lower bands are proved
(`Cert.boxOK_bandK`, `Cert.leafOK_bandK`), the upper band's tails, leaf base and glue are proved (lane A14), so
`VarianceBound Profile30.P` rests only on `UpperBoxOK` (lane A15). -/
theorem varianceBound_profile30_of_upperBox (hU : UpperBoxOK) : VarianceBound Profile30.P :=
  varianceBound_profile30_of_boxes Cert.boxOK_band0 Cert.boxOK_band1 Cert.boxOK_band2 Cert.boxOK_band3
    Cert.leafOK_band0 Cert.leafOK_band1 Cert.leafOK_band2 Cert.leafOK_band3 hU

end Erdos993Lean.Analytic.Reserve
