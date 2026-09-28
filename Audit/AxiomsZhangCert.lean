import Erdos993Lean.ZhangCert.Final

/-! Axiom audit for the OPTIONAL Zhang certificate target (`lake build Erdos993LeanZhangCert`), run
with `lake env lean Erdos993Lean/ZhangCert/Audit.lean` after that build.
Expected: `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]` for the
first three lines (the single `native_decide`, `ZhangCertX.checkRange_2_60`), and
`[propext, Classical.choice, Quot.sound]` (or a subset) for the others. -/

#print axioms Erdos993Lean.Zhang.certificatesSound
#print axioms Erdos993Lean.Zhang.finite60_of_rows
#print axioms Erdos993Lean.ZhangCertX.checkRange_2_60
-- the bridge (standard axioms only)
#print axioms Erdos993Lean.ZhangCertX.checkRange_sound
#print axioms Erdos993Lean.ZhangCertX.checkN_sound
#print axioms Erdos993Lean.ZhangCertX.tripleOK_sound
#print axioms Erdos993Lean.ZhangCertX.genericOK_sound
#print axioms Erdos993Lean.ZhangCertX.coefZ_cast
#print axioms Erdos993Lean.ZhangCertX.rhsZ_cast
#print axioms Erdos993Lean.ZhangCertX.toRow_holds
#print axioms Erdos993Lean.ZhangCertX.aggRow_holds
#print axioms Erdos993Lean.ZhangCertX.binomN_eq
#print axioms Erdos993Lean.ZhangCertX.binomZ_cast
-- the reduction it feeds (Zhang/Finite60.lean)
#print axioms Erdos993Lean.Zhang.finite60_of_sound
-- the theorem
#print axioms Erdos993Lean.Zhang.forest_unimodal_of_card_le_sixty
