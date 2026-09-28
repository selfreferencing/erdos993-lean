import Erdos993Lean.ZhangKernel.Main

/-! Axiom audit for the OPTIONAL kernel-checked Zhang target (`Erdos993LeanZhangKernel`), run with
`lake env lean Erdos993Lean/ZhangKernel/Audit.lean` after building `Erdos993Lean.ZhangKernel.Main`.
Expected: `[propext, Classical.choice, Quot.sound]` (or a subset) on every line; in particular no
`Lean.ofReduceBool` and no `Lean.trustCompiler`. -/

#print axioms Erdos993Lean.Zhang.certificatesSound_kernel
#print axioms Erdos993Lean.Zhang.forest_unimodal_of_card_le_sixty_kernel
-- the kernel checks
#print axioms Erdos993Lean.ZhangKernel.order_60
#print axioms Erdos993Lean.ZhangKernel.check_60_40
#print axioms Erdos993Lean.ZhangKernel.bRowCheck_eq
#print axioms Erdos993Lean.ZhangKernel.tabCheck_eq
-- the soundness chain
#print axioms Erdos993Lean.ZhangKernel.checkOrderV_sound
#print axioms Erdos993Lean.ZhangKernel.checkAV_sound
#print axioms Erdos993Lean.ZhangKernel.genericOK_of_genericOKV
#print axioms Erdos993Lean.ZhangKernel.genericOK_of_directV
#print axioms Erdos993Lean.ZhangKernel.coefK_eq
#print axioms Erdos993Lean.ZhangKernel.chooseK_eq
