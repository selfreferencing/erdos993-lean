import Erdos993Lean.FormalConjectures.Erdos993

/-! Prints the axioms of `Erdos993.erdos_993`, the statement of Erdős Problem #993 in google-deepmind/formal-conjectures
(pull request #4192, copied verbatim), proved from `Erdos993Lean.Analytic.erdos993`, and of the four bridge lemmas.
Run: `lake build Erdos993LeanFormalConjectures`, then `lake env lean Audit/AxiomsFormalConjectures.lean`. -/

#check (Erdos993.erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  G.IsTree → Erdos993.UnimodalSeq (Erdos993.indepSeq G))
#print axioms Erdos993.erdos_993
#print axioms Erdos993Lean.Analytic.erdos993

-- The bridge lemmas on their own (standard axioms only).
#print axioms Erdos993Lean.FormalConjecturesBridge.unimodal_of_unimodalUpTo_of_zero
#print axioms Erdos993Lean.FormalConjecturesBridge.isIndepSet_map_iff
#print axioms Erdos993Lean.FormalConjecturesBridge.count_eq
#print axioms Erdos993Lean.FormalConjecturesBridge.count_eq_zero_of_indepNum_lt
