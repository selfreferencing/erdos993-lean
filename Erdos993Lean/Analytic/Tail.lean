import Erdos993Lean.Analytic.Tail.Weighted
import Erdos993Lean.Analytic.Tail.Rooted
import Erdos993Lean.Analytic.Tail.LemmaA
import Erdos993Lean.Analytic.Tail.Marginal
import Erdos993Lean.Analytic.Tail.Scalar
import Erdos993Lean.Analytic.Tail.Fallback
import Erdos993Lean.Analytic.Tail.LemmaB
import Erdos993Lean.Analytic.Tail.LemmaC
import Erdos993Lean.Analytic.Tail.Boundary
import Erdos993Lean.Analytic.Tail.Unit
import Erdos993Lean.Analytic.Tail.Reduction
import Erdos993Lean.Analytic.Tail.PerUnit
import Erdos993Lean.Analytic.Tail.Laplace
import Erdos993Lean.Analytic.Tail.Weight
import Erdos993Lean.Analytic.Tail.Markov

/-!
# The tail input T3 (lane A3): design

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A3.  Sources: the report
`ProofRuns/2026-09-27_zhang_review/reports/T23.md` §1, §3 (Lemmas A, B, C; Theorems T3-1, T3-2),
Soul's audit `SOUL/RESULTS/O3.md` (the surviving fallback rate), Zhang (45)–(46).

## What is formalized

T3 bounds the Laplace transform of the free count `M` of the conditional binomial mixture
`forestMixture F B λ` (Defs.lean): for an independent set `B`, `C = Bᶜ`, `q = λ/(1+λ)` and
`0 ≤ z ≤ 1`, `E(1 − q + q z)^M = E z^{K_B}`, `K_B = |S ∩ B|` for the hard-core set `S`.  The
consumer is O3 (`TailBound`) through Markov's inequality.

## Representation of the rooted structure

* Everything lives in one ambient acyclic graph `G` on `V`, as functions of a vertex *subset* `s`
  (the convention of `IndependencePoly.lean` and `Floor/TreeDecomp.lean`).
* `Zw G wt s = ∑_{I ⊆ s independent} ∏_{v ∈ I} wt v` (`Tail/Weighted.lean`): uniform weight `λ`
  gives `Z(s)`; weight `λ` on `C` and `λ z` on `B` gives the numerator of `E z^{K_B}`.
* A rooted tree is a pair `(s, r)` with `ConnectedIn G s`, `r ∈ s`; its children are
  `nbrsIn G s r` and the subtree of the child `w` is the branch `compIn G (s.erase r) w`
  (`erase_eq_biUnion`, `outsideClosedNbhd_eq_biUnion`).  Quantities attached to every vertex are
  defined by well-founded recursion on `s.card` through `treeSum` / `treeProd`
  (`Tail/Rooted.lean`); proofs go by `rooted_induction`.
* The downward probability of T23 is `rootProb G λ s r = λ Z(s − N[r]) / Z(s)` (the root marginal
  of the subtree alone); `rootProb_odds` is the recursion `R_r = λ ∏_w (1 − p_w)`.
* Components of `G[s]` are peeled off one at a time (`compIn G s x` has no edges to the rest), so
  forest statements follow from tree statements by strong induction on `s.card`.

## Headline results (all sorry-free; axioms `propext`, `Classical.choice`, `Quot.sound`)

* Lemma A (`Tail/LemmaA.lean`): `lemmaA_tree`, `phiF_le_toy`, `lemmaA_forest` (every `z ∈ [0, 1]`).
* Lemma B (`Tail/LemmaB.lean`): `lemmaB_tree`, `lemmaB_component`, `rmin_le_child`, `mSum_le_max`.
* Lemma C (`Tail/LemmaC.lean`): `lemmaC_exact`, `lemmaC_ineq`, `lemmaC_tree`.
* Soul's fallback (`Tail/Fallback.lean`, `Tail/Weight.lean`): `laplace_fallback_mixture` —
  `E(1 − q + q z)^M ≤ exp(−q(1 − q) r(λ, z) m)` for every forest and every independent `B`
  (no hypotheses); `laplace_fallback_hardcore` (hard-core form).
* The Laplace identity and `q m = W` (`Tail/Laplace.lean`, `Tail/Weight.lean`): `laplaceIdentity`,
  `weightIdentity` (they discharge the named propositions `LaplaceIdentity`, `WeightIdentity`).
* Theorem T3-2, repaired (`Tail/Boundary.lean`, `Tail/Unit.lean`, `Tail/Reduction.lean`):
  `boundary_lemma` (the `Y_B = 0` boundary, proved), `t3_reduction_mixture` — conditional only on
  the named numerical proposition `T3UNonneg λ z a ℓ` (the domain `Y_B > 0`), for `B` with the
  `LeafCondition`, `0 < λ ≤ 6`, `a ≥ 0`, `ℓ ≤ log((1 + λ)/(1 + λ z))`.
* Theorem T3-1, per-unit form (`Tail/PerUnit.lean`): `t31_reduction_mixture` — conditional only on
  the one-variable named proposition `PerUnitRate λ z ℓ` (no leaf condition).
* The consumer form (`Tail/Markov.lean`): `tail_fallback` (unconditional), `tail_t3`, `tail_t31`:
  `P(M ≤ j) ≤ exp(−ℓ m) ((1 + λ)/(1 + λ z))^j`.
-/
