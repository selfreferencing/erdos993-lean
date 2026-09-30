> Paths such as `ASTRA/...`, `SOUL/...` and `LEAN/...` below refer to files in our campaign archive. The proof documents, certificates, checkers and review reports they name are available on request. The Lean files are in this repository.

# Unimodality of forest independence sequences: an analytic proof for forests with at least 61 vertices

## 0. Summary

**Theorem (Erdős Problem #993).** For every finite forest F, the independence sequence i_0(F), i_1(F), …, i_α(F) is
unimodal.

The proof has two parts.

- **n ≤ 60.** This is your finite-order theorem, *Exact Certificates for Unimodality of Forest Independence
  Polynomials* (v1.1, Proposition 1.2).
  - It is formalized in Lean 4 with Mathlib: König for forests, the decomposition, the eleven inequality families, the
    reduction, and all 17,100 certificates.
  - The certificates are checked two ways. The first is a Lean checker whose soundness is proved, run with one
    `native_decide`. The second is the Lean kernel itself: 900 `decide +kernel` slices, standard axioms only.
- **n ≥ 61.** An analytic argument built on your conditional binomial mixture over a maximum-weight independent set.
  - It replaces the stage certificates 59 → 900 by five analytic inputs (O1–O5), an activity window (O6), an explicit
    no-valley lemma, a small-mean atlas and a large-mean Fourier theorem.
  - All six inputs O1–O6 have been adopted by the campaign's referee (O2 at 15:23 EDT today), so the argument is
    complete on paper. The referee is an AI agent (the Claude session that ran this campaign), not a person; no
    human referee has checked the argument.
  - Several inputs are computer-assisted, and each certificate family was checked differently (§5). The O1 and O2
    certificates were replayed in full by independent code with different interval arithmetic. The O1, O3 and O4
    certificates are checked in Lean by checkers whose soundness is proved; for O3 and O4 these Lean checkers are the
    only independent check of the cells. The O2 certificates are checked in Lean too, so the whole theorem is now
    proved in Lean (§6).

**Status.**

| Component | On paper | Refereed | In Lean |
|---|---|---|---|
| n ≤ 60 (your finite part) | ✓ | ✓ (our 2026-09-27 review: every lemma checked; all 17,100 certificates re-verified by an independent exact checker) | ✓ (kernel-checked, standard axioms) |
| Mixture identities, window (O6), no-valley lemma, large-mean theorem | ✓ | ✓ | ✓ |
| O3 lower tail of M | ✓ | ✓ | ✓ |
| O4 small-mean atlas | ✓ | ✓ | ✓ |
| O5 floor on E M | ✓ | ✓ | ✓ |
| O1 Var M ≤ D m | ✓ all five bands | ✓ | ✓ all five bands |
| O2 Var K ≤ (1+θ)(1−q)W | ✓ all of [1/3, 7/3] (14 certificate rows) | ✓ (adopted 15:23 EDT) | ✓ all 14 rows |

The whole theorem is proved in Lean with no hypotheses: `Erdos993Lean.Analytic.erdos993 : Erdos993Statement`. Its trust
base is the standard axioms plus `Lean.ofReduceBool` and `Lean.trustCompiler`, which enter only through the 271
`native_decide` certificate evaluations of the analytic route (§6).

## 1. Setup: your mixture

Fix a forest F on n vertices and an activity λ > 0.
- The hard-core measure weights an independent set S by λ^{|S|}.
- K = |S|, with mean μ(λ) and variance V.
- π_v = P(v ∈ S) and q = λ/(1+λ).

Let B be an independent set of maximum weight W = Σ_{b ∈ B} π_b; every maximizer is allowed, ties included. Put
C = V(F) \ B and J = S ∩ C. Condition on J:
- Y = |J|;
- M = #{b ∈ B : b has no neighbour in J} is the free count.

Conditionally on J, the selected count |S ∩ B| is Binomial(M, q), so

- K = Y + Bin(M, q), and qm = W, where m = E M.
- At an activity with μ(λ) = k an integer, δ := k − Y − qM satisfies E δ = 0 and E δ² = V − (1−q)W.
- Var(K_B) = (1−q)W + q² Var M, where K_B = |S ∩ B|.

These are formalized in Lean (`forestMixture`, `MixtureFacts`, `forestMixture_var_delta_le`,
`forestMixture_varM`).

## 2. Reduction to interior ranks (O6)

Let L = ⌈n/4⌉ and let ν be the maximum size of a matching in F. The matching skeleton polynomial

    β(x) = (1 + 2x)^ν (1 + x)^{n−2ν}

is the independence polynomial of the graph that keeps only the ν edges of a maximum matching. Let h_β be its first
mode (the Lean code calls it `hB`); it has nothing to do with the maximizing set B of §1.
- The prefix i_0 ≤ … ≤ i_L rises (your Input E, in Lean).
- The tail beyond h_β falls, by comparison with β (in Lean).
- So only ranks L < k < h_β need a no-valley argument.

For such k:

    μ(1/3) ≤ n/4 ≤ L < k ≤ h_β − 1 < n/2 − ν/3 ≤ μ(7/3).

Three bounds, all proved in Lean, give this chain:
- B2: μ(1/3) ≤ n/4;
- B7: h_β ≤ ⌈n/2 − ν/3⌉ = ⌈(3n − 2ν)/6⌉, so h_β − 1 < n/2 − ν/3;
- B5, the occupation bound at λ = 7/3: μ(7/3) ≥ n/2 − ν/3.

The chain goes through h_β − 1 because h_β itself can equal n/2 − ν/3: for the edgeless forest on 62 vertices both
are 31. Hence k = μ(λ) for some λ ∈ (1/3, 7/3), and it suffices to exclude a weak valley of (P(K = j))_j at j = k for
λ in the window [1/3, 7/3]. Your Lemma 3.2 (the activity-2 mean bound) is not needed.

## 3. The no-valley criterion (O4)

At integer mean k, a weak valley at k contradicts

    (λ + λ⁻¹) P(K = k) > P(K = k − 1) + P(K = k + 1),

and the mixture gives these probabilities as E b_M(k − Y) with binomial rows b_M. The criterion is an explicit
threshold lemma ("T1") for mixtures of binomials. It needs four inputs about the law of (M, δ).

The activity window is cut into 30 bands, and each band has fixed targets (the profile):

| λ | D (O1) | θ (O2) |
|---|---|---|
| [1/3, 3/5] | 8/5 | 1 |
| (3/5, 4/5] | 7/5 | 7/10 |
| (4/5, 13/10] | 6/5 | 3/5 |
| (13/10, 8/5] | 7/5 | 7/10 |
| (8/5, 7/3] | 8/5 | 1 |

The four inputs are:
- **(O1)** Var M ≤ D m;
- **(O2)** E δ² ≤ θ q(1−q) m, equivalently V ≤ (1+θ)(1−q)W;
- **(O3)** lower-tail bounds P(M ≤ r) ≤ T(m, r) for every integer r < M₁(λ, m) = ⌈m⌉ + 1 (the cutoff in the Lean
  interface `TailBound`);
- **(O5)** a floor m ≥ m_floor(band).

Given these, the no-valley inequality holds for every m ≥ m_floor:
- **m < 400:** a certified atlas of rational dual boxes. For m ≤ 50 there are 1,502 boxes and 3,716,121 integer-state
  checks; for 50–400 there are 215 boxes and 3,181,289 checks.
- **m ≥ 400:** a Fourier theorem. It uses explicit estimates for the binomial characteristic function and the local
  curvature of b_M, and needs only D ≤ 8/5, θ ≤ 7/10 in the centre (θ ≤ 1 outside) and the tail P(M < m/3) ≤ e^{−m/30}.

Both the atlas and the Fourier theorem are proved in Lean. The atlas is checked by an exact rational checker with 60
`native_decide` band checks; its soundness is proved on standard axioms.

## 4. The inputs

### O5: the floor on E M

A tree induction gives affine lower bounds μ_F(x) ≥ r_x n + h_x at 106 rational activities. These are the density
records of your stage 80, re-checked, with 11,130 branch cases. They are transferred across activities and combined
with the integer rank k > n/4, W ≥ μ/2 and m = W/q. This gives explicit floors m_floor for all n ≥ 61. It is in Lean,
using the records at x = 1 and x = 11/10.

### O3: the lower tail of M

The Laplace identity E(1 − q + qt)^M = E t^{K_B} holds, and E(1−q)^M = Z_F[C]/Z_F. A repaired potential induction
with k = a·r(λ) bounds the transform on 30 bands × 5 tilts t ∈ {0, 1/20, 1/10, 1/5, 3/10}. The certified cells come to
18.7 M in Sol's original cover (Arb intervals) and 277,664 in the Lean checker's own cover, with an analytic boundary
case. It is in Lean: `TailBound Profile30.P`, with 30 `native_decide` band checks.

### O1: Var M ≤ D m — the two-generation reserve

The bound holds for every forest, every λ in a band and every independent B containing every leaf whose neighbour has
degree ≥ 2, which includes every maximizer.

**Proof outline.** Attached, all in `ASTRA/O1/`: `FULL_PROFILE30_O1_ASSEMBLY.md` (the assembly of the five bands);
`SHARP_FIRST_FOUR_ASSEMBLY.md` for the four lower bands, with `LOWER_SHARP_ALTERNATE_PROOF.md` ([1/3, 3/5]) and
`SHARP_FIRST_FOUR_RESERVE_PROOF.md` (the next three); `UPPER_SHARP_SIGNED_PORT_PROOF.md` for [8/5, 7/3]; and
`TWO_GENERATION_RESERVE_PROOF.md` (the method, and the universal fallback D = 2 on [1/3, 7/3]).

**The objects.** Root every component that meets B and has a vertex outside B at a vertex outside B. A component inside
B is a single vertex (B is independent), and a component disjoint from B contributes nothing. Then every vertex
without children lies in B, which the induction below needs. With an arbitrary root the invariant can fail: a single
edge rooted at its endpoint in B has a child outside B with F = 0 < α y. This is the rooting of the Lean proof
(`varB_le_of_component` and `good_of_component` in `Erdos993Lean/Analytic/Reserve/Assembly.lean`).
For the subtree at v, let U⁰, V⁰ be the mean and variance of its B-selected
count (the number of vertices of S ∩ B in the subtree: its share of K_B, not of the total count K) when the parent of v
is unoccupied, and U¹, V¹ the same when the parent is occupied. Put a = 1_B(v), A = 1 + (D−1)q, F = A U⁰ − V⁰,
G = A U¹ − V¹ = Σ_child F, u = U⁰ − U¹ and y = −log(1 − p), where p is the downward message (the probability that v is
occupied when its parent is not). The law of total variance gives

    F = A p a + (1−p) Σ F_i + p Σ G_i − p(1−p)(a − Σ u_i)²,   u = p(a − Σ u_i).

**The reserve.** The invariant is F ≥ α y + β u + γ u²/y, with band coefficients:

| Band | D | α | β | γ |
|---|---|---|---|---|
| [1/3, 3/5] | 8/5 | q/2 | 0 | λ(3+λ)/11 |
| [3/5, 4/5] | 7/5 | 23q/50 | 0 | λ(3+λ)/13 |
| [4/5, 13/10] | 6/5 | 23q/50 | 0 | λ(3+λ)/13 |
| [13/10, 8/5] | 7/5 | 23q/50 | 0 | λ(3+λ)/13 |
| [8/5, 7/3] | 8/5 | q/2 | (λ−1)/27 | 31λ/100 |

**The induction step.** Take a parent with message p whose children have messages p_i and log-masses
y_i = −log(1 − p_i). Write Y = Σ_i y_i for the parent's child log-mass and y₀ = −log(1 − p), so that
p = λe^{−Y}/(1 + λe^{−Y}). For one child with message s, write y = −log(1 − s) and let T be the sum of the log-masses of
its own children (the grandchildren), so that s = λe^{−T}/(1 + λe^{−T}) and Y ≥ y. (T, Y and the E below are local to
O1: they are not the tail function T(m, r) of §3, the count Y = |J| of §1, or an expectation.) For the child, the
hypothesis gives F_child ≥ αy + βu + γu²/y and, applied to the grandchildren with Cauchy–Schwarz,
G_child ≥ αT + β(a − u/s) + γ(a − u/s)²/T, where u and a are the child's. Use (Σ_i u_i)² ≤ Y Σ_i u_i²/y_i, allocate in
proportions y_i/Y, and complete the square in each signed u. The step then reduces to three comparisons in (λ, T, Y):
- Z > 0, together with CC ≥ 0 (unselected parent and child);
- CB ≥ 0 (unselected parent, selected child);
- BC ≥ 0 (selected parent, unselected child).

A selected–selected pair never occurs, by independence.

The comparisons CC and BC contain the entropy term E = 1 − p + pT/y − y₀/Y. With Δ_O1 = s − p (not the δ = k − Y − qM
of §1), the exact identity E·y = KL(Ber p ‖ Ber s) + (Y − y)(p + y₀/Y), binary Pinsker KL ≥ 2Δ_O1² and Y ≥ y give
E ≥ 2Δ_O1²/y ≥ 0.

**The cover.**
- **Finite box** (T ≤ 6, Y ≤ 4): outward-interval certificates, 1,023,895 cells over the five bands.
- **Complement:** analytic tails.
- **Base:** the selected leaf (F = Dq², u = q).
- **Root:** PSD, β² ≤ 4αγ.

**Refereeing.** A recomputation checked:
- the theorem exactly, on about 179,000 (tree, λ, B) cases, with every maximizer plus random leaf-containing sets;
- the invariant, at about 4.8 M vertex records.

Four independent reviews followed, two of the written proofs and two full replays of the cells:
- the proof review of the four lower bands and of the universal bound D = 2 (`REVIEW_ASTRA_O1_PROOF.md`): every step
  checked, the square completion re-derived symbolically, and all 73 rational tail claims checked in exact arithmetic;
- the proof review of the upper band's signed step, with β ≠ 0 (`REVIEW_ASTRA_O1_UPPER_PROOF.md`): the algebra
  re-derived independently, 46 exact tail claims, the leaf base and the PSD condition;
- the replay of every cell of the four lower bands (`REVIEW_ASTRA_O1_REPLAY.md`), with the reviewer's own code and
  mpmath interval arithmetic instead of Astra's Arb, and again with a second, lemma-free evaluator;
- the replay of all 617,294 upper-band cells (`REVIEW_ASTRA_O1_UPPER_REPLAY.md`), with the reviewer's own code, plus a
  second integer-arithmetic engine on 65,085 of them, the tightest included.

**In Lean:** all five bands are proved from the certificates (`VarianceBound Profile30.P`).

### O2: Var K ≤ (1+θ)(1−q)W — the correlated-innovation payment

**Proof outline.** Attached: `SOUL/O2_FINAL/ASSEMBLY/PRO_R2_PROOF.md`, `O2_FULL_ASSEMBLY_DRAFT.md`,
`GLOBAL_O2_FINITE_BALANCE_AND_COVER.md` and `REFINED_SELECTOR_PRODUCER.md` (same folder), and the certificate
inventories (`SOUL/O2_FINAL/R2_PACKET/CERTIFICATES.json` for Pro R2's six rows,
`LEAN/o2_gaps/GAP_CERTIFICATE_INVENTORY.json` for the eight new rows).

**The objects.**
- Innovation identity: V = Σ_v π_v (1 − p_v) z_v², where z_v = 1 − Σ_child p_u z_u is the total-count response.
- A competing random independent set Γ, built on the original forest, with P(v ∈ Γ) = a′_v. Since B is a maximizer,
  E[Σ_{v ∈ Γ} π_v] ≤ W, and a cavity source satisfies g(p, r) ≤ a′_v.

**The balance identity.** With price c = (1+θ)/(1+λ) and band coefficient tables u, v, s, τ, w, ℓ (functions of the
parent cavity probability):

    cW − V = c·E[W − score(Γ)] + c Σ π(a′ − g) + Σ p Φ
             + three Cauchy remainders (explicit sums of squares) + packed child-mass slack + root log credit.

Every term except Σ p Φ is nonnegative by construction. The local payment Φ ≥ 0 is certified on the whole physical
domain: every real signed response, an analytic small-p tail, and a separate leaf endpoint.

**Status: adopted by the campaign's AI referee at 15:23 EDT today.** The basis:
- *Written proof.* An independent review found it correct, with no gap: the innovation identity, Γ, the eight-term
  identity (symbolically, and exactly on small forests and on a selected corpus of 49 actual forests up to 60
  vertices), domain membership, the tail and leaf constants, and the band bookkeeping. Its scope was Pro R2's six rows,
  the ones certified at the time, which cover [1/3, 3/5] ∪ [4/5, 8/5]. For the eight new rows the same argument is
  machine-checked: the Lean reduction below is proved for all 14 coefficient tables and needs from each row only its
  local payment and leaf endpoint, which the independent replay certified.
- *Certificates.* The cover of [1/3, 7/3] has 14 rows. Six are Pro R2's: low on [1/3, 3/5], central_0–3 on
  [4/5, 13/10] and upper_shoulder on [13/10, 8/5]. Eight are new and close the two former gaps, in R2's format and on
  R2's domain: L1, L23 and L4e on [3/5, 4/5] (γ = 17/10, θ = 7/10) and H1, H2b, H3b, H4b and H8 on [8/5, 7/3]
  (γ = 2, θ = 1). R2's rows were replayed with a copy of R2's checker; the new rows were generated and replayed with
  R2's unmodified engine and checker.
- *Independent replay.* A separate review agent replayed all 84,156 cells of the 14 rows with its own code and its own
  128-bit outward-rounded interval arithmetic: 0 failures, every cover complete, the small-message tail and the leaf
  endpoint re-verified, and the whole window covered with no gap. It found the central band thin: a dense float sample
  puts the minimum of Φ at about 3.3 × 10⁻⁴ near λ ≈ 1.298 (certified ≥ 2.5 × 10⁻⁴ there), and the check fails in that
  cell if γ is lowered by 0.5%.
- *Recomputation.* Before adopting, the referee re-tallied the replay's cell records, recomputed the SHA-256 of all 14
  certificates against the inventories, and ran an exact check with the 14 tables on 2,205 forest/activity cases from
  the same 49-forest corpus: no failure of the innovation identity, the eight-term identity, domain membership or
  Φ ≥ 0.
- *Lean.* Proved. `varianceRatioBound_profile30_of_certs` derives `VarianceRatioBound Profile30.P` from the certified
  local payment (`LocalPaymentOK`) and the leaf endpoint (`LeafOK`) of the 14 rows. A verified checker proves both for
  every row (`localPaymentOK_all`, `leafOK_all`): 168 root-box checks evaluated by `native_decide`, with soundness on
  the standard axioms, and the rows' tables proved equal to the ones in the statement.

**Finite evidence.** The caps hold with room on all 205,004 trees through 18 vertices at 10 activities, and on 1,476
larger families. In an exact recompute on 698 trees at 35 activities, the worst realized θ is 0.60 against 1 on
[1/3, 3/5], 0.45 against 0.7, 0.38 against 0.6 in the centre, 0.28 against 0.7, and 0.31 against 1.

## 5. Verification of the computer-assisted parts

| Certificate family | Size | Independent replay | Referee | Lean |
|---|---|---|---|---|
| Your 17,100 finite-part certificates | 49 data strings | ✓ all 17,100 triples and all 1,907 LP certificates by our independent exact checker (2026-09-27 review); also your checkers and our Lean checker | ✓ verified (2026-09-27 review) | ✓ `native_decide` and ✓ kernel |
| O4 atlas | 1,717 dual boxes, 6.9 M integer states | Only by the Lean checker (exact rational arithmetic); the review checked the box theorem, not each box | ✓ adopted | ✓ 60 checks |
| O3 tail cells | 150 band × tilt pairs | Only by the Lean checker, on its own cover of 277,664 cells; Sol's 18.7 M-cell cover was not re-run in full | ✓ adopted | ✓ 30 checks |
| O1 reserve cells | 1,023,895 cells | ✓ every cell: reviewers' own code with mpmath intervals (Astra used Arb); a second engine on every lower-band cell and on 65,085 upper cells | ✓ adopted | ✓ 13 checks (406,601 + 670,014 leaves) |
| O2 payment cells | 14 rows, 84,156 cells | ✓ every cell: reviewer's own code with 128-bit outward-rounded intervals | ✓ adopted | ✓ 168 checks |

## 6. The Lean formalization

The formalization uses Lean 4 v4.28 and Mathlib v4.28. It is shared with you in a private repository with three
branches:
- `main`: the n ≤ 60 theorem, `Zhang.forest_unimodal_of_card_le_sixty`.
- `kernel-checked-certificates`: the same theorem with all 17,100 certificates checked by the kernel
  (`Zhang.forest_unimodal_of_card_le_sixty_kernel`, standard axioms only).

- `analytic-route`: the whole proof, including the n ≥ 61 argument. Its top theorem has no hypotheses:

      theorem Erdos993Lean.Analytic.erdos993 : Erdos993Statement

The finite part enters through the kernel-checked certificates (`Zhang.certificatesSound_kernel`). O1 is
`VarianceBound Profile30.P` for all five bands, and O2 is `VarianceRatioBound Profile30.P` from the 14 certified rows
(§4).

Trust. The soundness theorems of all the checkers use only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). In the analytic route the certificates themselves are evaluated by exactly 271 `native_decide` calls
(30 tail, 60 atlas, 13 O1, 168 O2), and these add two axioms, `Lean.ofReduceBool` and `Lean.trustCompiler`.
`#print axioms erdos993` lists exactly these five axioms. A census of the proof term confirms the count and that the
finite part is the kernel-checked one.

## 7. Provenance

- **The mixture framework and the finite part** are yours.
- **The analytic route** was assembled in Kevin Vallier's campaign:
  - the inputs O3–O6 and the O4 atlas by "Sol" (an OpenAI Codex agent);
  - O1 by "Astra";
  - the O2 payment by GPT Pro and Sol, with the eight certificates that closed its two gaps generated by a Claude agent
    using Pro's engine;
  - the Lean formalization and all refereeing by Claude (Anthropic) agents.

  Each of O1–O6 was reviewed independently before the referee adopted it; §5 lists, per certificate family, what was
  replayed and by which code.
- **The supporting files are available on request**: the proof documents, certificates, checkers and review reports
  named above. The Lean sources and this write-up are in the repository.
