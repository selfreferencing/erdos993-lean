# Erdős Problem #993 in Lean 4

Lean 4 formalization of a proof of Erdős Problem #993 (the Alavi–Malde–Schwenk–Erdős conjecture), built on the proof
due to Tong Zhang and Wei Li.

We claim a Lean 4 proof that the independent set sequence of every finite forest is unimodal.
- **Forests with at most 60 vertices.** The formalization follows Zhang and Li's finite-order argument, and all 17,100
  of their certificate cases are checked in Lean.
- **Forests with at least 61 vertices.** The formalization uses a different argument. It keeps Zhang and Li's
  conditional binomial mixture but replaces their large-order argument. This argument was developed in this project,
  and it has not been independently reviewed.

The finite-order mathematics and the mixture are Zhang and Li's. The large-order argument and the formalization come
from Kevin Vallier's project; see "Method".

Zhang and Li's work:
- T. Zhang and W. Li, *Unimodality of Forest Independence Polynomials*, manuscript, Zenodo,
  <https://doi.org/10.5281/zenodo.22999166> (not yet refereed; an arXiv version is in preparation). The verification materials
  are at <https://github.com/zhangzenozhang-jpg/forest-unimodality-arxiv-verification> (companion version 2026-09-27,
  commit `8067893`).
- The earlier consolidated manuscript, which is the version cited by section number in the Lean comments: T. Zhang,
  *Exact Certificates for Unimodality of Forest Independence Polynomials*, v1.1 (26 September 2026),
  <https://github.com/zhangzenozhang-jpg/-forest-unimodality-proof> (commit `d5669d7`).

## Main theorem

```lean
theorem Erdos993Lean.Analytic.erdos993 : Erdos993Statement
```

The theorem is in `Erdos993Lean/Analytic/Erdos993.lean`. Its statement uses these definitions, verbatim from
`Erdos993Lean/Statement.lean`:

```lean
/-- A finite forest encoded as a simple graph on the vertex type `Fin n`. -/
structure FiniteForest where
  n : Nat
  graph : SimpleGraph (Fin n)
  isForest : graph.IsAcyclic

/--
`UnimodalUpTo N a` says that the finite sequence `a 0, a 1, ..., a N` has a peak: it is
nondecreasing before the peak and nonincreasing after it.
-/
def UnimodalUpTo (N : Nat) (a : Nat → Nat) : Prop :=
  ∃ peak : Nat,
    peak ≤ N ∧
      (∀ k : Nat, k < peak → a k ≤ a (k + 1)) ∧
      (∀ k : Nat, peak ≤ k → k < N → a (k + 1) ≤ a k)

/-- The number of independent sets of cardinality `k` in a finite forest (Mathlib's
`indepSetFinset`, classical decidability). -/
noncomputable def independenceCount (F : FiniteForest) (k : Nat) : Nat := by
  classical
  exact (F.graph.indepSetFinset k).card

/-- The maximum size of an independent set in the finite forest. -/
noncomputable def independenceNumber (F : FiniteForest) : Nat :=
  F.graph.indepNum

/-- The independence sequence of `F` is unimodal through its independence number. -/
noncomputable def independenceSequenceUnimodal (F : FiniteForest) : Prop :=
  UnimodalUpTo (independenceNumber F) (independenceCount F)

noncomputable def Erdos993Statement : Prop :=
  ∀ forest : FiniteForest, independenceSequenceUnimodal forest
```

In plain English: let F be a finite forest with independence number α, and let i_k be the number of independent sets
of size k. Then for some p, i₀ ≤ i₁ ≤ … ≤ i_p ≥ i_{p+1} ≥ … ≥ i_α.

Conventions:
- **Forests, not only trees.** A forest is any acyclic simple graph on n labelled vertices. This includes disconnected
  graphs and the empty graph (n = 0).
- **The sequence starts at i₀ = 1.** The empty set is counted; the lemma `independenceCount_zero` proves
  `independenceCount F 0 = 1`.
- **Unimodality is stated for i₀, …, i_α.** Since i_k = 0 for every k > α, this is the same as unimodality of the
  whole sequence (i_k)_{k ≥ 0}. That equivalence is elementary and is not stated as a separate theorem here.

## Verification status

- **Lean:** `leanprover/lean4:v4.28.0` (file `lean-toolchain`).
- **Mathlib:** commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`), pinned in `lake-manifest.json`.
- **Axioms.** `#print axioms Erdos993Lean.Analytic.erdos993` prints:

  ```
  'Erdos993Lean.Analytic.erdos993' depends on axioms: [propext,
   Classical.choice,
   Lean.ofReduceBool,
   Lean.trustCompiler,
   Quot.sound]
  ```

- **`sorry`: none.** `git grep -n -w sorry -- '*.lean'` returns 4 lines, all inside comments (for example "no `sorry`").
  The axiom list above contains no `sorryAx`.
- **Other markers.** There are no `axiom` declarations. `unsafe`, `implemented_by` and `@[extern]` appear only in
  comments, never in code.
- **`native_decide`.** **The theorem depends on `native_decide`: its axioms include `Lean.ofReduceBool` and
  `Lean.trustCompiler` as well as `propext`, `Classical.choice` and `Quot.sound`.** The modules the theorem imports
  contain 271 `native_decide` evaluations, all in the argument for forests with at least 61 vertices. For those steps
  the proof trusts the Lean compiler and runtime, not only the kernel. The finite part (at most 60 vertices) does not
  use `native_decide`: its certificates are checked by kernel reduction (`decide +kernel`).

## Structure of the proof

There are two parts, joined at 60/61 vertices.

**Forests with at most 60 vertices.**

```lean
theorem Erdos993Lean.Zhang.forest_unimodal_of_card_le_sixty_kernel (F : FiniteForest) (hn : F.n ≤ 60) :
    independenceSequenceUnimodal F
```

- The file is `Erdos993Lean/ZhangKernel/Main.lean`.
- The reduction to a finite certificate claim is Zhang and Li's (`Erdos993Lean/Zhang/`, `Erdos993Lean/Zhang/Rows/`).
- The certificate claim `Zhang.certificatesSound_kernel` covers the 17,100 parameter triples (n, a, k) of the domain
  `P60`:
  - 2 ≤ n ≤ 60, ⌈n/2⌉ ≤ a ≤ n − 1, 1 ≤ k < ⌊(2a+1)/3⌋ (`Erdos993Lean/Zhang/Relaxation.lean`);
  - `#eval P60.card` prints `17100`.
- They are checked by 900 kernel evaluations (`decide +kernel`), one per pair (n, a), in the 24 modules of
  `Erdos993Lean/ZhangKernel/Checks/`.
- The checker's soundness is proved in Lean for arbitrary data.
- The axioms of this part are `[propext, Classical.choice, Quot.sound]`, both for `forest_unimodal_of_card_le_sixty_kernel`
  and for `Zhang.certificatesSound_kernel`.
- Build time, clean clone: the 24 check modules took 7,067 s of module time (longest 557 s), and the 24 generated data
  modules another 1,887 s. The build runs modules in parallel, so these are module times, not wall time.

**Forests with at least 61 vertices.** `noWeakValley_of_analytic_inputs` (`Erdos993Lean/Analytic/Top.lean`, hypothesis
`61 ≤ F.n`) excludes a weak valley at every interior rank. Six inputs about the mixture are proved in Lean:
- O6, the activity window;
- O1, a variance bound Var M ≤ D·m;
- O2, a variance-ratio bound Var K ≤ (1+θ)(1−q)W;
- O3, a lower tail for M;
- O4, a no-valley criterion;
- O5, a floor on E M.

Four families of parameter-box certificates are checked by the 271 `native_decide` evaluations above:
- 30 tail bands (`Analytic/TailCert/Checks/`);
- 60 atlas bands (`Analytic/Atlas/Checks/`);
- 13 O1 boxes (`Analytic/Reserve/Cert/Checks/`, `Analytic/Reserve/UpperCert/Checks/`);
- 168 O2 root boxes (`Analytic/O2/Cert/Checks/`).

These certificates do not depend on the forest.

**The composition** (`Erdos993Lean/Analytic/Top.lean`):

```lean
theorem erdos993_of_analytic_inputs_pending
    (hmix : MixtureFacts) (hcert : Zhang.Cert.CertificatesSound)
    {P : Profile} (h : AnalyticInputs P) : Erdos993Statement := by
  intro F
  rcases le_or_gt F.n 60 with hn | hn
  · exact Zhang.Rows.finite60_of_certificates hcert F hn
  · unfold independenceSequenceUnimodal
    exact unimodalUpTo_of_unimodal (unimodal_of_noWeakValley_window F
      (fun k hk1 hk2 => noWeakValley_of_analytic_inputs hmix h F (by omega) k hk1 hk2))
```

`erdos993` instantiates it. The mixture facts are `mixtureFacts`, the certificate claim is
`Zhang.certificatesSound_kernel`, and the analytic inputs come from their theorems. The chain is `erdos993` →
`Reserve.UpperCert.erdos993_of_O2` → `State.erdos993_of_upperBox_O2` → `State.erdos993_of_O1_O2` →
`Glue30.erdos993_of_profile30` → `erdos993_of_analytic_inputs_std` → `erdos993_of_analytic_inputs_cert` →
`erdos993_of_analytic_inputs_pending`.

## Relation to the paper

**Following Zhang and Li directly.** The Lean comments use the section numbers of Zhang's v1.1 manuscript.
- **The finite-order theorem** (v1.1, Proposition 1.2):
  - König's theorem for forests (`Zhang/Konig.lean`);
  - the decomposition relative to a maximum independent set (`Zhang/Decomposition.lean`);
  - the coefficient bounds (`Zhang/CoefficientBounds.lean`);
  - the relaxation and the certificate principle (`Zhang/Relaxation.lean`);
  - the reduction (`Zhang/Finite60.lean`);
  - the eleven inequality families (`Zhang/Rows/`);
  - the certificate layer (`ZhangKernel/`).
- **The certificate data** are theirs.
- **The conditional binomial mixture** K = Y + Bin(M, q) over a maximum-weight independent set B, and its identities
  (`mixtureFacts`, `Analytic/HardCore/`).

**Replaced.** Zhang and Li's argument for large forests is not formalized. Instead, the formalization proves every
forest with at least 61 vertices through the inputs O1–O6 above, all built on their mixture. The mathematics is in
`docs/ANALYTIC_PROOF.md`. O1 and O2 are the project's own inequalities about the hard-core model on forests.

## Dependencies and attribution

- **FLNYZ (arXiv:2609.20961): not used.** No result of that paper is stated, assumed or proved in this repository.
- **Galvin–Hilyard: not used.** No result of that paper is stated, assumed or proved in this repository.
- **No assumptions.** The top theorem has no hypotheses, and there are no `axiom` declarations.
- **Supporting lemmas from earlier work.** Several supporting lemmas (in `Erdos993Lean/Ceiling/`, `Floor/`, `Caterpillar/` and `SmallAlpha/`) come from the project's earlier work on this problem; comments in those files refer to internal project notes. They are used as lemmas only; no earlier result is claimed here.
- **Classical results proved here, with their sources.**
  - Hoggar's theorem that log-concavity is preserved by convolution (`Erdos993Lean/Hoggar.lean`; S. G. Hoggar,
    J. Combin. Theory Ser. B 16 (1974)).
  - The decrease of i_k from ⌈(2α − 1)/3⌉ on (`Erdos993Lean/SmallAlpha/BipartiteTail.lean`). This is classical for
    bipartite graphs (V. E. Levit and E. Mandrescu); the proof here is the project's.
- **Reused code: none found.**
  - Compared against github.com/junwei-lu/Erdos_993_Tree_Independent_Set_Unimodality at commit `b2a1d3e`, the Lean
    formalization of FLNYZ. No shared code beyond generic Mathlib tactic lines. 15 declaration names coincide (for
    example `indepPoly` and `mem_avail`), with different statements or proofs.
  - No code from Tong Zhang's repositories.
- **Reused data: Zhang and Li's certificates.** The source is `certificates.json` (SHA-256 `a77f4fc4…bcc5a`), inside
  `inputs/forest_n60_extension_and_n100_gap.zip` of github.com/zhangzenozhang-jpg/-forest-unimodality-proof at commit
  `d5669d7`. The same zip (git blob `e849b89`) is in `companion/2026-09-27/anc/repro/inputs/` of
  github.com/zhangzenozhang-jpg/forest-unimodality-arxiv-verification at commit `8067893`. The data are stored in two
  places:
  - `Erdos993LeanZhangCompute/Checker/Data1.lean`–`Data5.lean`, as strings;
  - `Erdos993Lean/ZhangKernel/Data/`, as check items generated from them.
- **Mathlib** is the only Lean dependency (with its own dependencies, pinned in `lake-manifest.json`).

## License

- The Lean code is released under the Apache License 2.0 (`LICENSE`).
- The certificate data are copyright Tong Zhang and Wei Li and are redistributed here under CC BY 4.0 with their permission; see `NOTICE` for the source commit, the license link and the modifications made.

## Building

```sh
git clone https://github.com/selfreferencing/erdos993-lean.git
cd erdos993-lean
lake exe cache get
lake build                          # default target: the statement and Zhang and Li's reduction for n ≤ 60
lake build Erdos993LeanTheorem      # the theorem, with every certificate library it imports
lake env lean Audit/AxiomsTheorem.lean
```

`lake build` alone does not build the theorem; `lake build Erdos993LeanTheorem` does.

Measured on a clean clone of commit `dde62e4` (2026-09-28/29): Apple M5, 10 cores, 32 GB RAM, macOS 26.3.1.

| Command | Wall time | Result |
|---|---|---|
| `lake exe cache get` | 175 s | exit 0 |
| `lake build` | 2,025 s | exit 0, 8,063 jobs |
| `lake build Erdos993LeanTheorem` | 3,732 s | exit 0, 8,709 jobs |
| `lake env lean` on the axiom audit | 37 s | the output above |

The total was 1 h 39 min. The build finished with no errors; its 88 warnings are linter and linker notices, and
none is a `sorry`. The machine was running other jobs at the same time (load average 27 at the start), so an idle
machine should be faster. The largest single process peaked at about 6.2 GB of memory.

The certificate modules are large. If memory is tight, build them one module at a time; see the header of each
certificate library's `Main.lean`. The toolchain and every dependency are pinned (`lean-toolchain`,
`lake-manifest.json`).

## Method

This formalization was produced by a system of AI agents directed by Kevin Vallier: Anthropic's Claude models, and
OpenAI's Codex and GPT models. The same system developed the large-order argument. Lean is the check. No human has
reviewed the Lean code line by line. The claim rests on the Lean kernel and, for the `native_decide` evaluations, on
the Lean compiler.

## Status

This is an unrefereed claim. The paper has not been peer reviewed. Corrections and questions are welcome.

Contact: Kevin Vallier, kevinvallier@gmail.com.
