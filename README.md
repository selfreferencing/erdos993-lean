# Erdős Problem #993 in Lean 4: every forest has a unimodal independence sequence

Private preview, not for redistribution. The license is to be decided.

This repository is a Lean 4 formalization, with Mathlib `v4.28.0`, of Erdős Problem #993.
- Branch `main` formalizes the finite part of T. Zhang's method: the independence sequence of every forest with at
  most 60 vertices is unimodal.
- This branch, `analytic-route`, adds an analytic argument for forests with at least 61 vertices. With it, the full
  statement is proved with no hypotheses; see "The whole theorem" below.

`WHAT_WE_DID.md` explains in plain terms what was done and by whom. `docs/ANALYTIC_PROOF.md` gives the mathematics of
the argument for forests with at least 61 vertices.

## The finite part: forests with at most 60 vertices

```lean
theorem Erdos993Lean.Zhang.forest_unimodal_of_card_le_sixty (F : FiniteForest) (hn : F.n ≤ 60) :
    independenceSequenceUnimodal F
```

The theorem is in `Erdos993Lean/ZhangCert/Final.lean`. The definitions of the statement are in
`Erdos993Lean/Statement.lean`:
- a `FiniteForest` is a simple graph on `Fin n` that is acyclic in Mathlib's sense (`SimpleGraph.IsAcyclic`);
- independent sets are counted with Mathlib's `indepSetFinset`;
- unimodality is weak unimodality up to the independence number.

## Method

The method is T. Zhang, *Exact Certificates for Unimodality of Forest Independence Polynomials*, v1.1 (2026),
Proposition 1.2:
- König's theorem for forests;
- the decomposition relative to a maximum independent set with few edges in its complement (Lemma 2.5);
- the path and matching bounds;
- the relaxation and certificate principle;
- the eleven families of linear inequalities (Section 2.9);
- the 17,100 parameter cases settled by certificates.

## What is proved, and with which axioms

- **Default target** (`lake build`), standard axioms only (`propext`, `Classical.choice`, `Quot.sound`):
  - the statement;
  - König for forests (`Zhang.indepNum_add_matchingNumber`);
  - the decomposition, the coefficient bounds, and the relaxation and certificate principle;
  - the reduction (`Zhang.finite60_of_sound`);
  - every inequality family (`Zhang.Rows.rowsSound`).
- **Optional target** (`lake build Erdos993LeanZhangCert`): the certificate claim `Zhang.certificatesSound`.
  - A certificate checker is written in Lean, and its soundness is proved for arbitrary data
    (`ZhangCertX.checkRange_sound`, standard axioms).
  - The checker is evaluated on the author's certificate data by exactly one `native_decide`
    (`ZhangCertX.checkRange_2_60`, a few seconds). The data are 49 strings in
    `Erdos993LeanZhangCompute/Checker/Data*.lean`.
  - The axioms of the final theorem are therefore `propext`, `Classical.choice`, `Quot.sound`,
    `Lean.ofReduceBool` and `Lean.trustCompiler`.

- **Kernel-checked certificates** (optional target `lake build Erdos993LeanZhangKernel`): the same certificate claim
  checked by the Lean kernel itself, with no `native_decide` and standard axioms only.
  - `Zhang.certificatesSound_kernel` is proved by 900 `decide +kernel` slices over a kernel-reducible mirror of the
    checker (`Erdos993Lean/ZhangKernel/`); the whole run takes about 10 minutes of kernel time.
  - `Zhang.forest_unimodal_of_card_le_sixty_kernel` is the 60-vertex theorem on `propext`, `Classical.choice` and
    `Quot.sound` alone (`Erdos993Lean/ZhangKernel/Audit.lean` prints the axioms).

## The whole theorem (branch `analytic-route`)

```lean
theorem Erdos993Lean.Analytic.erdos993 : Erdos993Lean.Erdos993Statement
```

The theorem is in `Erdos993Lean/Analytic/Erdos993.lean`. `Erdos993Statement` says that every `FiniteForest` has a
unimodal independence sequence; its definitions are the ones described above, in `Erdos993Lean/Statement.lean`. That
file's docstring still calls the problem open, because it is kept byte-identical to the pinned statement file.

The proof has two parts.
- **Forests with at most 60 vertices.** The kernel-checked certificates above (`Zhang.certificatesSound_kernel`).
- **Forests with at least 61 vertices.** An analytic argument built on T. Zhang's conditional binomial mixture over a
  maximum-weight independent set. Everything is proved in Lean:
  - the reduction to excluding weak valleys at interior ranks, each of which is the hard-core mean at an activity in
    [1/3, 7/3] (O6);
  - the mixture identities;
  - an explicit no-valley lemma, with a small-mean atlas of rational dual certificates and a large-mean Fourier
    theorem (O4);
  - the lower tail of the free count M (O3) and floors on its mean (O5);
  - Var M ≤ D·m on all five activity bands (O1, `VarianceBound Profile30.P`);
  - Var K ≤ (1+θ)(1−q)W on the whole activity window (O2, `VarianceRatioBound Profile30.P`), from 14 certified
    coefficient rows.

Trust. Every soundness theorem uses only the standard axioms. The analytic route evaluates its certificates with
exactly 271 `native_decide` calls: 30 for the tail cells, 60 for the atlas, 13 for O1 and 168 for O2. These calls add
`Lean.ofReduceBool` and `Lean.trustCompiler`:

```
'Erdos993Lean.Analytic.erdos993' depends on axioms:
  [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```

Build with `lake build Erdos993LeanTheorem`, then run `lake env lean Audit/AxiomsTheorem.lean`. The certificate check
modules are large, so if memory is tight, build them one module at a time first; see the header of each certificate
library's `Main.lean`.

## Build

```sh
lake exe cache get
lake build
lake build Erdos993LeanZhangCert
lake env lean Audit/AxiomsZhangCert.lean
lake build Erdos993LeanZhangKernel        # kernel-checked certificates; a few GB of memory per module
lake env lean Erdos993Lean/ZhangKernel/Audit.lean
lake build Erdos993LeanTheorem             # the whole theorem, with every certificate library it needs
lake env lean Audit/AxiomsTheorem.lean
```

The two audit commands print the axioms of the headline results. A from-scratch build of all three targets, with only
Mathlib's cache, took about 51 minutes on a busy 10-core machine, mostly the 24 kernel-check modules.

## Layout

| Path | Contents |
|---|---|
| `Erdos993Lean/Statement.lean` | the statement |
| `Erdos993Lean/Zhang/` | König for forests, decomposition, coefficient bounds, relaxation, the reduction for n ≤ 60 |
| `Erdos993Lean/Zhang/Rows/` | the inequality families |
| `Erdos993Lean/ZhangCert/`, `Erdos993LeanZhangCompute/` | the certificate checker, its soundness, the data and the final theorem |
| `Erdos993Lean/ZhangKernel/` | the kernel-checked certificates: a kernel-reducible checker, its soundness and the 900 kernel slices |
| `Erdos993Lean/Analytic/` | the argument for n ≥ 61: the mixture, the window, the no-valley lemma, the atlas (`Atlas/`), the tail (`TailCert/`), the floors, O1 (`Reserve/`), O2 (`O2/`), and the whole theorem (`Erdos993.lean`) |

The Zhang modules also import a few general supporting modules from a larger package, for unimodality lemmas, the
bipartite tail and matching bounds: `Ceiling/`, `SmallAlpha/`, `Floor/`, `Caterpillar/`, `Hoggar.lean`,
`Sequences.lean` and `IndependencePoly.lean`. Their comments sometimes refer to that package's internal notes.
