# Erdős Problem #993: every forest with at most 60 vertices is unimodal (Lean 4)

Private preview, not for redistribution. The license is to be decided.

This repository is a Lean 4 formalization, with Mathlib `v4.28.0`, of the finite part of T. Zhang's method for Erdős
Problem #993. It proves that the independence sequence of every forest with at most 60 vertices is unimodal.

## Main theorem

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

## The analytic route: forests with at least 61 vertices (branch `analytic-route`)

This branch adds a Lean formalization of an analytic argument for large forests, built on T. Zhang's conditional
binomial mixture over a maximum-weight independent set. Everything is proved in Lean except the two hypotheses of the
top theorem:

```lean
theorem Erdos993Lean.Analytic.State.erdos993_of_upperBox_O2
    (hU : Erdos993Lean.Analytic.Reserve.UpperBoxOK)
    (h2 : Erdos993Lean.Analytic.VarianceRatioBound Erdos993Lean.Analytic.Profile30.P) :
    Erdos993Statement
```

(`Erdos993Lean/Analytic/State.lean`).

- **Proved in Lean**, together with the kernel-checked finite part above:
  - the reduction to excluding weak valleys at interior ranks of an activity window [1/3, 7/3];
  - the mixture identities;
  - an explicit no-valley lemma;
  - a large-mean Fourier theorem;
  - a small-mean atlas of dual certificates;
  - the lower tail of the free count;
  - density floors;
  - the variance of the free count (input O1) on all five activity bands, except the finite box of the top band.
- **`UpperBoxOK`**: the finite box of the top band's O1 certificate (617,294 cells). It is proved on paper and
  independently replayed; its Lean checker is in progress.
- **`VarianceRatioBound Profile30.P`** (input O2), the variance-ratio bound: in progress.

Trust: standard axioms, plus `Lean.ofReduceBool` and `Lean.trustCompiler` through 94 `native_decide` certificate
checks. Their soundness is proved in Lean on standard axioms: 30 for the tail cells, 60 for the atlas and 4 for O1's
lower bands.

Build: `lake build Erdos993LeanAnalyticState`, which also builds the certificate libraries it needs. Build the check
modules one at a time if memory is tight.

## Build

```sh
lake exe cache get
lake build
lake build Erdos993LeanZhangCert
lake env lean Audit/AxiomsZhangCert.lean
lake build Erdos993LeanZhangKernel        # kernel-checked certificates; a few GB of memory per module
lake env lean Erdos993Lean/ZhangKernel/Audit.lean
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

The Zhang modules also import a few general supporting modules from a larger package, for unimodality lemmas, the
bipartite tail and matching bounds: `Ceiling/`, `SmallAlpha/`, `Floor/`, `Caterpillar/`, `Hoggar.lean`,
`Sequences.lean` and `IndependencePoly.lean`. Their comments sometimes refer to that package's internal notes.
