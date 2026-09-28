# What we did

A note for Tong Zhang from Kevin Vallier's Erdős #993 campaign, 2026-09-28.

**In one sentence.** Your proof of Erdős Problem #993 is now a complete, machine-checked Lean proof. Your finite-order
theorem is formalized as it stands. The large-forest half is replaced by a new argument built on your conditional
binomial mixture, and that argument is formalized too.

```lean
theorem Erdos993Lean.Analytic.erdos993 : Erdos993Lean.Erdos993Statement
```

The statement says that every finite forest has a unimodal independence sequence, in Mathlib's own terms: acyclic simple
graphs on `Fin n`, independent sets counted by `indepSetFinset`, unimodality up to `indepNum`. The theorem has no
hypotheses. `lake env lean Audit/AxiomsTheorem.lean` prints its axioms.

## 1. We reviewed your proof first (27 September)

Six independent review lanes checked your manuscript v1.1 and its supplements A and B. Each lane was an AI agent with
its own code, and none ran your scripts.

**Coverage:**
- **The finite part.** Every lemma was checked. Every inequality family held on all 515,786 forests with at most 18
  vertices. All 17,100 triples and all 1,907 LP certificates were re-verified by an independent exact checker.
- **The large-forest part.** Lemma 3.2 was reconstructed; the window was checked; the base stage n ≥ 900 was re-derived
  with all its certificates re-checked; stages 59–500 and the coverage between stages were checked.

**Findings:**
- No false statement, no counterexample and no mathematical gap.
- One writing gap, which is repairable. Stage 80's written density induction omits two conditions that its code enforces
  and its data satisfy.

We have the full reports if they are useful to you. This was an AI-assisted review, not a human referee report.

## 2. Your finite part, in Lean (branches `main` and `kernel-checked-certificates`)

We formalized the n ≤ 60 half of your method:
- König's theorem for forests;
- the decomposition;
- the eleven inequality families;
- the reduction;
- all 17,100 certificates.

The certificates are checked in two ways:
- **On `main`:** by a Lean checker whose soundness is proved, run with one `native_decide`.
- **On `kernel-checked-certificates`:** by the Lean kernel itself, in 900 `decide +kernel` slices, on standard axioms
  only. This is the version the whole theorem uses.

## 3. A new argument for forests with at least 61 vertices (branch `analytic-route`)

**Why a new argument.** Formalizing your staged chain from 900 down to 59 would mean formalizing three things:
- eight stages of certificates;
- Lemma 3.2, whose case analysis is in the Chinese supplement;
- the outside result that the base stage uses, that the path minimizes the mean at activity 1 (Andriantiana,
  Razanajatovo Misanantenaina and Wagner).

Instead we looked for one argument that works for every n ≥ 61 at once.

**Your idea, which we keep.** Tune the activity λ so that the mean of |S| is a given rank k. Condition on everything
outside a maximum-weight independent set B. What remains is K = Y + Bin(M, q).

**What we prove about the mixture.** Six facts, true for every forest:
- **O6, the window.** Every rank that could hold a valley is the mean at some λ in [1/3, 7/3]. The rise to ⌈n/4⌉ and the
  fall after the matching mode are proved in Lean, as in your Input E. Your Lemma 3.2 is not needed.
- **O1.** Var M ≤ D·m, with D ≤ 8/5 depending on the band. It is proved by an induction on rooted trees that carries a
  two-generation reserve with an entropy (KL) term.
- **O2.** Var|S| ≤ (1+θ)(1−q)W, with θ ≤ 1 depending on the band. It is proved by writing Var|S| as a sum of
  per-vertex innovations and paying them through an exact eight-term ledger. One term of the ledger compares B with a
  random competing independent set, and that is where the maximality of B is used.
- **O3, a lower tail for M.** It is proved by a potential induction on the Laplace transform, using
  E(1−q)^M = I(F − B)/I(F).
- **O5, a floor on m = E M.** It uses the density records of your stage 80, re-checked, together with the rank.
- **O4, no valley at the mean.** A criterion for mixtures of binomials turns the facts above into the absence of a
  valley. It is checked by an atlas of rational dual boxes for m < 400 and by a Fourier estimate for m ≥ 400.

O1 and O2 are new inequalities about the hard-core model on forests, and they may be of interest in their own right.
The details are in `docs/ANALYTIC_PROOF.md`.

**Where the computer is used.** O1, O2, O3 and the atlas close with interval or rational certificates over small boxes
of parameters. Two examples: O1 has about one million cells, and O2 has 84,156 cells in 14 rows. These certificates
depend on neither the size nor the shape of the forest.
- The O1 and O2 cells were replayed in full by independent code.
- Every family is checked in Lean by a checker whose soundness is proved.

## 4. Trust

- **Soundness theorems:** every one uses only the standard axioms.
- **Analytic certificates:** evaluated by exactly 271 `native_decide` calls (30 tail, 60 atlas, 13 O1, 168 O2). These
  calls add `Lean.ofReduceBool` and `Lean.trustCompiler`.
- **Finite part:** enters through the kernel-checked certificates.

A version checked only by the kernel would also require moving the analytic certificates to kernel evaluation. That is
possible in principle but expensive.

## 5. Who did what

- **Yours.** The conditional binomial mixture and the finite-order theorem.
- **Done in Kevin Vallier's campaign, by AI agents under his direction:**
  - "Sol", an OpenAI Codex agent: O3–O6, the atlas, and the assembly of O2;
  - "Astra": O1;
  - GPT Pro: the O2 payment proof;
  - Claude agents (Anthropic): the Lean formalization, all the reviews and independent replays, and the certificates
    that closed O2's last two activity ranges.

No human referee has checked the new argument yet. Every piece was independently recomputed and reviewed before it was
adopted. The proof documents, certificates, checkers and review reports are available on request.

## 6. How to check it

```sh
lake exe cache get
lake build Erdos993LeanTheorem
lake env lean Audit/AxiomsTheorem.lean
```

The certificate check modules are large, so on a machine with limited memory, build them one module at a time first;
see the README.
