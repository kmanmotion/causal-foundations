# Causal Foundations — Lean 4 pilot v0.1.0

This supplement formalizes **Theorem 13** of Kai Liang's
*Causal Foundations and Experimental Certification of Contingent Assignment,
Heredity, and Reflexive Maintenance*, v1.0,
[DOI 10.5281/zenodo.22902457](https://doi.org/10.5281/zenodo.22902457).

`CausalFoundations.theorem13` proves the finite-horizon equivalence between
sequential resource feasibility and decomposability of all aggregate prefixes
in an arbitrary commutative cancellative resource monoid, including horizon zero.
The [statement alignment](STATEMENT_ALIGNMENT.md) records the hypotheses and
quantifiers. The [coverage inventory](THEOREM_COVERAGE.md) tracks the other
15 numbered theorems and 24 grouped supplementary obligations.

Only Theorem 13 is formalized. The 13 audited theorem declarations include
auxiliary results; five additional boundary-test theorems cover zero horizon
and a noncancellative obstruction. These counts do not represent new research
discoveries or whole-paper completion. Theorem 13 uses the standard
`Classical.choice`; the verification rejects custom axioms and missing proofs.

## Reproduce

The toolchain is pinned to `leanprover/lean4:v4.24.0`. This pilot needs no mathlib.
From this directory, with Lean and Lake installed:

```sh
lake build CausalFoundations
lake env lean AxiomAudit.lean
lake env lean BoundaryTests.lean -o .lake/build/lib/lean/BoundaryTests.olean
```

For the complete checks, obtain the official
[lean4checker](https://github.com/leanprover/lean4checker) at commit
`da26eb05e9959402afcb9bd6dfe5dc4f700f70d6`, then run:

```sh
python3 verification/run_checks.py \
  --toolchain /absolute/path/to/lean-4.24.0-linux \
  --checker /absolute/path/to/lean4checker \
  --require-standard-runtime
```

The runner checks the three published PDF hashes, official executable hashes,
all 18 theorem axiom dependencies, rejection of a false statement, fresh kernel
replay, and a clean rebuild from source followed by another kernel replay.
`NegativeControl.lean` deliberately contains an invalid proof of `2 = 3` and
must fail compilation; it is excluded from the library and default build target.

[GitHub Actions](https://github.com/kmanmotion/causal-foundations/actions/workflows/lean.yml)
runs these checks on standard Ubuntu for relevant pushes and pull requests.
Each run uploads `results.json` and command logs for 14 days. The run result
and its exact checked commit determine verification status; the presence of
this README alone is not evidence that a particular commit passed.

## Source and verification scope

`SOURCE_LOCK.json` identifies the public v1.0 commit and the exact three PDF
hashes. `verification/TOOLCHAIN_LOCK.json` pins the Lean release archive and
checker. Source code is versioned; compiler downloads, dependencies and compiled
caches are generated during verification.

The earlier local run required the process-path workaround documented in
`verification/proc_self_compat.c`. GitHub verification forbids that workaround
and requires the unchanged official Lean executable and shared runtime.
For an affected local environment only, the runner accepts a compiled
`--compat-library`; such a result is explicitly labelled as a compatibility run.

Fresh replay uses the same Lean kernel, not an independently implemented
verifier. Paper-to-formal-statement alignment was reviewed by the assisting AI;
it has not received independent human certification. Formal verification of this
mathematical statement does not establish biochemical realization or historical
origin claims. The manuscript's publication and review status is described in
the [repository README](../README.md).

The next mathematical target is Theorem 14, beginning with explicit residual-game
and history-dependent strategy definitions. It is not yet formalized here.
