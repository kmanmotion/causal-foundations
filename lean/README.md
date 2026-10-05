# Causal Foundations — Lean 4 formalization v0.2.0

This supplement formalizes **Theorems 13 and 14** of Kai Liang's
*Causal Foundations and Experimental Certification of Contingent Assignment,
Heredity, and Reflexive Maintenance*, v1.0,
[DOI 10.5281/zenodo.22902457](https://doi.org/10.5281/zenodo.22902457).

- `CausalFoundations.theorem13`: finite-horizon sequential resource feasibility
  is equivalent to feasibility of every aggregate prefix in an arbitrary
  commutative cancellative resource monoid, including horizon zero.
- `CausalFoundations.theorem14`: for an arbitrary commutative resource monoid,
  universal nonanticipating winning policies, membership of every root in the
  maximal residual-invariant set, and nonempty viable residual subfibers are
  equivalent. A memoryless policy is constructed as a consequence; general
  history dependence is allowed in the initial policy condition.

See the [Theorem 13 alignment](STATEMENT_ALIGNMENT.md),
[Theorem 14 alignment](THEOREM14_ALIGNMENT.md), and
[coverage inventory](THEOREM_COVERAGE.md). The other 14 numbered theorems and
remaining supplementary obligations are not claimed to be formalized.

There are **44 audited main theorem declarations and 10 boundary-test theorems**.
These include auxiliary lemmas and are not counts of new research discoveries.
Theorem 13 depends on the standard `Classical.choice`; Theorem 14 depends on the
standard `propext`, `Classical.choice` and `Quot.sound`. Every transitive dependency
is checked against an explicit list. Omitted proofs and custom dependencies fail
verification. The Boolean positive example and truncated-addition negative example
check that Theorem 14 neither silently assumes cancellation nor claims every
commutative monoid admits a universal winning policy.

## Reproduce

The toolchain is pinned to `leanprover/lean4:v4.24.0`. No mathlib is needed.
From this directory, with Lean and Lake installed:

```sh
lake build CausalFoundations
lake env lean AxiomAudit.lean
lake env lean BoundaryTests.lean -o .lake/build/lib/lean/BoundaryTests.olean
lake env lean ResidualGameTests.lean -o .lake/build/lib/lean/ResidualGameTests.olean
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
all 54 theorem dependencies, rejection of a false statement, fresh kernel replay
of all constants imported by `ReplayAll` (both proof modules and both test modules),
and a clean source rebuild followed by the same complete replay. Main and boundary
dependency audits must agree between the two builds. There are 16 command checks.
`NegativeControl.lean` deliberately contains an invalid proof of `2 = 3` and
must fail compilation; it is excluded from the library and default build target.

[GitHub Actions](https://github.com/kmanmotion/causal-foundations/actions/workflows/lean.yml)
runs these checks on standard Ubuntu for relevant pushes and pull requests.
Each run uploads `results.json` and command logs for 14 days. The run result
and its exact checked commit determine verification status; this README alone
is not evidence that a particular commit passed. CI requires a clean checkout.

## Source and verification scope

`SOURCE_LOCK.json` identifies the public v1.0 commit and the exact three PDF
hashes. `verification/TOOLCHAIN_LOCK.json` pins the Lean release archive and
checker. Source code is versioned; compiler downloads, dependencies and compiled
caches are generated during verification.

The earlier local environment required the process-path workaround documented
in `verification/proc_self_compat.c`. GitHub verification forbids that workaround
and requires the unchanged official Lean executable and shared runtime.
For an affected local environment only, the runner accepts a compiled
`--compat-library`; such a result is explicitly labelled as a compatibility run.

Fresh replay uses the same Lean kernel, not an independently implemented
verifier. Paper-to-formal-statement alignment was reviewed by the assisting AI;
it has not received independent human certification. The selected strategies
are set-theoretic, with no assertion of measurability, continuity or computability.
Formal verification does not establish biochemical realization or historical
origin claims. Publication and review status are described in the
[repository README](../README.md).

The proposed next target is Theorem 15's semantic sufficient-basis quotient
poset. It is not yet formalized here.
