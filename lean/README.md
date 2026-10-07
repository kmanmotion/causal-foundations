# Causal Foundations — Lean 4 formalization v0.7.0

This supplement formalizes **Theorems 2, 3, 13, 14, 15 and 16** and the
**deterministic branch of Theorem 1** of Kai Liang's
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
- `CausalFoundations.theorem15`: semantic sufficient-basis classes form a
  partial order and an upper set in the weak-to-strong order. Minimal sufficient
  classes correspond exactly to maximal sufficient conjunction-generated
  theorem domains, relative to one fixed finite premise library.

- `CausalFoundations.theorem16`: bijective transport of ambient models and
  atoms that preserves and reflects target and atom truth constructs an order
  isomorphism of sufficient semantic classes. Minimal bases and maximal
  conjunction-generated domains are invariant under this transport.

- `CausalFoundations.theorem2`: a channel factoring through the constructed
  state-action orbit quotient on a group-stable domain is symmetry-fixed when
  the assay is equivariant on that domain. Stable preparation and equivariant
  transition/intervention families yield stable finite-path reachability.

- `CausalFoundations.theorem1_deterministic`: the paper's inverse channel
  relabeling action is constructed. Equivariant assays send exactly fixed
  realized states to singleton channel orbits. Exactly equivariant deterministic
  evolution preserves those fixed states and excludes contingent assignment
  from them. Theorem 1's stochastic branch remains unformalized.

- `CausalFoundations.theorem3`: actual first-hit orientation events on a finite
  transitive orbit have equal probabilities under an invariant path probability
  law. Actual attainment, measurability and an invariant null exception set are
  explicit. Conditional uniformity requires positive hit probability. This
  endpoint is in the [probability subproject](probability/README.md).

See the [Theorem 3 alignment](THEOREM3_ALIGNMENT.md),
[Theorem 2 alignment](THEOREM2_ALIGNMENT.md),
[Theorem 1 deterministic alignment](THEOREM1_DETERMINISTIC_ALIGNMENT.md),
[Theorem 13 alignment](STATEMENT_ALIGNMENT.md),
[Theorem 14 alignment](THEOREM14_ALIGNMENT.md),
[Theorem 15 alignment](THEOREM15_ALIGNMENT.md),
[Theorem 16 alignment](THEOREM16_ALIGNMENT.md), and
[coverage inventory](THEOREM_COVERAGE.md). Theorem 1 has partial completion status: its stochastic branch remains
unformalized. The other 9 numbered theorems and remaining supplementary
obligations are not claimed to be formalized.

There are **145 audited main theorem declarations and 60 boundary-test theorems**
across the core and probability subprojects (205 total). The original core has
124 main and 44 test theorems; Theorem 3 adds 21 main and 16 test theorems.
These include auxiliary lemmas and are not counts of new research discoveries.
Theorem 13 depends on the standard `Classical.choice`; Theorem 14 depends on the
standard `propext`, `Classical.choice` and `Quot.sound`; Theorems 15 and 16 depend on
`propext` and `Quot.sound`. Theorem 2 and Theorem 1's deterministic endpoint use only
`Quot.sound`. Theorem 3 uses `propext`, `Classical.choice` and `Quot.sound`. Every transitive dependency
is checked against an explicit list. Omitted proofs and custom dependencies fail
verification. The Boolean positive example and truncated-addition negative example
check that Theorem 14 neither silently assumes cancellation nor claims every
commutative monoid admits a universal winning policy.
The semantic tests check aliases, ambient restriction, direction of entailment,
and failure of an enlarged-formula interpretation of domain maximality.
Representation tests also check model/atom relabeling, empty inputs and
counterexamples to weakening the transport conditions.
Fixed-set tests distinguish realized-state fixedness from invariant equal
weights, test inverse channel relabeling and expose the need for both
assay and evolution equivariance.
Orbit-erasure tests check exact orbit identification, restricted-domain claims,
failures without stability/equivariance/factorization, transported intervention
families and empty preparation.

## Reproduce

The toolchain is pinned to `leanprover/lean4:v4.24.0`. The original core needs no Mathlib. The separate probability subproject pins
Mathlib and all supporting repositories; use its [reproduction instructions](probability/README.md)
to verify Theorem 3 as well.
From this directory, with Lean and Lake installed:

```sh
lake build CausalFoundations
lake env lean AxiomAudit.lean
lake env lean BoundaryTests.lean -o .lake/build/lib/lean/BoundaryTests.olean
lake env lean ResidualGameTests.lean -o .lake/build/lib/lean/ResidualGameTests.olean
lake env lean SemanticBasisTests.lean -o .lake/build/lib/lean/SemanticBasisTests.olean
lake env lean RepresentationTests.lean -o .lake/build/lib/lean/RepresentationTests.olean
lake env lean FixedSetTests.lean -o .lake/build/lib/lean/FixedSetTests.olean
lake env lean OrbitErasureTests.lean -o .lake/build/lib/lean/OrbitErasureTests.olean
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
all 168 core theorem dependencies, rejection of a false statement, fresh kernel replay
of all safe, total constants imported by `ReplayAll` (six proof modules and six test modules),
and a clean source rebuild followed by the same complete replay. Main and boundary
dependency audits must agree between the two builds. There are 24 core command checks. The probability runner adds 16 checks, including
all 37 new declarations and two fresh replays with transitive Mathlib imports.
Its cold project build reuses the pinned external dependency cache and copies
no compiled project files. Both runners must pass for v0.7.0 (40 checks total).
`NegativeControl.lean` deliberately contains an invalid proof of `2 = 3` and
must fail compilation; it is excluded from the library and default build target.

[GitHub Actions](https://github.com/kmanmotion/causal-foundations/actions/workflows/lean.yml)
runs these checks on standard Ubuntu for relevant pushes and pull requests.
Each run uploads separate core and probability artifacts containing
`results.json` and command logs for 14 days. The run result
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
verifier. The pinned checker omits unsafe and partial definitions; every project
theorem and its logical proof dependencies is within the replay scope. Paper-to-formal-statement alignment was reviewed by the assisting AI;
it has not received independent human certification. Theorem 14
selectors remain set-theoretic, without a claim of measurability, continuity or
computability. Theorem 3 instead assumes the declared measurable first-time and
label maps and uses an actual probability measure.
Formal verification does not establish biochemical realization or historical
origin claims. Publication and review status are described in the
[repository README](../README.md).

The proposed next target is Theorem 4's finite matching genesis construction,
starting with partial matchings, the frozen challenge assay and single-link ablation. Theorem 1's stochastic branch retains
separate incomplete status until its conditional-probability and countable
actual-update obligations are proved.
