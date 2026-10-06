# Theorem 2 alignment

Baseline: *Causal Foundations and Experimental Certification of Contingent
Assignment, Heredity, and Reflexive Maintenance*, v1.0,
[DOI 10.5281/zenodo.22902457](https://doi.org/10.5281/zenodo.22902457),
main text section 3.2, pages 5–6. The statement and its domain caveat were
checked against both rendered published pages. The channel action is the
constructed inverse relabeling from section 2.3 and the Theorem 1 module.
The three PDFs and publication commit remain bound by `SOURCE_LOCK.json`.

`CausalFoundations.theorem2` proves the pointwise symmetry-quotient erasure
statement on the supplied domain. Reachability stability is additionally
derived under the preparation and transition-family conditions described in
the published paragraph. No fixedness assumption on individual input states
is needed.

| Published object or claim | Lean representation | Binding |
|---|---|---|
| Group Γ and action on causal states | `SymmetryGroup`, `Action` | Reuses explicit group and action laws from Theorem 1 |
| State orbit | `Orbit a x y` | There exists an actual group element carrying x to y |
| Orbit quotient π: C → C/Γ | `orbitSetoid`, `OrbitQuotient`, `orbitClass` | Reflexivity, symmetry and transitivity are proved; quotient equality is equivalent to being in the same orbit |
| Γ-stable domain D | `GroupStable a D` | Every group transform of a domain member is also in D |
| Assay equivariant on D | `EquivariantOn a b D Φ` | Equivariance is required for domain members, without assuming it outside D |
| Factorization on D | `FactorsOn a D Φ` | An actual map from the constructed global orbit quotient agrees with Φ only on D |
| Φ(γc) = Φ(c) | `factor_invariant` | Derived using quotient equality and membership of both c and γc in D |
| γ·Φ(c) = Φ(c) | `factor_fixed` | Derived from quotient invariance and restricted assay equivariance |
| Every channel orbit is trivial | `factor_singleton` | Actual output orbit membership is exactly equality to the original channel |
| Contingent assignment excluded | `factor_no_contingency` | Excludes the necessary nontrivial-channel-orbit clause, retaining other scientific conditions separately |
| Output information must survive the erasure | `nontrivial_prevents_factorization` | Under the same domain/equivariance conditions, a nontrivial channel orbit rules out the stated factorization |
| Reachable domain | `Reachable P R` | Finite admissible paths starting in the declared preparation predicate P |
| Preparation and transitions preserve domain symmetry | `reachable_stable` | Derived by induction from stable P and an equivariant binary transition relation R |
| Equivariant intervention family | `FamilyEquivariant`, `AllowedStep`, `reachable_family_stable` | Group transforms transport intervention labels; individual named interventions need not each commute with the action |

## Proof correspondence

1. `inverse_act_act`, `orbit_symm` and `orbit_trans` establish that the actual
   orbit relation is an equivalence relation. `orbit_class_eq_iff` checks that
   the constructed quotient identifies precisely those states, and
   `orbit_class_act` derives π(γc) = π(c).
2. The factorization witness supplies Φ(c) = bar(π(c)). Stability supplies
   D(γc), so the same equality also applies at γc. Equality of the quotient
   classes then gives Φ(γc) = Φ(c). Neither input-state fixedness nor
   output fixedness is supplied as a premise.
3. Restricted equivariance identifies Φ(γc) with γ·Φ(c). The channel is
   therefore fixed, its orbit is a singleton, and its nontrivial-orbit
   contingency clause is impossible. The endpoint uses the paper's
   constructed inverse challenge/response channel action.
4. Reachability stability follows by induction on admissible finite paths.
   The prepared origin is transported using stable preparation; every step
   is transported using the transition relation. For labelled intervention
   families, the union of allowed steps is equivariant because the transformed
   label remains in that family. `reachable_least` supplies the closure
   principle used to verify counterexamples.

## Boundary checks and limits

Nine test theorems cover a proper stable domain containing nonfixed input
states whose erased channels are fixed; a nonfixed channel outside that
domain; an unstable conditioned singleton with equivariance and factorization
but a nontrivial channel orbit; failure without assay equivariance; failure
without factorization; identification of precisely the same state orbits;
reachability under transported intervention labels; empty preparation; and
loss of reachable-domain stability without transition-family equivariance.

The stable-domain condition is explicit and is not inferred for an arbitrary
conditioned realized state. The factorization witness is an input about the
assay's information content, not a proof that a physical system has that
property. Equality of arbitrary-valued response functions suffices for the
argument; probability normalization and scientific admissibility remain
separate. Finite challenge sets and a nontrivial group can be supplied when
instantiating the paper's assay; the equality theorem itself also holds for
larger challenge types and trivial groups.

`Reachable` describes finite compositions of the declared transition relation.
It asserts no measurable path law, stochastic support certification, or
continuous-time accumulation limit. Those results require their own models.
Theorem 1's stochastic branch remains `NOT_FORMALIZED`.

The 20 new main declarations and nine new boundary tests are individually
audited. All definitions and transitive constants are replayed with the same
official Lean kernel, before and after a source-only cold rebuild. Theorem 2
depends only on standard `Quot.sound`; the exact orbit-identification lemma
also uses standard `propext`. No custom logical dependencies are introduced.
The ten prior Theorem 13–16 and Theorem 1 proof/test files retain their hashes.

Semantic correspondence was reviewed by the assisting AI, without independent
human certification. Completion is five numbered endpoints (Theorems 2 and
13–16) plus the deterministic branch of Theorem 1, with no new research-theorem
credit and no whole-paper certification.
