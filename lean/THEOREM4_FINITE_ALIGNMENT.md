# Theorem 4: finite matching foundations (v0.8.0)

Published source: *Causal Foundations and Experimental Certification of
Contingent Assignment, Heredity, and Reflexive Maintenance*, v1.0,
DOI 10.5281/zenodo.22902457, section 3.4, pages 6-7. The three PDF hashes remain
those in `SOURCE_LOCK.json`. This is a formalization of published structural
arguments, not a new mathematical discovery or a change to the paper.

**Theorem 4 status: PARTIAL.** Only the finite structural foundations listed
below are complete, conditional on verification for the exact source commit.
The full stochastic genesis theorem is **NOT_FORMALIZED**.

## Representation and proved correspondence

`FiniteMatching.Matching n` is a function from the input copy of `Fin n` to
`Option (Fin n)` with a proved column-uniqueness condition. The graph relation
`Link M u v` is exactly `M.partner u = some v`. Thus each input has at most one
partner and each output occurs at most once. `none` is one common null response,
not an input-dependent label. Input and output permutations are independent;
using the same indexing type for the two finite carriers does not constrain
them to a diagonal relabeling.

| Published structural object or assertion | Formal construction / proof |
|---|---|
| All permutations on both finite carriers | `Permutation`, `relabelGroup`; explicit inverse and group laws |
| Empty origin, no links, no preferred admissible pair | `empty_no_links`, `empty_all_pairs_admissible`, `empty_fixed` |
| Relabel both endpoints of a link | `transport_link_iff`, `stateAction` |
| Both endpoints must be unmatched before adding a link | `Admissible`, `extend`, `extension_exact_link` |
| Genesis extensions respect the independent relabelings | `extend_transport`, `genesis_step_transport` |
| Each extension changes the actual state and preserves existing links | `genesis_step_changes_realized_state`, `genesis_step_preserves_links` |
| Frozen challenged readout returns partner or common null | `assay`, `assay_unique_response`, `empty_assay_common_null` |
| Readout obeys the paper's inverse channel action | `assay_equivariant`; the response action fixes `none` |
| Single-realized-link removal deletes exactly that graph edge | `ablate_exact_link`; other challenged responses are unchanged |
| Realized-link removal changes its challenged response | `realized_link_ablation_changes_response` |
| Removing the newly added link recovers the previous state | `extension_ablation_recovers` |
| Ablation is a transported organization intervention | `ablate_transport` |
| Finite sequences of deletions cannot add an origin link | `empty_deletion_minors` |
| Perfect means every input and every output is matched | `Perfect`; `perfect_iff_permutation` proves equivalence with permutation graphs |
| All perfect organizations are symmetry-related | `perfect_matchings_same_orbit` |
| Each perfect organization's challenged link can be ablated | `perfect_each_challenge_ablatable` |
| At least two contingently different perfect organizations for n >= 2 | `at_least_two_contingent_matchings` |
| A perfect organization has a nontrivial readout-channel orbit | `perfect_channel_has_nontrivial_example` |

The bundled endpoint is
`CausalFoundations.FiniteMatching.finite_matching_foundations`.
The response channel is the deterministic event channel `partner u = r`, with
one true response for each input. It is not presented as a newly formalized
probability kernel. `perfectPermutation` uses ordinary set-theoretic choice to
recover a permutation from an already perfect matching; it does not install
that permutation in the empty origin or in an extension rule.

## Boundary and counterexample checks

The 12 test theorems cover the empty carrier, lack of contrast in an empty
origin, deletion-only origin minors, two distinct perfect organizations,
forbidden input/output reuse, actual state change, exact ablation and unaffected
other challenges, exclusion of many-to-one rows, inverse input transport under
a three-cycle, the singleton-carrier contrast boundary, and a nontrivial
two-carrier readout orbit. Finite decisions are checked by the Lean kernel;
there is no native-evaluation proof dependency.

## Exact incomplete obligations

No statement in this module proves any of the following:

- the count `(n-k)^2` of available pairs after `k` links;
- a uniform next-pair probability, a positive rate parameter, or a CTMC law;
- exponential holding times or their independence;
- almost-sure attained first entry into the perfect matchings;
- the expectation `lambda^-1 * sum (j=1..n) j^-2`;
- a uniform terminal permutation or a positive finite-horizon hit probability;
- the complete assay-complete origin-minor audit (only link deletions are modeled);
- heredity, reflexive maintenance, resource admissibility, chemistry or history.

The next work package is exact finite counting and finite extension paths,
followed by the probability-law and waiting-time obligations. Theorem 1's
stochastic branch remains a separate unfinished obligation.

The 37 new main declarations and 12 new test declarations are audited against
the explicit registry and replayed with the same pinned Lean kernel. Only the
standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` are
allowed. Paper-to-code alignment was reviewed by the assisting AI and is not
independent external certification.
