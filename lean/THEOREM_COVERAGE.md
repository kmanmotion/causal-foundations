# Published-paper formalization inventory — v0.1.0

Baseline: Causal Foundations v1.0, DOI 10.5281/zenodo.22902457.
This is a source-bound implementation inventory, not a fresh proof audit of all
entries. `COMPLETE` below is conditional on a passing `verification/run/results.json`
for the exact delivered source hash. All other entries remain `NOT_FORMALIZED`.
The current assistant performed the semantic reading; no independent reviewer is
claimed. Dependencies below describe mathematical needs, not a claim that the
corresponding mathlib API has already been found or tested.

## Sixteen numbered main-text theorems

| ID; main-text location | Target and indispensable scope | Principal formal dependencies | Status |
|---|---|---|---|
| T01; §3.1 | Equivariant maps/evolution preserve exactly fixed realized states; the separate stochastic part is simultaneous only on the declared countable actual-update sequence | Group actions, fixed sets; actual conditional kernels, conditional expectation, measurable sets, countable null union for stochastic branch | NOT_FORMALIZED |
| T02; §3.2 | An equivariant channel factoring through the orbit quotient on a group-stable reachable domain is fixed | Group action, stable domain, quotient factorization, equality of channels | NOT_FORMALIZED |
| T03; §3.3 | Equal first-hit probabilities on a finite transitive orientation orbit | Finite group, measurable invariant path law, disjoint cells, actual attained first entry outside invariant null set, finite horizon; positive hit probability only for conditioning | NOT_FORMALIZED |
| T04; §3.4 | Empty-matching stochastic genesis with a frozen assignment assay and organization ablation | Finite partial matchings, uniform rates on unmatched pairs, CTMC holding times, combinatorial counting, declared origin ontology and assay semantics | NOT_FORMALIZED |
| T05; §4.1 | Same passive path laws can have different decoder-free provenance | Explicit emergent/dormant witness pair; equality of observed path measures; randomized-test indistinguishability; supplement S1 | NOT_FORMALIZED |
| T06; §4.2 | Adaptive input-only control does not universally identify hidden provenance | T05 witness interface, adaptive policy measurability, induction/coupling of transcripts; no hidden-organization inspection; S2 | NOT_FORMALIZED |
| T07; §5.2 | Descendant TV contrast is bounded by Dobrushin coefficient times cut-state TV contrast | One common downstream screening kernel, signed measures, TV duality, oscillation, iterated contraction | NOT_FORMALIZED |
| T08; §5.3 | Aligned distributional causal heredity | H0*, H1*, H23*, H5† including joint context matching, stable structural mechanism and noise/context separation; S4.0 | NOT_FORMALIZED |
| T09; §6.2 | Signed support-capacity contrast and its oscillation–TV bottleneck bound | Common screening kernel, fixed measurable capacity event, event-probability transport, T07-style TV argument | NOT_FORMALIZED |
| T10; §8.1 | Positive conditional exit floor forbids permanent named orientation and bounds its mean exit time | Discrete epochs, hazard floor 0<r≤1, tail induction, infinite-event limit, tail-sum expectation | NOT_FORMALIZED |
| T11; §8.4 | Strict margins persist in a sufficiently small neighborhood of the same structural class | Finite diagnostic family, locally Lipschitz bounds, positive margins/locality radii, zero-Lipschitz convention | NOT_FORMALIZED |
| T12; §8.5 | Local finite-dimensional nonnegative parasite dynamics: subcritical decay, supercritical first-order direction, critical non-decision | Equivalent norm, spectral radius/Perron–Frobenius facts, little-o remainder, cone invariance; S20 | NOT_FORMALIZED |
| T13; §10.2, pp.19–20 | Finite sequential resource feasibility iff all aggregate prefixes are decomposable in a commutative cancellative monoid | Explicit monoid laws, finite-prefix recursion, cancellation, existential selection; source alignment in STATEMENT_ALIGNMENT.md | COMPLETE — pilot endpoint |
| T14; §11.2 | Nonanticipating winning policies iff every root lies in the maximal residual invariant iff viable residual subfibers exist | Arbitrary commutative monoid, residual game, invariant-union closure, reachable histories, set-theoretic successor choice; measurable selection NOT automatic | NOT_FORMALIZED |
| T15; §12.2 | Semantic sufficient-basis quotient poset; minimal classes correspond to maximal conjunction-generated domains | Finite declared premise library, ambient semantic entailment, equivalence quotient, order/upper set, reverse inclusion | NOT_FORMALIZED |
| T16; §12.5 | Representation-invariant sufficient-basis posets under declared semantic transport | T15 objects; bijections preserving/reflecting ambient membership, target and every premise atom | NOT_FORMALIZED |

## Important unnumbered results and supplementary obligations

These entries prevent “16/16” from being misreported as full-paper coverage.
They are grouped work packages, not a claim that all proof obligations in the
supplement have been enumerated. Every group below remains NOT_FORMALIZED except
the explicitly isolated boundary test in U21.

| ID | Location | Result family / further dependency |
|---|---|---|
| U01 | §2.2 | Future-interventional signature equivalence and refinement by sufficient statistics |
| U02 | §§2.3–2.4 | OA/contingency/origin verdict invariance under the fully specified assay- and origin-preserving transport |
| U03 | §2.4 | Diagnostic completeness, null audit and its ontology-relative contraposition; no automatic diagnostic completeness |
| U04 | §4.3; S3 | DFI-A certificate, actual surgical channel identity, null origin, matched nuisance, deletion and bypass countermodels |
| U05 | §6.4; S5, S16 | DFI-R(loop): stable support/maintenance kernels, aligned contexts and standardized next-support re-entry |
| U06 | §6.5; Supplement Part II | DFI-R(cap): actual future-signature binding, natural sham, support-state realization, RASM+, positive actual capacity effect |
| U07 | Proposition 1; S18.1 | Heredity and reflexive maintenance are non-equivalent; both explicit directions |
| U08 | §7.4; S17 | UCCE exact assembly on one fixed datum, structural embedding, regime closure, kernel/context identities and one global acyclic atlas |
| U09 | §7.5; Supplement Part III | Full finite joint non-vacuity construction with its entire intervention atlas; genesis-only symmetry scope |
| U10 | §§7.1–7.2; S6, S18.3 | Baseline binding, kernel selection, probability gluing, causal-cycle and ordering obstructions with their different premises |
| U11 | §8.2 | Two-sided exit-hazard tail bounds; no universal finite-size scaling without hazard assumptions |
| U12 | §8.3 | Markov-error contraction and exact identical-row-mixture attenuation; no model-uniform positive error radius |
| U13 | §9.3; S7 | Zero required-law TV error does not establish hard structural fidelity |
| U14 | §9.4; S11 | Local margin erosion for distinct A/H/R(loop)/R(cap) diagnostics |
| U15 | §9.5; S8–S10 | Matched-branch model error, rare-cell protocol amplification and realized continuation/binding bounds |
| U16 | §9.6 | Capacity-strengthened UFE envelope retaining BOTH support-loop and actual-capacity margins |
| U17 | §9.7; S12 | Finite-alphabet IID empirical TV confidence radius via coordinate concentration and union bound |
| U18 | §9.7; S13.1–S13.2 | Whole-envelope confidence soundness, acquisition+coverage, and separately assumed quantitative power separation |
| U19 | §9.7; S13.3–S13.4 | Random cell counts and simultaneous-in-time coverage under valid sampling designs; no arbitrary stopping substitution |
| U20 | §§10.1,10.3 | No canonical resource scalar and no unconditional positive-dissipation consequence |
| U21 | §11.3 | Cancellative/idempotent branches, CRS sufficiency, isomorphism and quotient limits; only the truncated target-monoid two-step obstruction is checked in BoundaryTests.lean, NOT the quotient homomorphism or full CRK theory |
| U22 | Proposition 2; §12.1 | Unrestricted weakest antecedent is degenerate; declared noncircular premise language is essential |
| U23 | §12.3 | Definitional-library expansions versus genuinely weaker sufficient assumptions |
| U24 | S19 | Measurability of countable diagnostics, signatures, capacity and downstream probability/decision events |

## Three-volume separation

- Main text: 16 numbered theorem endpoints plus the unnumbered mathematical
  obligations above. The main PDF has 33 pages.
- Mathematical supplement: 42 pages. It carries essential condition dictionaries,
  countermodels, concentration arguments, actual-capacity proof and finite joint
  witness. It is not optional background and cannot be omitted from the coverage
  denominator by counting only numbered main-text endpoints.
- Experimental methods supplement: the fixed statistical rules link back to the
  mathematical work packages. Physical membership, calibration, addressability,
  measurements, molecular feasibility and historical claims cannot be certified
  by Lean merely by declaring them as assumptions.

## Implementation order and completion gate

1. T13 source-bound pilot (this package).
2. T14 residual-invariant characterization, with fully specified strategy and
   history semantics, reusing the monoid interface using only the published definitions.
3. Symmetry/quotient and semantic-poset blocks; split T01's deterministic and
   stochastic branches explicitly until both are proved.
4. Probability kernels, TV contraction, causal certificates and composition.
5. Robustness/statistics plus the complete finite joint witness, then a final
   theorem-by-theorem semantic alignment and dependency closure audit.

This order is a proposal for the separately authorized verification track, not a
change to the main AURORA research task. Work estimates await API/dependency
prototypes; no automatic conversion or whole-paper completion date is promised.
One pilot endpoint out of 16 numbered endpoints is NOT a meaningful percentage
of total mathematical work. No whole-paper certification is claimed.
