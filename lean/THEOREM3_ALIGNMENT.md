# Published Theorem 3 — equal-orbit first hitting

Baseline: Causal Foundations v1.0, §3.3, main-paper page 6,
DOI 10.5281/zenodo.22902457. The three frozen PDF hashes remain in
`SOURCE_LOCK.json`. Alignment is the assisting AI's review; no independent
human review is claimed.

Endpoint: `CausalFoundations.theorem3` in
`probability/CausalFoundationsProbability/FirstHitting.lean`.

| Published object or premise | Formal binding |
|---|---|
| Finite group Γ with actions on paths, states and finite nonempty Θ | Existing `SymmetryGroup` and `Action`; endpoint has `Fintype Γ`, `Fintype Θ` and `Nonempty Θ` |
| Actions are measurable; time is unchanged | `path_measurable`, `state_measurable`; `process_equivariant` uses the same time argument |
| Finite horizon and actual visits | `Visit` requires `0 ≤ t`, `t ≤ horizon`, and membership in an actual orientation cell; `Hit` existentially quantifies visits |
| Natural or nonnegative real time | Generic linearly ordered time includes ℕ and ℝ; the real window `0 ≤ t ≤ T` is the paper's nonnegative time restriction. The declared horizon is an ordinary finite natural/real value |
| Measurable, pairwise disjoint, transported cells | `cells_measurable`, `cells_disjoint`, `cells_transport`; transport is membership equivalence under the constructed actions |
| Transitive finite orientation orbit | `transitive` supplies a group element connecting any pair of labels |
| Measurable hit event | `hit_measurable`; it is an explicit premise for real time, not inferred from an uncountable union |
| Invariant null exception set N | `exceptional_null`, `exceptional_invariant`; a measurable N is not additionally required |
| Actually attained first entry outside N | `attained` supplies a time in the visit window and proves that it is no later than every other visit, together with the cell and label at that time |
| Measurable extended time and orientation | `time_measurable`, `orientation_measurable`; time uses the declared time space plus a separate measurable infinity point, and finite orientation labels have the discrete space |
| Cemetery extension | Time is top and orientation is `none` outside `Hit`; genuine labels are `some θ`. Values on exceptional hits in N are unrestricted |
| Invariant complete path law | An actual Mathlib `Measure Ω` with `IsProbabilityMeasure μ` and `μ.map (pa.act g) = μ`; no equality of label masses is assumed |
| Equal first-hit probabilities | `μ (labelEvent D θ) = μ Hit / Fintype.card Θ`, with `labelEvent = Hit ∩ {orientation = some θ}` |
| Uniform conditional orientation | `conditionalOrientation` is the event-probability ratio. `conditional_uniform` requires strictly positive hit probability; finiteness follows from the probability-measure instance |

The proof transports visits and actual minima first. Uniqueness of the minimum
gives time invariance, and disjoint cells give orientation equivariance. The
invariant exception set and cemetery extension give these identities outside N,
including non-hits. Label-event preimages agree almost everywhere; exact equality
on N is not assumed. Measure pushforward invariance then gives equal label-event
probabilities. Transitivity identifies every label probability. The label events
are disjoint and their union agrees with `Hit` after deleting N from both;
removal of N preserves both probabilities. A finite sum gives the cardinal denominator. Division by the
hit probability occurs only in the positive-hit conditional theorem.

The stronger auxiliary equal-mass statement works for an arbitrary invariant
measure; the published endpoint includes probability normalization and finite Γ.
Finiteness of Γ is not needed for the core argument once the finite transitive
orientation set and the specified actions are present.

The executable boundary examples include a genuine invariant probability measure
on two paths, first hit at time zero and probability one half for each orientation.
They separate ensemble invariance from a fixed realized path, expose biased path
laws and nontransitive actions, and show that a nonzero exception mass cannot be
discarded. A four-path model adds a nonempty invariant null exception set,
retains nontransported labels on its exceptional hits, and still gives probability
one half for each orientation. Discrete visits attain a minimum by natural-number well ordering.
The real path `X(t)=t` visiting the open cell `(0,∞)` in `[0,1]` has no first entry:
any positive candidate admits an earlier positive visit at half its time.

This formalization does not derive actual attainment from continuity, construct
a CTMC, prove Theorem 4, or prove Theorem 1's stochastic branch. Statistical,
physical, chemical and historical premises remain separate. Published PDFs and
the v1.0 publication record are unchanged.
