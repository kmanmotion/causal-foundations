# Theorem 1: deterministic branch alignment

Baseline: *Causal Foundations and Experimental Certification of Contingent
Assignment, Heredity, and Reflexive Maintenance*, v1.0,
[DOI 10.5281/zenodo.22902457](https://doi.org/10.5281/zenodo.22902457),
main text section 3.1, page 5, and the channel action in section 2.3, page 3.
The statement was checked against the rendered published page. The three
PDFs and publication commit remain bound by `SOURCE_LOCK.json`.

`CausalFoundations.theorem1_deterministic` proves the complete **pointwise
deterministic branch**. The stochastic branch of this same numbered theorem
remains **NOT_FORMALIZED**, so Theorem 1 as a whole is only **PARTIAL**.

| Published object or claim | Lean representation | Binding |
|---|---|---|
| Symmetry group Γ | `SymmetryGroup Γ` | Explicit associativity, identity and both inverse laws |
| Group action | `Action G X` | Identity and product action laws; state/challenge/response actions use the same group |
| Exactly fixed realized state | `Fixed a x` | Every group element fixes this particular state |
| Channel Q(b given a) | `Channel Challenge Response Value` | Challenge argument first, then response; arbitrary values because the proof uses equality only |
| Induced channel action | `channelAction` | Constructed inverse relabeling of both challenge and response arguments; action laws proved |
| Assay equivariance | `Equivariant a (channelAction ac ar) Φ` | Exactly `Φ(γx) = γ·Φ(x)` |
| Trivial orbit | `fixed_iff_singleton_orbit` | Every orbit element equals the original channel, and conversely |
| Contingency exclusion | `ContingentWith b Φ other x` | Nontrivial channel orbit together with an arbitrary predicate for the remaining scientific conditions |
| Deterministic evolution F(t) | `F : Time → State → State`, `hF` | Exact equivariance for every supplied time; no extra flow, continuity or invertibility assumption |
| Fixed-set preservation | `evolution_fixed` | Every exactly fixed origin is fixed at every declared deterministic time |
| Evolved channel fixedness | `evolution_channel_fixed` | Requires both evolution and assay equivariance |
| Constructed update trajectory | `trajectory`, `trajectory_equivariant`, `trajectory_fixed` | Recursion over time-dependent deterministic steps; preservation proved for every natural-number index |

## Proof correspondence

1. The elementary group inverse identities are derived from the stated group
   laws. `channelAction` implements the published inverse argument transport;
   its identity and product laws are derived using these inverse identities
   and the challenge/response action laws.
2. `equivariant_fixed` proves `γ·f(x) = f(γ·x) = f(x)`. No orbit-collapse
   hypothesis is supplied. `fixed_iff_singleton_orbit` proves actual orbit
   membership is exactly equality to the original point.
3. `assay_fixed` and `assay_fixed_formula` apply this argument to the
   constructed channel action. `fixed_no_contingency` rules out a nontrivial
   channel orbit regardless of the other assignment conditions.
4. `evolution_fixed` applies the same argument to each supplied deterministic
   evolution map. The assay proof then applies to the evolved state. The
   endpoint explicitly packages origin and evolved-state fixedness, singleton
   channel orbits, and contingency exclusion.
5. `trajectory_equivariant` constructs equivariance of every finite
   composition of time-dependent deterministic steps. `trajectory_fixed`
   and `trajectory_channel_fixed` derive simultaneous preservation for all
   natural-number indices by deterministic recursion, without any probability
   or conditional-kernel claim.

## Boundary checks and limits

Eight audited test theorems check an exactly fixed `none` origin with
nontrivial Boolean symmetry and an equivariant sequence of flips; a fixed
channel that still has response contrast; a nonfixed origin with a nontrivial
channel orbit; invariant equal weights with no individually fixed Boolean
realization; failures without assay or evolution equivariance; a three-cycle
where inverse relabeling is distinct from forward relabeling; and the trivial
group boundary. Equal-weight invariance is a finite algebraic witness, not a
new measure-theoretic certification.

The abstract group theorem also holds for trivial groups and empty fixed sets;
it asserts no existence of an exactly fixed origin. A nontrivial group can
be supplied when binding the paper's assay. `ContingentWith` retains the
necessary nontrivial-orbit clause and leaves all remaining scientific
conditions separate. It does not define operational assignment by symmetry
alone, establish experimental membership, or rule out an invariant channel's
challenge-response contrast. Probability normalization is unnecessary for
this equality argument and is not claimed proved by the generic value type.

The stochastic branch still requires adapted random states, measurable fixed
sets, actual conditional update kernels, the fixed-set support condition,
conditional-expectation induction and a countable union of null events. None
of these is replaced by the deterministic recursion. No continuous-time
stochastic path or accumulation-time conclusion is asserted.

The 19 new main declarations and eight new test theorems are individually
audited, and all definitions and transitive constants are freshly replayed
before and after a source-only cold rebuild. The deterministic endpoint uses
only the standard `Quot.sound` (via function extensionality in the channel
action); it has no custom logical dependencies. The eight Theorem 13–16
proof/test files retain their prior hashes.

Replay uses the same official Lean kernel. Semantic correspondence was
reviewed by the assisting AI, without independent human certification.
Completion remains four numbered endpoints (Theorems 13–16) plus the
deterministic branch of Theorem 1, with no new research-theorem credit.
