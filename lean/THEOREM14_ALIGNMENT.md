# Theorem 14: paper-to-Lean alignment

Baseline: *Causal Foundations and Experimental Certification of Contingent
Assignment, Heredity, and Reflexive Maintenance*, v1.0,
[DOI 10.5281/zenodo.22902457](https://doi.org/10.5281/zenodo.22902457),
main text sections 11.1–11.2. The public PDF hashes and original publication
commit are locked in `SOURCE_LOCK.json`.

The endpoint is `CausalFoundations.theorem14` in
`CausalFoundations/ResidualGame.lean`. It proves both `WinningPolicies ↔ AllRoots`
and `AllRoots ↔ ViableSubfibers`, which express the three equivalent conditions.
The four implications are separately named and audited.

| Published object or condition | Lean representation | Scope |
|---|---|---|
| Arbitrary commutative monoid `(M,+,0)` | `CommResourceMonoid M` | Arbitrary carrier universe; no cancellation, idempotence, finiteness or numeric order assumed |
| Residual state `(a,b,r)`, with `a+r=b` | `CRK.State M` and `CRK.Omega R` | `Invariant` requires every member to satisfy the equation |
| Aggregate-admissible current move `(c,i)` | `CRK.admissible R x m` | Exactly `∃q, (a+c)+q=b+i`; depends on aggregate totals, not on a guessed future |
| Legal successor residual | `CRK.legal R x m s` | Exactly `r+i=c+s` |
| Successor state | `CRK.next R x m s` | Exactly `(a+c,b+i,s)` |
| Residual-invariant subset | `CRK.Invariant R W` | `∀x∈W, ∀ current admissible m, ∃s` legal and remaining in `W` |
| Union of every residual-invariant subset | `CRK.Wmax R x` | Membership means existence of an invariant set containing `x`; `wmax_invariant` proves closure of the union |
| Stream of demands and inflows | `CRK.Stream M = Nat → Move M` | Infinite discrete streams; every aggregate prefix must be feasible |
| General nonanticipating stock policy | `CRK.Policy M` and `CRK.Nonanticipating` | Stock after `t` moves agrees on all streams agreeing at indices `k<t`; arbitrary past dependence and time dependence are allowed |
| Universal winning policy | `CRK.WinningPolicies R` | `∀ initial b, ∃ one policy π` with nonanticipation, initialization and balance for every aggregate-feasible stream and every time |
| Every root lies in the union | `CRK.AllRoots R` | `∀b, Wmax R (0,b,b)` |
| Nonempty viable residual subfibers | `CRK.ViableSubfibers R` | One family `V(a,b,r)`; nonempty for every decomposable pair, contained in `a+r=b`, and closed across all admissible moves |

## Information and quantifier order

`π σ t` is stock **after** moves `0,…,t-1`. The response to current move `σ t`
is `π σ (t+1)`, so the current move is available when choosing its response.
`Nonanticipating` states that identical observed prefixes give identical stock.
Although policies are represented as functions of full streams for comparing
prefixes, the required equality forbids using unseen future entries. This does
not assume a memoryless policy or interchange `∃ policy ∀ stream` with
`∀ stream ∃ policy`.

## Correspondence of the four implications

1. **Policy ⇒ roots.** `Reachable` collects states along all feasible streams
   under the given general policy. To admit an arbitrary current move, `extend`
   preserves the observed past, inserts that move, and uses zero moves afterward.
   `extend_allPrefixes` proves that this is an aggregate-feasible infinite stream.
   Nonanticipation keeps the current stock unchanged; winning supplies a legal
   reachable successor. Thus `reachable_invariant` and `winning_root` follow.
   This supplies the continuation argument explicitly, rather than assuming that
   an arbitrary finite history has a feasible infinite extension.
2. **Roots ⇒ policy.** `response_spec` chooses a legal successor for each viable
   state/current-move pair. `play` recursively applies this one state-based
   selector. Prefix induction proves nonanticipation, invariant induction proves
   viability, and `memoryless_winning` proves all balances. The stronger
   `roots_imply_memoryless` yields one selector working from every root. The
   reduction from general history-dependent policies to memoryless ones is
   therefore proved as a consequence, not inserted into the first condition.
3. **Roots ⇒ subfibers.** `roots_imply_subfibers` applies move `(a,0)` at root
   `(0,b,b)` whenever `a` is decomposable from `b`. This proves nonempty fibers
   `V(a,b)={r : (a,b,r)∈Wmax}`. Invariance proves cross-fiber closure.
4. **Subfibers ⇒ roots.** `subfibers_imply_roots` forms the invariant union of
   the fibers. At `(0,b)`, the identity law forces every residual to equal `b`,
   placing each root in that invariant set and hence in `Wmax`.

## Boundary tests and limits

`ResidualGameTests.lean` proves that the published three-element truncated
monoid has no viable root at stock one, and hence no universal winning policy.
It also constructs viable subfibers for Boolean disjunction, proves the monoid
is noncancellative, and derives its universal winning policies. These finite
examples check opposite sides of the characterization; the main endpoint is a
universal proof over arbitrary monoids, not an enumeration of those examples.

Theorem 14's transitive standard logical dependencies are `propext`,
`Classical.choice`, and `Quot.sound`. The verifier checks these explicitly and
rejects omitted proofs and custom dependencies. The chosen selector has no
asserted measurability, continuity, computability or efficiency. Fresh replay
uses the same Lean kernel, not a separately implemented verifier. The semantic
alignment above is an AI-assisted review, not independent human certification.
No physical, chemical or historical realization claim follows from this code.
