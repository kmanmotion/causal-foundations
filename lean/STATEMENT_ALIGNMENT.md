# Theorem 13: paper-to-Lean alignment

Baseline: published v1.0, DOI 10.5281/zenodo.22902457, main PDF pp. 19–20,
section 10.2. The main Markdown source is identified by SHA-256
`69eaa11b00d9b2ae16df228237983a6330457d042afdb2cf886cd0dbddb00cec`.
The PDF SHA-256 is
`880ac4d4d6120b0b803adf0267f0476c505528e6e8c3eb8334c3e3e6327f996b`.

| Published object / condition | Lean object / condition | Scope check |
|---|---|---|
| Commutative resource monoid `(M,+,0)` | `CommResourceMonoid M` | Arbitrary carrier universe; associativity, commutativity and both identity laws explicitly supplied |
| Cancellativity | `LeftCancellative R` | Left cancellation suffices in a commutative monoid; not assumed for the necessity direction |
| Algebraic preorder `x ≼ y` iff `∃ r, x+r=y` | `Decomposes R x y` | No numerical order, positivity, division, subtraction or scalar resource is imported |
| Initial stock `B₀` | `initial : M` and `stock 0 = initial` | Initial condition is checked, not omitted |
| Demand `C_t`, inflow `I_t` | `demand inflow : Nat → M` | Arbitrary streams; only indices in the finite horizon are used |
| Empty sums equal zero | `prefixSum R x 0 = R.zero` | Both empty-prefix identities included |
| `C^[t] = Σ_{u=0}^{t-1} C_u` | recursive `prefixSum` | Step `t+1` appends exactly the time-`t` entry |
| Finite horizon of `N` transitions | `horizon : Nat` | Balances at `t<N`; prefix constraints at `t≤N`; includes `N=0` |
| Existence of sequential residual stocks | `SequentialFeasible` | A stock path is existentially constructed; values beyond `N` are unconstrained and irrelevant |
| All aggregate prefixes decomposable | `PrefixFeasible` | Includes terminal prefix `N`, not only `t<N` |
| Published equivalence | `CausalFoundations.theorem13` | Both implications proved at the published abstract algebraic level |

## Proof correspondence

1. Necessity uses `cumulative_balance`: induction telescopes the stated local
   balances into `C^[t] + B_t = B₀ + I^[t]`. The current stock witnesses
   decomposability. This implication does not need cancellation.
2. Sufficiency chooses one residual for each feasible prefix. At zero, the
   identity laws force that residual to equal the initial stock. The helper
   `balance_of_adjacent_prefixes` compares consecutive prefix equations and
   cancels exactly the common cumulative demand, yielding the local balance.
3. `Classical.choice` is a standard logical dependency of this existential
   implementation, not a new physical or algebraic assumption. It is reported
   explicitly. No self-declared axiom, unproved theorem input, omitted proof or
   native-evaluation axiom is used.
4. `residual_unique`, `residual_prefix_locality` and `sequential_stock_unique`
   check that the residual is uniquely fixed by current prefix data. These are
   auxiliary consequences, not separately credited new research results.
   The arbitrary-monoid online-policy equivalence of Theorem 14 is formalized
   separately; see THEOREM14_ALIGNMENT.md. No measurable/continuous/computable
   selector is asserted by either endpoint.

## Boundary tests

- A nonzero example has natural-number stock 3 and demand/inflow 1 at every step,
  for every finite horizon. It prevents an empty hypothesis class from being the
  only illustrated use of the theorem.
- The zero-horizon case has no transition obligation.
- The three-element truncated-addition monoid, with initial stock 1 and moves
  `(demand,inflow)=(1,0),(2,1)`, satisfies all prefixes through time 2 but has no
  sequential stock path. This formalizes the target-monoid obstruction described
  in section 11.3. The separate quotient-homomorphism claim is not formalized.
- An intentionally false equality `2=3` must fail compilation. It is a rejected
  negative test, never imported as part of the theorem library.

## Excluded promotions

No finite-sample check is substituted for the universal proof. Cancellation is
not claimed necessary for every prefix-complete monoid. No result about energy,
thermodynamic dissipation, infinite-horizon stochastic survival, biochemical
realization, origin of coding, or later research is credited by this T13 proof.
The separate Theorem 14 proof is documented in THEOREM14_ALIGNMENT.md.
Semantic alignment here is reviewed by the current assistant, not independently
peer-reviewed or itself automatically established by Lean.
