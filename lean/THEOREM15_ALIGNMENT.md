# Theorem 15: paper-to-Lean alignment

Baseline: *Causal Foundations and Experimental Certification of Contingent
Assignment, Heredity, and Reflexive Maintenance*, v1.0,
[DOI 10.5281/zenodo.22902457](https://doi.org/10.5281/zenodo.22902457),
main text section 12.2, page 22. The published PDF and publication commit are
locked in `SOURCE_LOCK.json`. The statement and its displayed order direction
were checked against the rendered published page.

The endpoint `CausalFoundations.theorem15` in
`CausalFoundations/SemanticBasis.lean` proves the reflexivity, transitivity and
antisymmetry of sufficient semantic classes, upward closure of sufficiency,
reverse domain inclusion, and minimal-class/maximal-domain equivalence.
The quotient and its sufficient subtype also have actual Lean core
`Std.IsPartialOrder` instances; the order is not assumed as an input.

| Published object | Lean representation | Scope |
|---|---|---|
| Ambient model class A | `A : Model → Prop` | Arbitrary model carrier universe; truth is restricted to A |
| Fixed finite library H with m atoms | `h : Fin m → Model → Prop` | Declared finite indexed library, including m=0; equivalent atom meanings are allowed |
| Subset S of H | `Semantic.Basis m = Fin m → Prop` | Every basis uses this same fixed atom library |
| Conjunction H_S | `Holds h S x` | Exactly all selected atoms; an empty conjunction is true |
| Ambient equivalence | `SemanticEq A h S T` | `∀x, A x → (Holds h S x ↔ Holds h T x)` |
| Semantic class [S]_A | `SemanticBasis A h`, `classOf A h S` | Actual `Quotient` of a proved `Setoid`, not syntactic subset equality |
| Theorem domain U_A(S) | `Domain A h S` | `A x ∧ Holds h S x` |
| Domain of a quotient class | `classDomain A h q` | Quotient lift with a proof of representative independence |
| Weak-to-strong order | `q ≤ r` | Domain(r) is included in domain(q); representative entailment proved separately |
| Sufficient basis | `Sufficient A h C S` | Every model in its domain satisfies C |
| Sufficient semantic class | `ClassSufficient A h C q`, `SufficientClass A h C` | Sufficiency descends to classes; the subtype inherits the proved order |
| Minimal sufficient class | `MinimalSufficient A h C q` | Sufficient and every sufficient class below it equals it |
| Maximal conjunction-generated domain | `MaximalSufficientDomain A h C S` | Sufficient and every sufficient library conjunction containing its domain has the same domain |

## Proof correspondence

1. `semantic_eq_refl`, `semantic_eq_symm` and `semantic_eq_trans` establish
   the equivalence relation. `semantic_eq_iff_domain_equal` identifies it
   with equality of ambient domains and validates the quotient lift.
2. `class_domain_injective` proves that equal lifted domains imply equal
   semantic classes. Reflexivity and transitivity are reverse-inclusion laws;
   antisymmetry uses domain equality and this injectivity. The sufficient
   subtype is proved partially ordered as well.
3. `sufficient_equiv` proves representative independence of sufficiency.
   `sufficient_upper` composes domain inclusion with the target implication.
4. `class_order_iff` proves the published reverse-inclusion formula;
   `class_order_entailment` checks its original ambient-entailment meaning.
5. `minimal_iff_maximal_domain` proves both directions. A larger sufficient
   domain gives a weaker sufficient class, so minimality makes the classes
   equal. Conversely, quotient induction considers every possible weaker
   sufficient class, and domain maximality plus antisymmetry makes it equal.

The library's scientific admissibility and noncircular provenance are declared
inputs, as in the paper, not consequences of an order-theoretic proof. This
module does not choose a privileged scientific premise library. It does not
assert that sufficient bases exist, that a least sufficient class exists, or
that a library-relative minimal condition is universally necessary.

## Boundary cases and limitations

Eight test theorems check: syntactically different alias bases becoming one
semantic class; a sufficient stronger basis with an insufficient empty basis;
the required weak-to-strong direction and failure of its converse; collapse
under an empty ambient class; and two sufficient branches whose disjunction
cannot be represented by any conjunction from their fixed two-atom library.
The latter witness exposes the boundary of the maximal-domain claim: expanding
the formula language requires a new semantic quotient and can enlarge domains.
It does not claim that the general library-expansion result in section 12.3
has been formalized.

Theorem 15's transitive standard logical dependencies are exactly `propext`
and `Quot.sound`. All 23 new main theorem declarations and eight new test
theorems are audited and included in `ReplayAll`. Definitions, setoids and
order instances are also checked during compilation and full constant replay.
The existing Theorem 13 and 14 proof and test sources are unchanged.

Fresh replay uses the same official Lean kernel. Semantic correspondence is
assistant-reviewed rather than independently certified. Only the published
Theorems 13, 14 and 15 are claimed formalized; no new research theorem,
whole-paper certification, or empirical/historical promotion is asserted.
