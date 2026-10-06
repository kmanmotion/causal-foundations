# Theorem 16: paper-to-Lean alignment

Baseline: *Causal Foundations and Experimental Certification of Contingent
Assignment, Heredity, and Reflexive Maintenance*, v1.0,
[DOI 10.5281/zenodo.22902457](https://doi.org/10.5281/zenodo.22902457),
main text section 12.5, page 23. The statement was checked against the
rendered published page. The PDFs and publication commit remain locked in
`SOURCE_LOCK.json`.

The endpoint `CausalFoundations.theorem16` constructs the order isomorphism
of sufficient semantic classes and proves both directions of minimal-class
and maximal-conjunction-domain invariance. It reuses the actual quotient,
partial orders and domain-maximality definition proved for Theorem 15.

| Published condition or conclusion | Lean representation | Meaning |
|---|---|---|
| Bijection between ambient model classes | `Transport.models : Bijection {x // A x} {y // B y}` | Both inverse laws; membership is encoded by each subtype; the model carriers may differ |
| Bijective atom transport | `Transport.atoms : Bijection (Fin m) (Fin n)` | Every declared atom has exactly one corresponding atom, with both inverse laws |
| Preserve and reflect target | `Transport.target_iff` | Target truth is equivalent at corresponding ambient models |
| Preserve and reflect each atom | `Transport.atom_iff` | Atom truth is equivalent at corresponding ambient models and indices |
| Transport a basis | `pushBasis t S` | Pull its membership predicate back along the inverse atom map |
| Induced semantic class map | `classMap t` | Quotient lift justified by preservation of semantic equivalence |
| Sufficient-basis order isomorphism | `sufficientOrderIso t` | Explicit forward/backward maps, both inverse laws and order preservation/reflection |
| Minimal bases | `minimal_transport` | Equivalence of `MinimalSufficient` at transported semantic classes |
| Maximal theorem domains | `maximal_domain_transport` | Equivalence of `MaximalSufficientDomain` for transported bases |

## Proof correspondence

1. `reverse` constructs the inverse semantic transport. `basis_pull_push`
   and `basis_push_pull` establish both round trips on every syntactic basis.
2. `holds_push_iff` and `domain_push_iff` transport conjunction truth and
   ambient domain membership. `ambient_forall_transport` uses surjectivity
   to cover every target ambient model. This proves transport of semantic
   equivalence, domain inclusion and sufficiency in both directions.
3. `classMap` is constructed by quotient lifting. Its two inverse laws are
   proved by quotient induction, not assumed. `class_order_transport` proves
   order preservation and reflection using the same reverse domain-inclusion
   order as Theorem 15. `semanticOrderIso` packages these results.
4. `class_sufficient_transport` permits restriction to sufficient subtypes;
   `sufficientOrderIso` has both inverse laws and the order equivalence.
   Its bijectivity supplies the preimage of every competing sufficient class.
5. `minimal_transport` compares all sufficient weaker classes in each
   representation. Theorem 15's minimal/maximal equivalence then proves
   `maximal_domain_transport`. Maximality concerns the transported finite
   library's conjunctions, including empty conjunctions.

## Scope and verification

The formalization requires a bijection only between ambient subtypes. It
imposes no additional condition on excluded carrier points. There is no claim
that arbitrary representations are equivalent: the declared model/atom
bijections and truth equivalences must first be supplied. They do not establish
the library's scientific admissibility, experimental realization or historical
provenance. No least sufficient class or existence of a nonvacuous basis is
asserted. Domains in different carriers correspond through the model map;
they are not identified as literally equal sets across types.

Nine boundary-test theorems exercise a Boolean model flip, atom-index swap
and a different carrier (`Option Bool`), with its unmatched `none` point
excluded. A concrete minimal basis transports to a minimal class and maximal
domain. Empty ambient classes and zero-atom libraries are also admitted.
Counterexamples show insufficiency of one-way atom preservation, changing
the target, or omitting surjectivity of the ambient model map. A two-atom
library cannot be bijectively merged into one atom.

The endpoint's transitive dependencies are exactly the standard `propext`
and `Quot.sound`. The 18 new main theorem declarations and nine new test
theorems are individually audited. Every definition, structure and imported
constant is included in the fresh kernel replay, both before and after a
source-only cold rebuild. The Theorem 13, 14 and 15 proof/test files retain
their prior hashes. The runner also handles multiline dependency output while
still enforcing the complete expected declaration set and dependency list.

Replay uses the same official Lean kernel; semantic alignment is reviewed by
the assisting AI, without independent human certification. This package
formalizes published Theorems 13–16. The remaining paper and supplementary
obligations remain outside its completion claim. No new research theorem is
credited by formalizing this published result.
