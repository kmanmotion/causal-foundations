import CausalFoundations.SemanticBasis

/-!
# Published Theorem 16: representation invariance

Source: Causal Foundations v1.0, section 12.5, page 23.
DOI: 10.5281/zenodo.22902457.

The input bijection concerns the ambient model subtypes, not the whole model
carriers. Target and atom truth are preserved and reflected on those subtypes.
The quotient maps and their order isomorphisms are constructed from this input.
Maximal domains are relative to the same transported finite atom library.
-/

namespace CausalFoundations.Representation

open Semantic

universe u v w z

/-- A bijection with both inverse laws stated explicitly. -/
structure Bijection (X : Type u) (Y : Type v) where
  forward : X → Y
  backward : Y → X
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ y, forward (backward y) = y

def Bijection.symm {X : Type u} {Y : Type v} (f : Bijection X Y) : Bijection Y X where
  forward := f.backward
  backward := f.forward
  backward_forward := f.forward_backward
  forward_backward := f.backward_forward

/-- Explicit order preservation and reflection, in addition to bijectivity. -/
structure OrderIsomorphism (X : Type w) (Y : Type z) [LE X] [LE Y]
    extends Bijection X Y where
  le_iff : ∀ x y, forward x ≤ forward y ↔ x ≤ y

/-- Every scientific predicate is supplied; the transport must satisfy both directions. -/
structure Transport {m n : Nat} {Model : Type u} {Model' : Type v}
    (A : Model → Prop) (B : Model' → Prop)
    (h : Fin m → Model → Prop) (k : Fin n → Model' → Prop)
    (C : Model → Prop) (D : Model' → Prop) where
  models : Bijection {x // A x} {y // B y}
  atoms : Bijection (Fin m) (Fin n)
  target_iff : ∀ x, C x.val ↔ D (models.forward x).val
  atom_iff : ∀ i x, h i x.val ↔ k (atoms.forward i) (models.forward x).val

variable {m n : Nat} {Model : Type u} {Model' : Type v}
  {A : Model → Prop} {B : Model' → Prop}
  {h : Fin m → Model → Prop} {k : Fin n → Model' → Prop}
  {C : Model → Prop} {D : Model' → Prop}

def reverse (t : Transport A B h k C D) : Transport B A k h D C where
  models := t.models.symm
  atoms := t.atoms.symm
  target_iff := by
    intro y
    have he := (t.target_iff (t.models.backward y)).symm
    rw [t.models.forward_backward] at he
    exact he
  atom_iff := by
    intro j y
    have he := (t.atom_iff (t.atoms.backward j) (t.models.backward y)).symm
    rw [t.atoms.forward_backward, t.models.forward_backward] at he
    exact he

def pushBasis (t : Transport A B h k C D) (S : Basis m) : Basis n :=
  fun j => S (t.atoms.backward j)

theorem basis_pull_push (t : Transport A B h k C D) (S : Basis m) :
    pushBasis (reverse t) (pushBasis t S) = S := by
  funext i
  change S (t.atoms.backward (t.atoms.forward i)) = S i
  rw [t.atoms.backward_forward]

theorem basis_push_pull (t : Transport A B h k C D) (T : Basis n) :
    pushBasis t (pushBasis (reverse t) T) = T := by
  funext j
  change T (t.atoms.forward (t.atoms.backward j)) = T j
  rw [t.atoms.forward_backward]

theorem holds_push_iff (t : Transport A B h k C D) (S : Basis m) (x : {x // A x}) :
    Holds h S x.val ↔ Holds k (pushBasis t S) (t.models.forward x).val := by
  constructor
  · intro hs j hj
    have he := (t.atom_iff (t.atoms.backward j) x).mp (hs _ hj)
    rw [t.atoms.forward_backward] at he
    exact he
  · intro ht i hi
    apply (t.atom_iff i x).mpr
    apply ht (t.atoms.forward i)
    change S (t.atoms.backward (t.atoms.forward i))
    rw [t.atoms.backward_forward]
    exact hi

theorem domain_push_iff (t : Transport A B h k C D) (S : Basis m) (x : {x // A x}) :
    Domain A h S x.val ↔ Domain B k (pushBasis t S) (t.models.forward x).val :=
  ⟨fun hx => ⟨(t.models.forward x).property, (holds_push_iff t S x).mp hx.2⟩,
   fun hy => ⟨x.property, (holds_push_iff t S x).mpr hy.2⟩⟩

theorem ambient_forall_transport (t : Transport A B h k C D)
    (P : Model → Prop) (Q : Model' → Prop)
    (he : ∀ x : {x // A x}, P x.val ↔ Q (t.models.forward x).val) :
    (∀ x, A x → P x) ↔ (∀ y, B y → Q y) := by
  constructor
  · intro hp y hy
    have hq := (he (t.models.backward ⟨y, hy⟩)).mp
      (hp _ (t.models.backward ⟨y, hy⟩).property)
    rw [t.models.forward_backward] at hq
    exact hq
  · intro hq x hx
    exact (he ⟨x, hx⟩).mpr (hq _ (t.models.forward ⟨x, hx⟩).property)

theorem semantic_eq_transport (t : Transport A B h k C D) (S T : Basis m) :
    SemanticEq A h S T ↔ SemanticEq B k (pushBasis t S) (pushBasis t T) := by
  apply ambient_forall_transport t
  intro x
  rw [← holds_push_iff t S x, ← holds_push_iff t T x]

theorem domain_inclusion_transport (t : Transport A B h k C D) (S T : Basis m) :
    Included (Domain A h S) (Domain A h T) ↔
      Included (Domain B k (pushBasis t S)) (Domain B k (pushBasis t T)) := by
  have he : (∀ x, A x → (Holds h S x → Holds h T x)) ↔
      (∀ y, B y → (Holds k (pushBasis t S) y → Holds k (pushBasis t T) y)) := by
    apply ambient_forall_transport t
    intro x
    rw [← holds_push_iff t S x, ← holds_push_iff t T x]
  constructor
  · intro hs y hy
    exact ⟨hy.1, he.mp (fun x hx hh => (hs x ⟨hx, hh⟩).2) y hy.1 hy.2⟩
  · intro ht x hx
    exact ⟨hx.1, he.mpr (fun y hy hh => (ht y ⟨hy, hh⟩).2) x hx.1 hx.2⟩

theorem sufficient_transport (t : Transport A B h k C D) (S : Basis m) :
    Sufficient A h C S ↔ Sufficient B k D (pushBasis t S) := by
  have he : (∀ x, A x → (Holds h S x → C x)) ↔
      (∀ y, B y → (Holds k (pushBasis t S) y → D y)) := by
    apply ambient_forall_transport t
    intro x
    rw [← holds_push_iff t S x, ← t.target_iff x]
  constructor
  · intro hs y hy
    exact he.mp (fun x hx hh => hs x ⟨hx, hh⟩) y hy.1 hy.2
  · intro ht x hx
    exact he.mpr (fun y hy hh => ht y ⟨hy, hh⟩) x hx.1 hx.2

def classMap (t : Transport A B h k C D) : SemanticBasis A h → SemanticBasis B k :=
  Quotient.lift (fun S => classOf B k (pushBasis t S))
    (fun S T he => Quotient.sound (s := basisSetoid B k)
      ((semantic_eq_transport t S T).mp he))

theorem class_map_representative (t : Transport A B h k C D) (S : Basis m) :
    classMap t (classOf A h S) = classOf B k (pushBasis t S) := rfl

theorem class_pull_push (t : Transport A B h k C D) (q : SemanticBasis A h) :
    classMap (reverse t) (classMap t q) = q := by
  refine Quotient.inductionOn q (fun S => ?_)
  change classOf A h (pushBasis (reverse t) (pushBasis t S)) = classOf A h S
  rw [basis_pull_push]

theorem class_push_pull (t : Transport A B h k C D) (r : SemanticBasis B k) :
    classMap t (classMap (reverse t) r) = r := by
  refine Quotient.inductionOn r (fun T => ?_)
  change classOf B k (pushBasis t (pushBasis (reverse t) T)) = classOf B k T
  rw [basis_push_pull]

theorem class_order_transport (t : Transport A B h k C D) (q r : SemanticBasis A h) :
    classMap t q ≤ classMap t r ↔ q ≤ r := by
  refine Quotient.inductionOn₂ q r (fun S T => ?_)
  exact (domain_inclusion_transport t T S).symm

theorem class_sufficient_transport (t : Transport A B h k C D) (q : SemanticBasis A h) :
    ClassSufficient B k D (classMap t q) ↔ ClassSufficient A h C q := by
  refine Quotient.inductionOn q (fun S => ?_)
  exact (sufficient_transport t S).symm

def semanticOrderIso (t : Transport A B h k C D) :
    OrderIsomorphism (SemanticBasis A h) (SemanticBasis B k) where
  forward := classMap t
  backward := classMap (reverse t)
  backward_forward := class_pull_push t
  forward_backward := class_push_pull t
  le_iff := class_order_transport t

def sufficientMap (t : Transport A B h k C D) : SufficientClass A h C → SufficientClass B k D :=
  fun q => ⟨classMap t q.val, (class_sufficient_transport t q.val).mpr q.property⟩

theorem sufficient_pull_push (t : Transport A B h k C D) (q : SufficientClass A h C) :
    sufficientMap (reverse t) (sufficientMap t q) = q :=
  Subtype.eq (class_pull_push t q.val)

theorem sufficient_push_pull (t : Transport A B h k C D) (r : SufficientClass B k D) :
    sufficientMap t (sufficientMap (reverse t) r) = r :=
  Subtype.eq (class_push_pull t r.val)

def sufficientOrderIso (t : Transport A B h k C D) :
    OrderIsomorphism (SufficientClass A h C) (SufficientClass B k D) where
  forward := sufficientMap t
  backward := sufficientMap (reverse t)
  backward_forward := sufficient_pull_push t
  forward_backward := sufficient_push_pull t
  le_iff := fun q r => class_order_transport t q.val r.val

theorem minimal_transport (t : Transport A B h k C D) (q : SemanticBasis A h) :
    MinimalSufficient A h C q ↔ MinimalSufficient B k D (classMap t q) := by
  constructor
  · intro hm
    refine ⟨(class_sufficient_transport t q).mpr hm.1, ?_⟩
    intro r hr hle
    have hp := (class_sufficient_transport (reverse t) r).mpr hr
    have horder : classMap (reverse t) r ≤ q := by
      apply (class_order_transport t _ q).mp
      rw [class_push_pull]
      exact hle
    have he := congrArg (classMap t) (hm.2 _ hp horder)
    rw [class_push_pull] at he
    exact he
  · intro hm
    refine ⟨(class_sufficient_transport t q).mp hm.1, ?_⟩
    intro r hr hle
    have he := hm.2 (classMap t r) ((class_sufficient_transport t r).mpr hr)
      ((class_order_transport t r q).mpr hle)
    have hb := congrArg (classMap (reverse t)) he
    rw [class_pull_push, class_pull_push] at hb
    exact hb

theorem maximal_domain_transport (t : Transport A B h k C D) (S : Basis m) :
    MaximalSufficientDomain A h C S ↔ MaximalSufficientDomain B k D (pushBasis t S) :=
  (minimal_iff_maximal_domain A h C S).symm.trans
    ((minimal_transport t (classOf A h S)).trans
      (minimal_iff_maximal_domain B k D (pushBasis t S)))

end CausalFoundations.Representation

namespace CausalFoundations

open Semantic Representation

/-- The constructed sufficient-basis order isomorphism and both invariance claims. -/
theorem theorem16 {m n : Nat} {Model : Type u} {Model' : Type v}
    {A : Model → Prop} {B : Model' → Prop}
    {h : Fin m → Model → Prop} {k : Fin n → Model' → Prop}
    {C : Model → Prop} {D : Model' → Prop} (t : Transport A B h k C D) :
    (∃ e : OrderIsomorphism (SufficientClass A h C) (SufficientClass B k D),
      ∀ q, e.forward q = sufficientMap t q) ∧
    (∀ q, MinimalSufficient A h C q ↔ MinimalSufficient B k D (classMap t q)) ∧
    (∀ S, MaximalSufficientDomain A h C S ↔
      MaximalSufficientDomain B k D (pushBasis t S)) :=
  ⟨⟨sufficientOrderIso t, fun _ => rfl⟩, minimal_transport t, maximal_domain_transport t⟩

end CausalFoundations
