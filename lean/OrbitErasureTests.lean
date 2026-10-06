import CausalFoundations.OrbitErasure
import FixedSetTests

namespace CausalFoundations.OrbitErasureTests

open Symmetry FixedSetTests

def wholeBool (_ : Bool) : Prop := True
def wholeBoolStable : GroupStable flipAction wholeBool := fun _ _ _ => trivial

def biasEquivariant : Equivariant flipAction (channelAction flipAction flipAction) bias :=
  fun g b => assayEquivariant g (some b)

def biasTrueNontrivial : NontrivialOrbit (channelAction flipAction flipAction) (bias true) :=
  nonfixed_origin_can_have_nontrivial_channel_orbit.2

def someDomain : Option Bool → Prop
  | none => False
  | some _ => True

def someDomainStable : GroupStable stateAction someDomain := by
  intro g s hs
  cases s with
  | none => exact False.elim hs
  | some _ => trivial

def erasedAssay : Option Bool → Channel Bool Bool Nat
  | none => bias true
  | some _ => diagonal

def erasedEquivariantOn :
    EquivariantOn stateAction (channelAction flipAction flipAction) someDomain erasedAssay := by
  intro g s hs
  cases s with
  | none => exact False.elim hs
  | some b => cases g <;> funext c r <;> cases c <;> cases r <;> rfl

def erasedFactorsOn : FactorsOn stateAction someDomain erasedAssay := by
  refine ⟨fun _ => diagonal, ?_⟩
  intro s hs
  cases s with
  | none => exact False.elim hs
  | some _ => rfl

theorem proper_stable_domain_erases_nonfixed_states :
    ¬ Fixed stateAction (some true) ∧
    Fixed (channelAction flipAction flipAction) (erasedAssay (some true)) ∧
    (∀ other, ¬ ContingentWith (channelAction flipAction flipAction) erasedAssay other (some true)) := by
  have h := theorem2 flipGroup stateAction flipAction flipAction someDomain erasedAssay
    someDomainStable erasedEquivariantOn erasedFactorsOn (some true) trivial
  exact ⟨nonfixed_origin_can_have_nontrivial_channel_orbit.1, h.2.1, h.2.2.2⟩

theorem local_domain_does_not_assert_outside_fixedness :
    NontrivialOrbit (channelAction flipAction flipAction) (erasedAssay none) ∧
    ¬ Equivariant stateAction (channelAction flipAction flipAction) erasedAssay := by
  refine ⟨biasTrueNontrivial, ?_⟩
  intro he
  have bad := congrArg (fun Q : Channel Bool Bool Nat => Q false true) (he true none)
  change (1 : Nat) = 0 at bad
  cases bad

def conditioned (b : Bool) : Prop := b = true
def conditionedFactors : FactorsOn flipAction conditioned bias :=
  ⟨fun _ => bias true, fun _ hx => congrArg bias hx⟩

theorem singleton_conditioning_needs_group_stability :
    FactorsOn flipAction conditioned bias ∧
    EquivariantOn flipAction (channelAction flipAction flipAction) conditioned bias ∧
    NontrivialOrbit (channelAction flipAction flipAction) (bias true) ∧
    ¬ GroupStable flipAction conditioned := by
  refine ⟨conditionedFactors, restrict_equivariance _ _ _ _ biasEquivariant,
    biasTrueNontrivial, ?_⟩
  intro hs
  have bad := hs true true rfl
  change false = true at bad
  cases bad

def constantBiased (_ : Bool) : Channel Bool Bool Nat := bias true

theorem factorization_alone_does_not_fix_channels :
    GroupStable flipAction wholeBool ∧
    FactorsOn flipAction wholeBool constantBiased ∧
    NontrivialOrbit (channelAction flipAction flipAction) (constantBiased true) ∧
    ¬ EquivariantOn flipAction (channelAction flipAction flipAction) wholeBool constantBiased := by
  refine ⟨wholeBoolStable, ⟨fun _ => bias true, fun _ _ => rfl⟩, biasTrueNontrivial, ?_⟩
  intro he
  have bad := congrArg (fun Q : Channel Bool Bool Nat => Q false true) (he true true trivial)
  change (1 : Nat) = 0 at bad
  cases bad

theorem equivariance_alone_does_not_erase :
    EquivariantOn flipAction (channelAction flipAction flipAction) wholeBool bias ∧
    ¬ FactorsOn flipAction wholeBool bias := by
  have he := restrict_equivariance flipAction _ wholeBool bias biasEquivariant
  exact ⟨he, nontrivial_prevents_factorization flipAction _ wholeBool bias
    wholeBoolStable he trivial biasTrueNontrivial⟩

theorem quotient_identifies_exactly_state_orbits :
    orbitClass stateAction (some false) = orbitClass stateAction (some true) ∧
    orbitClass stateAction none ≠ orbitClass stateAction (some true) := by
  constructor
  · exact (orbit_class_eq_iff stateAction _ _).mpr ⟨true, rfl⟩
  · intro he
    obtain ⟨g, hg⟩ := (orbit_class_eq_iff stateAction _ _).mp he
    change none = some true at hg
    cases hg

def preparation (s : Option Bool) : Prop := s = none
def preparationStable : GroupStable stateAction preparation := by
  intro g s hs
  exact hs ▸ rfl

def twoChoices (i : Bool) (s t : Option Bool) : Prop := s = none ∧ t = some i
def twoChoicesEquivariant : FamilyEquivariant stateAction flipAction twoChoices := by
  intro g i s t ⟨hs, ht⟩
  subst s
  subst t
  exact ⟨rfl, rfl⟩

def twoChoiceReachable (i : Bool) : Reachable preparation (AllowedStep twoChoices) (some i) :=
  Reachable.step (Reachable.initial rfl) ⟨i, rfl, rfl⟩

theorem transported_interventions_generate_stable_reachability :
    Reachable preparation (AllowedStep twoChoices) (some false) ∧
    Reachable preparation (AllowedStep twoChoices) (some true) ∧
    GroupStable stateAction (Reachable preparation (AllowedStep twoChoices)) ∧
    ¬ Equivariant stateAction stateAction (fun _ => some false) := by
  refine ⟨twoChoiceReachable false, twoChoiceReachable true,
    reachable_family_stable stateAction flipAction preparation twoChoices
      preparationStable twoChoicesEquivariant, ?_⟩
  intro he
  have bad := he true none
  change some false = some true at bad
  cases bad

theorem empty_preparation_has_no_reachable_origin :
    ∀ s : Bool, ¬ Reachable (fun _ => False) (fun _ _ => True) s := by
  intro s hs
  exact reachable_least (fun _ => False) (fun _ => False) (fun _ _ => True)
    (fun _ h => h) (fun _ _ h _ => h) s hs

def oneChoice (s t : Option Bool) : Prop := s = none ∧ t = some true
def narrowDomain (s : Option Bool) : Prop := s = none ∨ s = some true

def oneChoiceNarrow : ∀ s, Reachable preparation oneChoice s → narrowDomain s :=
  reachable_least preparation narrowDomain oneChoice (fun _ hp => Or.inl hp)
    (fun _ _ _ hr => Or.inr hr.2)

theorem transition_family_closure_is_essential :
    GroupStable stateAction preparation ∧
    Reachable preparation oneChoice (some true) ∧
    ¬ GroupStable stateAction (Reachable preparation oneChoice) ∧
    ¬ TransitionEquivariant stateAction oneChoice := by
  have hr : Reachable preparation oneChoice (some true) :=
    Reachable.step (Reachable.initial rfl) ⟨rfl, rfl⟩
  refine ⟨preparationStable, hr, ?_, ?_⟩
  · intro hs
    have bad := oneChoiceNarrow _ (hs true _ hr)
    change some false = none ∨ some false = some true at bad
    cases bad with
    | inl he => cases he
    | inr he => cases he
  · intro he
    have bad := (he true none (some true) ⟨rfl, rfl⟩).2
    change some false = some true at bad
    cases bad

#print axioms proper_stable_domain_erases_nonfixed_states
#print axioms local_domain_does_not_assert_outside_fixedness
#print axioms singleton_conditioning_needs_group_stability
#print axioms factorization_alone_does_not_fix_channels
#print axioms equivariance_alone_does_not_erase
#print axioms quotient_identifies_exactly_state_orbits
#print axioms transported_interventions_generate_stable_reachability
#print axioms empty_preparation_has_no_reachable_origin
#print axioms transition_family_closure_is_essential

end CausalFoundations.OrbitErasureTests
