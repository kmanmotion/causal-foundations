import CausalFoundations.Representation

namespace CausalFoundations.RepresentationTests

open Semantic Representation

def allModels {X : Type} (_ : X) : Prop := True
def represented (y : Option Bool) : Prop := y.isSome = true
def sourceAtoms (i : Fin 2) (b : Bool) : Prop := if i.val = 0 then b = true else b = false
def targetAtoms (j : Fin 2) (y : Option Bool) : Prop :=
  if j.val = 0 then y = some true else y = some false
def sourceBasis : Basis 2 := fun i => i.val = 0

/-- Changes the carrier, flips model labels and swaps atom indices. -/
def renamed : Transport allModels represented sourceAtoms targetAtoms
    (fun b => b = true) (fun y => y = some false) where
  models := {
    forward := fun b => ⟨some (!b.val), rfl⟩
    backward := fun y => ⟨!(y.val.getD false), True.intro⟩
    backward_forward := by
      intro x
      apply Subtype.eq
      cases x.val <;> rfl
    forward_backward := by
      intro y
      apply Subtype.eq
      rcases y with ⟨y, hy⟩
      cases y with
      | none => cases hy
      | some b => cases b <;> rfl
  }
  atoms := {
    forward := Fin.rev
    backward := Fin.rev
    backward_forward := Fin.rev_rev
    forward_backward := Fin.rev_rev
  }
  target_iff := by intro ⟨b, hb⟩; cases b <;> simp
  atom_iff := by
    intro i ⟨b, hb⟩
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with hi | hi <;> cases b <;> simp [sourceAtoms, targetAtoms, Fin.rev, hi]

theorem nontrivial_model_and_atom_renaming :
    (renamed.models.forward ⟨true, True.intro⟩).val = some false ∧
    renamed.atoms.forward ⟨0, by decide⟩ = ⟨1, by decide⟩ ∧
    Sufficient represented targetAtoms (fun y => y = some false) (pushBasis renamed sourceBasis) := by
  refine ⟨rfl, rfl, (sufficient_transport renamed sourceBasis).mp ?_⟩
  intro b hb
  exact hb.2 ⟨0, by decide⟩ rfl

theorem unmatched_carrier_point_is_excluded :
    ¬ represented none ∧ ∀ S : Basis 2, ¬ Domain represented targetAtoms S none := by
  constructor
  · intro h; cases h
  · intro S h; cases h.1

theorem source_basis_minimal :
    MinimalSufficient allModels sourceAtoms (fun b => b = true)
      (classOf allModels sourceAtoms sourceBasis) := by
  refine ⟨fun b hb => hb.2 ⟨0, by decide⟩ rfl, ?_⟩
  intro q
  refine Quotient.inductionOn q (fun S hs hle => ?_)
  have hz : S ⟨0, by decide⟩ := by
    classical
    by_cases hz : S ⟨0, by decide⟩
    · exact hz
    · have bad := hs false ⟨True.intro, by
        intro i hi
        by_cases he : i.val = 0
        · have ie : i = ⟨0, by decide⟩ := Fin.ext he
          exact False.elim (hz (ie ▸ hi))
        · simp [sourceAtoms, he]⟩
      cases bad
  apply class_le_antisymm allModels sourceAtoms hle
  intro b hb
  exact ⟨hb.1, fun i hi => by
    have bt : b = true := hb.2 ⟨0, by decide⟩ hz
    change i.val = 0 at hi
    simp [sourceAtoms, hi, bt]⟩

theorem renamed_minimum_and_maximal_domain :
    MinimalSufficient represented targetAtoms (fun y => y = some false)
      (classMap renamed (classOf allModels sourceAtoms sourceBasis)) ∧
    MaximalSufficientDomain represented targetAtoms (fun y => y = some false)
      (pushBasis renamed sourceBasis) := by
  constructor
  · exact (minimal_transport renamed _).mp source_basis_minimal
  · exact (maximal_domain_transport renamed sourceBasis).mp
      ((minimal_iff_maximal_domain allModels sourceAtoms (fun b => b = true) sourceBasis).mp
        source_basis_minimal)

def emptyTransport : Transport (fun (_ : Nat) => False) (fun (_ : Bool) => False)
    (fun (_ : Fin 0) _ => True) (fun (_ : Fin 0) _ => False)
    (fun _ => True) (fun _ => False) where
  models := {
    forward := fun x => False.elim x.property
    backward := fun y => False.elim y.property
    backward_forward := fun x => False.elim x.property
    forward_backward := fun y => False.elim y.property
  }
  atoms := {
    forward := fun i => Fin.elim0 i
    backward := fun j => Fin.elim0 j
    backward_forward := fun i => Fin.elim0 i
    forward_backward := fun j => Fin.elim0 j
  }
  target_iff := fun x => False.elim x.property
  atom_iff := fun i => Fin.elim0 i

theorem empty_ambient_and_library_allow_vacuous_transport :
    Nonempty (OrderIsomorphism
      (SufficientClass (fun (_ : Nat) => False) (fun (_ : Fin 0) _ => True) (fun _ => True))
      (SufficientClass (fun (_ : Bool) => False) (fun (_ : Fin 0) _ => False) (fun _ => False))) :=
  ⟨sufficientOrderIso emptyTransport⟩

def fullBasis : Basis 1 := fun _ => True
def trueAtom (_ : Fin 1) (_ : Bool) : Prop := True
def orientationAtom (_ : Fin 1) (b : Bool) : Prop := b = true

/-- One-way atom preservation alone can turn a sufficient basis into an insufficient one. -/
theorem one_way_atom_preservation_is_insufficient :
    (∀ i b, orientationAtom i b → trueAtom i b) ∧
    Sufficient allModels orientationAtom (fun b => b = true) fullBasis ∧
    ¬ Sufficient allModels trueAtom (fun b => b = true) fullBasis := by
  refine ⟨fun _ _ _ => True.intro, fun _ hx => hx.2 ⟨0, by decide⟩ True.intro, ?_⟩
  intro hs
  have bad := hs false ⟨True.intro, fun _ _ => True.intro⟩
  cases bad

theorem target_preservation_is_essential :
    Sufficient allModels trueAtom (fun _ => True) fullBasis ∧
    ¬ Sufficient allModels trueAtom (fun _ => False) fullBasis :=
  ⟨fun _ _ => True.intro, fun hs => hs false ⟨True.intro, fun _ _ => True.intro⟩⟩

/-- An embedding of just the true model misses a target counterexample. -/
theorem model_surjectivity_is_essential :
    (∀ i : Fin 1, (True ↔ trueAtom i true)) ∧
    (True ↔ (true : Bool) = true) ∧
    Sufficient allModels (fun (_ : Fin 1) (_ : Unit) => True) (fun _ => True) fullBasis ∧
    ¬ Sufficient allModels trueAtom (fun b => b = true) fullBasis := by
  refine ⟨fun _ => Iff.rfl,
    ⟨fun _ => rfl, fun _ => True.intro⟩, fun _ _ => True.intro, ?_⟩
  intro hs
  have bad := hs false ⟨True.intro, fun _ _ => True.intro⟩
  cases bad

theorem two_atoms_cannot_be_bijectively_merged : ¬ Nonempty (Bijection (Fin 2) (Fin 1)) := by
  intro ⟨f⟩
  have he : f.forward ⟨0, by decide⟩ = f.forward ⟨1, by decide⟩ := by
    apply Fin.ext
    have h0 := (f.forward ⟨0, by decide⟩).isLt
    have h1 := (f.forward ⟨1, by decide⟩).isLt
    omega
  have hb := congrArg f.backward he
  rw [f.backward_forward, f.backward_forward] at hb
  have bad := congrArg Fin.val hb
  cases bad

#print axioms nontrivial_model_and_atom_renaming
#print axioms unmatched_carrier_point_is_excluded
#print axioms source_basis_minimal
#print axioms renamed_minimum_and_maximal_domain
#print axioms empty_ambient_and_library_allow_vacuous_transport
#print axioms one_way_atom_preservation_is_insufficient
#print axioms target_preservation_is_essential
#print axioms model_surjectivity_is_essential
#print axioms two_atoms_cannot_be_bijectively_merged

end CausalFoundations.RepresentationTests
