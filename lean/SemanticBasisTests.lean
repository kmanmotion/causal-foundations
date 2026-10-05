import CausalFoundations.SemanticBasis

namespace CausalFoundations.Tests

open Semantic

def allModels {Model : Type} (_ : Model) : Prop := True

def aliasAtoms (_ : Fin 2) (b : Bool) : Prop := b = true

def firstAtom : Basis 2 := fun i => i.val = 0
def secondAtom : Basis 2 := fun i => i.val = 1

theorem alias_bases_syntactically_distinct : firstAtom ≠ secondAtom := by
  intro he
  have hp : firstAtom ⟨0, by decide⟩ := rfl
  have ht : secondAtom ⟨0, by decide⟩ := he ▸ hp
  change (0 : Nat) = 1 at ht
  cases ht

theorem alias_classes_equal :
    classOf allModels aliasAtoms firstAtom = classOf allModels aliasAtoms secondAtom := by
  apply (classOf_eq_iff allModels aliasAtoms firstAtom secondAtom).mpr
  intro b _
  constructor
  · intro hs i _
    exact hs ⟨0, by decide⟩ rfl
  · intro ht i _
    exact ht ⟨1, by decide⟩ rfl

def singleAtom (_ : Fin 1) (b : Bool) : Prop := b = true
def emptyBasis : Basis 1 := fun _ => False
def fullBasis : Basis 1 := fun _ => True

theorem full_basis_sufficient : Sufficient allModels singleAtom (fun b => b = true) fullBasis :=
  fun _ hx => hx.2 ⟨0, by decide⟩ True.intro

theorem empty_basis_not_sufficient :
    ¬ Sufficient allModels singleAtom (fun b => b = true) emptyBasis := by
  intro hs
  have bad := hs false ⟨True.intro, fun _ hi => False.elim hi⟩
  cases bad

theorem weak_to_strong_direction :
    classOf allModels singleAtom emptyBasis ≤ classOf allModels singleAtom fullBasis ∧
    ¬ classOf allModels singleAtom fullBasis ≤ classOf allModels singleAtom emptyBasis := by
  constructor
  · exact basis_subset_implies_order allModels singleAtom (fun _ hi => False.elim hi)
  · intro hr
    have bad := (hr false ⟨True.intro, fun _ hi => False.elim hi⟩).2
      ⟨0, by decide⟩ True.intro
    cases bad

theorem empty_ambient_classes_equal
    (q r : SemanticBasis (fun (_ : Bool) => False) aliasAtoms) : q = r := by
  refine Quotient.inductionOn₂ q r (fun S T => ?_)
  apply (classOf_eq_iff (fun (_ : Bool) => False) aliasAtoms S T).mpr
  exact fun _ ha => False.elim ha

def threeModels (x : Nat) : Prop := x = 0 ∨ x = 1 ∨ x = 2
def branchAtoms (i : Fin 2) (x : Nat) : Prop := if i.val = 0 then x = 0 else x = 1
def branchUnion (x : Nat) : Prop := x = 0 ∨ x = 1

theorem two_branch_bases_sufficient :
    Sufficient threeModels branchAtoms branchUnion firstAtom ∧
    Sufficient threeModels branchAtoms branchUnion secondAtom := by
  constructor
  · intro x hx
    exact Or.inl (hx.2 ⟨0, by decide⟩ rfl)
  · intro x hx
    exact Or.inr (hx.2 ⟨1, by decide⟩ rfl)

/-- An admitted disjunction could supply a larger domain than this library generates. -/
theorem disjunction_not_conjunction_generated :
    ¬ ∃ S : Basis 2, Domain threeModels branchAtoms S = branchUnion := by
  intro ⟨S, he⟩
  have hx0 : Domain threeModels branchAtoms S 0 := by
    rw [he]
    exact Or.inl rfl
  have hx1 : Domain threeModels branchAtoms S 1 := by
    rw [he]
    exact Or.inr rfl
  have hx2 : Domain threeModels branchAtoms S 2 := by
    refine ⟨Or.inr (Or.inr rfl), ?_⟩
    intro i hi
    by_cases hz : i.val = 0
    · have bad := hx1.2 i hi
      simp [branchAtoms, hz] at bad
    · have bad := hx0.2 i hi
      simp [branchAtoms, hz] at bad
  rw [he] at hx2
  rcases hx2 with bad | bad <;> cases bad

#print axioms alias_bases_syntactically_distinct
#print axioms alias_classes_equal
#print axioms full_basis_sufficient
#print axioms empty_basis_not_sufficient
#print axioms weak_to_strong_direction
#print axioms empty_ambient_classes_equal
#print axioms two_branch_bases_sufficient
#print axioms disjunction_not_conjunction_generated

end CausalFoundations.Tests
