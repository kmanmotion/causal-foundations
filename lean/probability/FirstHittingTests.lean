import CausalFoundationsProbability
import Mathlib.MeasureTheory.Measure.Dirac

open scoped ENNReal

namespace CausalFoundations.FirstHittingTests

open CausalFoundations.Symmetry CausalFoundations.FirstHitting MeasureTheory Set

local instance : MeasurableSpace (Option Bool) := ⊤

def flipGroup : SymmetryGroup Bool where
  identity := false
  product := Bool.xor
  inverse := id
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  identity_left := by intro a; cases a <;> rfl
  identity_right := by intro a; cases a <;> rfl
  inverse_left := by intro a; cases a <;> rfl
  inverse_right := by intro a; cases a <;> rfl

def flipAction : Action flipGroup Bool where
  act := Bool.xor
  identity_act := by intro a; cases a <;> rfl
  product_act := by intro g h a; cases g <;> cases h <;> cases a <;> rfl

noncomputable def coin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac false + Measure.dirac true)

instance coin_probability : IsProbabilityMeasure coin := by
  constructor
  simp only [coin, Measure.smul_apply, smul_eq_mul, Measure.add_apply, measure_univ]
  simpa only [one_add_one_eq_two] using
    (ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by simp) (by simp))

theorem coin_invariant (g : Bool) : coin.map (flipAction.act g) = coin := by
  have hm : Measurable (flipAction.act g) := measurable_of_countable _
  unfold coin
  rw [Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac hm, Measure.map_dirac hm]
  cases g <;> simp [flipAction, Bool.xor, add_comm]

noncomputable def coinModel : Model (Time := ℕ) flipGroup flipAction flipAction flipAction coin where
  horizon := 0
  process := fun _ ω => ω
  cells := fun θ => {θ}
  path_measurable := fun _ => measurable_of_countable _
  state_measurable := fun _ => measurable_of_countable _
  cells_measurable := fun _ => measurableSet_singleton _
  cells_disjoint := by intro θ η x hθ hη; exact hθ.symm.trans hη
  cells_transport := by intro g θ x; cases g <;> cases θ <;> cases x <;> decide
  process_equivariant := by intro g t ω; rfl
  transitive := by intro θ η; cases θ <;> cases η <;> first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩
  hit_measurable := (Set.to_countable _).measurableSet
  exceptional := ∅
  exceptional_null := measure_empty
  exceptional_invariant := by intro g ω; rfl
  firstTime := fun _ => (0 : WithTop ℕ)
  orientation := some
  time_measurable := measurable_const
  orientation_measurable := measurable_of_countable _
  attained := by
    intro ω _ _
    exact ⟨0, ω, rfl, ⟨⟨le_rfl, le_rfl, ω, rfl⟩, fun _ hs => hs.1⟩, rfl, rfl⟩
  off_time := by
    intro ω h
    rcases h with h | h
    · exact False.elim (h ⟨0, le_rfl, le_rfl, ω, rfl⟩)
    · exact False.elim h
  off_orientation := by
    intro ω h
    rcases h with h | h
    · exact False.elim (h ⟨0, le_rfl, le_rfl, ω, rfl⟩)
    · exact False.elim h
  path_law_invariant := coin_invariant

theorem coin_hit_univ : Hit coinModel.process coinModel.cells coinModel.horizon = univ := by
  ext ω
  exact ⟨fun _ => trivial, fun _ => ⟨0, le_rfl, le_rfl, ω, rfl⟩⟩

theorem two_orientation_half (θ : Bool) : coin (labelEvent coinModel θ) = 1 / (2 : ℝ≥0∞) := by
  rw [equal_orbit_first_hit coinModel θ, coin_hit_univ, measure_univ]
  rfl

theorem positive_hit_conditional_half (θ : Bool) :
    conditionalOrientation coinModel θ = 1 / (2 : ℝ≥0∞) := by
  have hH : 0 < coin (Hit coinModel.process coinModel.cells coinModel.horizon) := by
    rw [coin_hit_univ, measure_univ]
    exact zero_lt_one
  exact conditional_uniform coinModel hH θ

theorem invariant_law_has_asymmetric_realization :
    (∀ g, coin.map (flipAction.act g) = coin) ∧ ¬ Fixed flipAction false := by
  refine ⟨coin_invariant, ?_⟩
  intro h
  have bad := h true
  exact Bool.noConfusion bad

theorem biased_path_law_not_invariant :
    (Measure.dirac false).map (flipAction.act true) ≠ Measure.dirac false := by
  intro h
  have he := congrArg (fun m : Measure Bool => m {false}) h
  have hm : Measurable (flipAction.act true) := measurable_of_countable _
  rw [Measure.map_dirac hm] at he
  simp [flipAction, Bool.xor] at he

def identityAction : Action flipGroup Bool where
  act := fun _ x => x
  identity_act := fun _ => rfl
  product_act := fun _ _ _ => rfl

theorem no_transitivity_no_uniformity :
    (∀ g, (Measure.dirac false).map (identityAction.act g) = Measure.dirac false) ∧
    (¬ ∃ g, identityAction.act g false = true) ∧
    Measure.dirac false {ω : Bool | some ω = some false} ≠
      Measure.dirac false {ω : Bool | some ω = some true} := by
  exact ⟨fun _ => Measure.map_id, by simp [identityAction], by simp⟩

theorem nonnull_exception_cannot_be_ignored :
    coin univ ≠ 0 ∧
    coin (univ ∩ {_ω : Bool | (none : Option Bool) = some false}) ≠ coin univ / 2 := by
  constructor
  · rw [measure_univ]
    exact one_ne_zero
  · have hempty : (univ ∩ {_ω : Bool | (none : Option Bool) = some false}) = ∅ := by
      ext ω
      simp
    rw [hempty, measure_empty, measure_univ]
    exact ne_of_lt (ENNReal.div_pos (by simp) (by simp))

theorem discrete_hit_attains {Ω State Θ : Type*} (X : ℕ → Ω → State)
    (B : Θ → Set State) (T : ℕ) (ω : Ω) (hH : ω ∈ Hit X B T) :
    ∃ t, FirstEntry X B T ω t := by
  classical
  exact ⟨Nat.find hH, Nat.find_spec hH, fun s hs => Nat.find_min' hH hs⟩

def openCell (_ : Unit) : Set ℝ := {t | 0 < t}
def continuousPath (t : ℝ) (_ : Unit) : ℝ := t

theorem continuous_visit_without_first_entry :
    () ∈ Hit continuousPath openCell (1 : ℝ) ∧
      ¬ ∃ t, FirstEntry continuousPath openCell (1 : ℝ) () t := by
  constructor
  · exact ⟨1, zero_le_one, le_rfl, (), (show (0 : ℝ) < 1 from zero_lt_one)⟩
  · rintro ⟨t, hfirst⟩
    obtain ⟨_, _, θ, ht⟩ := hfirst.1
    have hpos : 0 < t := ht
    have hh : 0 < t / 2 := half_pos hpos
    have hlt : t / 2 < t := (half_lt_self_iff).2 hpos
    have hsmall : Visit continuousPath openCell (1 : ℝ) () (t / 2) :=
      ⟨le_of_lt hh, le_trans (le_of_lt hlt) hfirst.1.2.1, (), hh⟩
    exact (not_le_of_gt hlt) (hfirst.2 (t / 2) hsmall)

theorem horizon_excludes_later_visits :
    ¬ Visit (fun t (_ : Unit) => t) (fun (_ : Unit) => ({1} : Set ℕ)) 0 () 1 := by
  intro h
  exact Nat.not_succ_le_zero 0 h.2.1

theorem zero_hit_ratio_is_zero {Ω State Time : Type*} {G : SymmetryGroup Bool}
    [LinearOrder Time] [Zero Time] [MeasurableSpace Ω] [MeasurableSpace State]
    [MeasurableSpace Time]
    {pa : Action G Ω} {sa : Action G State} {oa : Action G Bool} {μ : Measure Ω}
    (D : Model (Time := Time) G pa sa oa μ)
    (hH : μ (Hit D.process D.cells D.horizon) = 0) (θ : Bool) :
    conditionalOrientation D θ = 0 ∧ conditionalOrientation D θ ≠ 1 / (2 : ℝ≥0∞) := by
  have hz : conditionalOrientation D θ = 0 := by
    unfold conditionalOrientation
    rw [null_hit_zero D hH θ, hH, ENNReal.zero_div]
  refine ⟨hz, ?_⟩
  rw [hz]
  exact ne_of_lt (ENNReal.div_pos (by simp) (by simp))

end CausalFoundations.FirstHittingTests

#print axioms CausalFoundations.FirstHittingTests.coin_invariant
#print axioms CausalFoundations.FirstHittingTests.coin_hit_univ
#print axioms CausalFoundations.FirstHittingTests.two_orientation_half
#print axioms CausalFoundations.FirstHittingTests.positive_hit_conditional_half
#print axioms CausalFoundations.FirstHittingTests.invariant_law_has_asymmetric_realization
#print axioms CausalFoundations.FirstHittingTests.biased_path_law_not_invariant
#print axioms CausalFoundations.FirstHittingTests.no_transitivity_no_uniformity
#print axioms CausalFoundations.FirstHittingTests.nonnull_exception_cannot_be_ignored
#print axioms CausalFoundations.FirstHittingTests.discrete_hit_attains
#print axioms CausalFoundations.FirstHittingTests.continuous_visit_without_first_entry
#print axioms CausalFoundations.FirstHittingTests.horizon_excludes_later_visits
#print axioms CausalFoundations.FirstHittingTests.zero_hit_ratio_is_zero
