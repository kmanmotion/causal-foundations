import CausalFoundations.FixedSet

namespace CausalFoundations.FixedSetTests

open Symmetry

def flipGroup : SymmetryGroup Bool where
  identity := false
  product := Bool.xor
  inverse := id
  assoc := by intro g h k; cases g <;> cases h <;> cases k <;> rfl
  identity_left := by intro g; cases g <;> rfl
  identity_right := by intro g; cases g <;> rfl
  inverse_left := by intro g; cases g <;> rfl
  inverse_right := by intro g; cases g <;> rfl

def flipAction : Action flipGroup Bool where
  act := Bool.xor
  identity_act := by intro b; cases b <;> rfl
  product_act := by intro g h b; cases g <;> cases h <;> cases b <;> rfl

def stateAction : Action flipGroup (Option Bool) where
  act g s := s.map (Bool.xor g)
  identity_act := by intro s; cases s with
    | none => rfl
    | some b => cases b <;> rfl
  product_act := by
    intro g h s
    cases s with
    | none => rfl
    | some b => cases g <;> cases h <;> cases b <;> rfl

def diagonal : Channel Bool Bool Nat := fun c r => if c = r then 1 else 0
def bias (b : Bool) : Channel Bool Bool Nat := fun _ r => if r = b then 1 else 0
def assay : Option Bool → Channel Bool Bool Nat
  | none => diagonal
  | some b => bias b

def assayEquivariant : Equivariant stateAction (channelAction flipAction flipAction) assay := by
  intro g s
  cases s with
  | none => cases g <;> funext c r <;> cases c <;> cases r <;> rfl
  | some b => cases g <;> cases b <;> funext c r <;> cases c <;> cases r <;> rfl

def noneFixed : Fixed stateAction none := fun _ => rfl
def step (_ : Nat) (s : Option Bool) : Option Bool := s.map Bool.not
def stepEquivariant (n : Nat) : Equivariant stateAction stateAction (step n) := by
  intro g s
  cases s with
  | none => rfl
  | some b => cases g <;> cases b <;> rfl

theorem fixed_origin_stays_fixed_at_every_deterministic_step :
    ∀ n, Fixed stateAction (trajectory step none n) ∧
      Fixed (channelAction flipAction flipAction) (assay (trajectory step none n)) :=
  fun n => ⟨trajectory_fixed stateAction step stepEquivariant noneFixed n,
    trajectory_channel_fixed stateAction _ assay assayEquivariant step stepEquivariant noneFixed n⟩

/-- A symmetry-fixed channel can retain a challenge-response contrast. -/
theorem fixed_channel_can_have_response_contrast :
    Fixed (channelAction flipAction flipAction) (assay none) ∧
      assay none false false ≠ assay none true false := by
  refine ⟨assay_fixed stateAction flipAction flipAction assay assayEquivariant noneFixed, ?_⟩
  intro he
  change (1 : Nat) = 0 at he
  cases he

theorem nonfixed_origin_can_have_nontrivial_channel_orbit :
    ¬ Fixed stateAction (some true) ∧
      NontrivialOrbit (channelAction flipAction flipAction) (assay (some true)) := by
  constructor
  · intro hx
    have bad := hx true
    change some false = some true at bad
    cases bad
  · refine ⟨true, ?_⟩
    intro he
    have bad := congrArg (fun Q : Channel Bool Bool Nat => Q false true) he
    change (0 : Nat) = 1 at bad
    cases bad

def equalWeights (_ : Bool) : Nat := 1

theorem neutral_equal_weights_do_not_fix_realizations :
    (∀ g b, equalWeights (flipAction.act g b) = equalWeights b) ∧
    (∀ b, ¬ Fixed flipAction b) := by
  constructor
  · exact fun _ _ => rfl
  · intro b hx
    have bad := hx true
    cases b <;> cases bad

def badAssay (_ : Option Bool) : Channel Bool Bool Nat := bias true

theorem assay_equivariance_is_essential :
    Fixed stateAction none ∧
    NontrivialOrbit (channelAction flipAction flipAction) (badAssay none) ∧
    ¬ Equivariant stateAction (channelAction flipAction flipAction) badAssay := by
  refine ⟨noneFixed, ⟨true, ?_⟩, ?_⟩
  · intro he
    have bad := congrArg (fun Q : Channel Bool Bool Nat => Q false true) he
    change (0 : Nat) = 1 at bad
    cases bad
  · intro he
    have bad := congrArg (fun Q : Channel Bool Bool Nat => Q false true) (he true none)
    change (1 : Nat) = 0 at bad
    cases bad

def badEvolution (_ : Option Bool) : Option Bool := some true

theorem evolution_equivariance_is_essential :
    Fixed stateAction none ∧ ¬ Fixed stateAction (badEvolution none) ∧
    ¬ Equivariant stateAction stateAction badEvolution := by
  refine ⟨noneFixed, ?_, ?_⟩
  · intro hx
    have bad := hx true
    change some false = some true at bad
    cases bad
  · intro he
    have bad := he true none
    change some true = some false at bad
    cases bad

def cyclicGroup : SymmetryGroup (Fin 3) where
  identity := ⟨0, by decide⟩
  product g h := ⟨(g.val + h.val) % 3, Nat.mod_lt _ (by decide)⟩
  inverse g := ⟨(3 - g.val) % 3, Nat.mod_lt _ (by decide)⟩
  assoc := by decide
  identity_left := by decide
  identity_right := by decide
  inverse_left := by decide
  inverse_right := by decide

def rotateAction : Action cyclicGroup (Fin 3) where
  act := cyclicGroup.product
  identity_act := cyclicGroup.identity_left
  product_act := cyclicGroup.assoc

def unitAction : Action cyclicGroup Unit where
  act _ x := x
  identity_act := fun _ => rfl
  product_act := fun _ _ _ => rfl

theorem channel_action_uses_inverse_relabeling :
    (channelAction rotateAction unitAction).act ⟨1, by decide⟩
      (fun c _ => c.val) ⟨0, by decide⟩ () = 2 ∧
    (rotateAction.act ⟨1, by decide⟩ ⟨0, by decide⟩).val = 1 := ⟨rfl, rfl⟩

def identityGroup : SymmetryGroup Unit where
  identity := ()
  product _ _ := ()
  inverse _ := ()
  assoc := fun _ _ _ => rfl
  identity_left := by intro g; cases g; rfl
  identity_right := by intro g; cases g; rfl
  inverse_left := fun _ => rfl
  inverse_right := fun _ => rfl

def identityAction : Action identityGroup Bool where
  act _ b := b
  identity_act := fun _ => rfl
  product_act := fun _ _ _ => rfl

theorem trivial_group_boundary : ∀ b, Fixed identityAction b ∧ ¬ NontrivialOrbit identityAction b :=
  fun _ => ⟨fun _ => rfl, fixed_no_nontrivial_orbit identityAction (fun _ => rfl)⟩

#print axioms fixed_origin_stays_fixed_at_every_deterministic_step
#print axioms fixed_channel_can_have_response_contrast
#print axioms nonfixed_origin_can_have_nontrivial_channel_orbit
#print axioms neutral_equal_weights_do_not_fix_realizations
#print axioms assay_equivariance_is_essential
#print axioms evolution_equivariance_is_essential
#print axioms channel_action_uses_inverse_relabeling
#print axioms trivial_group_boundary

end CausalFoundations.FixedSetTests
