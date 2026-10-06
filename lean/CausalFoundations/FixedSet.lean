import Init

/-!
# Published Theorem 1: deterministic fixed-set impossibility

Source: Causal Foundations v1.0, section 3.1, page 5; induced channel action
in section 2.3, page 3. DOI: 10.5281/zenodo.22902457.

Only the pointwise deterministic branch is formalized. The stochastic branch,
actual conditional kernels and countable null-event argument are separate.
Other assignment conditions remain arbitrary: contingency requires a nontrivial
channel orbit in addition to those conditions, not merely a response contrast.
-/

namespace CausalFoundations.Symmetry

universe u v w z t

structure SymmetryGroup (Γ : Type u) where
  identity : Γ
  product : Γ → Γ → Γ
  inverse : Γ → Γ
  assoc : ∀ g h k, product (product g h) k = product g (product h k)
  identity_left : ∀ g, product identity g = g
  identity_right : ∀ g, product g identity = g
  inverse_left : ∀ g, product (inverse g) g = identity
  inverse_right : ∀ g, product g (inverse g) = identity

theorem group_left_cancel {Γ : Type u} (G : SymmetryGroup Γ) {g a b : Γ}
    (he : G.product g a = G.product g b) : a = b := by
  have ha : G.product (G.inverse g) (G.product g a) = a := by
    rw [← G.assoc, G.inverse_left, G.identity_left]
  have hb : G.product (G.inverse g) (G.product g b) = b := by
    rw [← G.assoc, G.inverse_left, G.identity_left]
  exact ha.symm.trans ((congrArg (G.product (G.inverse g)) he).trans hb)

theorem inverse_identity {Γ : Type u} (G : SymmetryGroup Γ) :
    G.inverse G.identity = G.identity := by
  have he := G.inverse_right G.identity
  rw [G.identity_left] at he
  exact he

theorem inverse_product {Γ : Type u} (G : SymmetryGroup Γ) (g h : Γ) :
    G.inverse (G.product g h) = G.product (G.inverse h) (G.inverse g) := by
  apply group_left_cancel G (g := G.product g h)
  rw [G.inverse_right]
  symm
  calc
    G.product (G.product g h) (G.product (G.inverse h) (G.inverse g)) =
        G.product g (G.product h (G.product (G.inverse h) (G.inverse g))) := G.assoc _ _ _
    _ = G.product g (G.product (G.product h (G.inverse h)) (G.inverse g)) :=
        congrArg (G.product g) (G.assoc h (G.inverse h) (G.inverse g)).symm
    _ = G.identity := by rw [G.inverse_right, G.identity_left, G.inverse_right]

structure Action {Γ : Type u} (G : SymmetryGroup Γ) (X : Type v) where
  act : Γ → X → X
  identity_act : ∀ x, act G.identity x = x
  product_act : ∀ g h x, act (G.product g h) x = act g (act h x)

variable {Γ : Type u} {G : SymmetryGroup Γ} {X : Type v} {Y : Type w} {Z : Type z}

def Fixed (a : Action G X) (x : X) : Prop := ∀ g, a.act g x = x
def Orbit (a : Action G X) (x y : X) : Prop := ∃ g, a.act g x = y
def NontrivialOrbit (a : Action G X) (x : X) : Prop := ∃ g, a.act g x ≠ x
def Equivariant (a : Action G X) (b : Action G Y) (f : X → Y) : Prop :=
  ∀ g x, f (a.act g x) = b.act g (f x)

/-- The other scientific requirements are retained as a separate arbitrary predicate. -/
def ContingentWith (b : Action G Y) (Φ : X → Y) (other : X → Prop) (x : X) : Prop :=
  other x ∧ NontrivialOrbit b (Φ x)

theorem orbit_self (a : Action G X) (x : X) : Orbit a x x :=
  ⟨G.identity, a.identity_act x⟩

theorem fixed_iff_singleton_orbit (a : Action G X) (x : X) :
    Fixed a x ↔ (∀ y, Orbit a x y ↔ y = x) := by
  constructor
  · intro hx y
    constructor
    · intro ⟨g, hg⟩
      exact hg.symm.trans (hx g)
    · intro hy
      rw [hy]
      exact orbit_self a x
  · intro ho g
    exact (ho (a.act g x)).mp ⟨g, rfl⟩

theorem fixed_no_nontrivial_orbit (a : Action G X) {x : X} (hx : Fixed a x) :
    ¬ NontrivialOrbit a x := fun ⟨g, hg⟩ => hg (hx g)

theorem equivariant_fixed (a : Action G X) (b : Action G Y) (f : X → Y)
    (hf : Equivariant a b f) {x : X} (hx : Fixed a x) : Fixed b (f x) := by
  intro g
  exact (hf g x).symm.trans (congrArg f (hx g))

theorem equivariant_composition (a : Action G X) (b : Action G Y) (c : Action G Z)
    (f : X → Y) (k : Y → Z) (hf : Equivariant a b f) (hk : Equivariant b c k) :
    Equivariant a c (fun x => k (f x)) := by
  intro g x
  exact (congrArg k (hf g x)).trans (hk g (f x))

theorem fixed_no_contingency (a : Action G X) (b : Action G Y) (Φ : X → Y)
    (hΦ : Equivariant a b Φ) (other : X → Prop) {x : X} (hx : Fixed a x) :
    ¬ ContingentWith b Φ other x :=
  fun hc => fixed_no_nontrivial_orbit b (equivariant_fixed a b Φ hΦ hx) hc.2

theorem evolution_fixed {Time : Type t} (a : Action G X) (F : Time → X → X)
    (hF : ∀ s, Equivariant a a (F s)) {x : X} (hx : Fixed a x) :
    ∀ s, Fixed a (F s x) := fun s => equivariant_fixed a a (F s) (hF s) hx

theorem evolution_channel_fixed {Time : Type t} (a : Action G X) (b : Action G Y)
    (Φ : X → Y) (hΦ : Equivariant a b Φ) (F : Time → X → X)
    (hF : ∀ s, Equivariant a a (F s)) {x : X} (hx : Fixed a x) :
    ∀ s, Fixed b (Φ (F s x)) :=
  fun s => equivariant_fixed a b Φ hΦ (evolution_fixed a F hF hx s)

theorem evolution_no_contingency {Time : Type t} (a : Action G X) (b : Action G Y)
    (Φ : X → Y) (hΦ : Equivariant a b Φ) (F : Time → X → X)
    (hF : ∀ s, Equivariant a a (F s)) (other : Time → X → Prop)
    {x : X} (hx : Fixed a x) : ∀ s, ¬ ContingentWith b Φ (other s) (F s x) :=
  fun s => fixed_no_contingency a b Φ hΦ (other s) (evolution_fixed a F hF hx s)

def trajectory (step : Nat → X → X) (x : X) : Nat → X
  | 0 => x
  | n + 1 => step n (trajectory step x n)

theorem trajectory_equivariant (a : Action G X) (step : Nat → X → X)
    (hs : ∀ n, Equivariant a a (step n)) (n : Nat) :
    Equivariant a a (fun x => trajectory step x n) := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih => exact equivariant_composition a a a _ (step n) ih (hs n)

theorem trajectory_fixed (a : Action G X) (step : Nat → X → X)
    (hs : ∀ n, Equivariant a a (step n)) {x : X} (hx : Fixed a x) :
    ∀ n, Fixed a (trajectory step x n) :=
  fun n => equivariant_fixed a a _ (trajectory_equivariant a step hs n) hx

theorem trajectory_channel_fixed (a : Action G X) (b : Action G Y)
    (Φ : X → Y) (hΦ : Equivariant a b Φ) (step : Nat → X → X)
    (hs : ∀ n, Equivariant a a (step n)) {x : X} (hx : Fixed a x) :
    ∀ n, Fixed b (Φ (trajectory step x n)) :=
  fun n => equivariant_fixed a b Φ hΦ (trajectory_fixed a step hs hx n)

abbrev Channel (Challenge : Type v) (Response : Type w) (Value : Type z) :=
  Challenge → Response → Value

/-- The paper's inverse relabeling action, with challenge argument written first. -/
def channelAction {Challenge : Type v} {Response : Type w} {Value : Type z}
    (a : Action G Challenge) (b : Action G Response) :
    Action G (Channel Challenge Response Value) where
  act g Q c r := Q (a.act (G.inverse g) c) (b.act (G.inverse g) r)
  identity_act := by
    intro Q
    funext c r
    rw [inverse_identity, a.identity_act, b.identity_act]
  product_act := by
    intro g h Q
    funext c r
    rw [inverse_product, a.product_act, b.product_act]

theorem channel_action_formula {Challenge : Type v} {Response : Type w} {Value : Type z}
    (a : Action G Challenge) (b : Action G Response) (g : Γ)
    (Q : Channel Challenge Response Value) (c : Challenge) (r : Response) :
    (channelAction a b).act g Q c r =
      Q (a.act (G.inverse g) c) (b.act (G.inverse g) r) := rfl

theorem assay_fixed {Challenge : Type w} {Response : Type z} {Value : Type t}
    (a : Action G X) (ac : Action G Challenge) (ar : Action G Response)
    (Φ : X → Channel Challenge Response Value)
    (hΦ : Equivariant a (channelAction ac ar) Φ) {x : X} (hx : Fixed a x) :
    Fixed (channelAction ac ar) (Φ x) := equivariant_fixed a _ Φ hΦ hx

theorem assay_fixed_formula {Challenge : Type w} {Response : Type z} {Value : Type t}
    (a : Action G X) (ac : Action G Challenge) (ar : Action G Response)
    (Φ : X → Channel Challenge Response Value)
    (hΦ : Equivariant a (channelAction ac ar) Φ) {x : X} (hx : Fixed a x)
    (g : Γ) (c : Challenge) (r : Response) :
    Φ x (ac.act (G.inverse g) c) (ar.act (G.inverse g) r) = Φ x c r :=
  congrArg (fun Q : Channel Challenge Response Value => Q c r) (assay_fixed a ac ar Φ hΦ hx g)

end CausalFoundations.Symmetry

namespace CausalFoundations

open Symmetry

/-- Complete deterministic branch; stochastic Theorem 1 is not part of this endpoint. -/
theorem theorem1_deterministic {Γ : Type u} (G : SymmetryGroup Γ)
    {State : Type v} {Challenge : Type w} {Response : Type z} {Value : Type t} {Time : Type r}
    (a : Action G State) (ac : Action G Challenge) (ar : Action G Response)
    (Φ : State → Channel Challenge Response Value)
    (hΦ : Equivariant a (channelAction ac ar) Φ)
    (F : Time → State → State) (hF : ∀ s, Equivariant a a (F s)) :
    (∀ x, Fixed a x →
      Fixed (channelAction ac ar) (Φ x) ∧
      (∀ Q, Orbit (channelAction ac ar) (Φ x) Q ↔ Q = Φ x) ∧
      (∀ other, ¬ ContingentWith (channelAction ac ar) Φ other x)) ∧
    (∀ s x, Fixed a x →
      Fixed a (F s x) ∧ Fixed (channelAction ac ar) (Φ (F s x)) ∧
      (∀ Q, Orbit (channelAction ac ar) (Φ (F s x)) Q ↔ Q = Φ (F s x)) ∧
      (∀ other, ¬ ContingentWith (channelAction ac ar) Φ other (F s x))) := by
  constructor
  · intro x hx
    have hq := assay_fixed a ac ar Φ hΦ hx
    exact ⟨hq, (fixed_iff_singleton_orbit _ _).mp hq,
      fun other => fixed_no_contingency a _ Φ hΦ other hx⟩
  · intro s x hx
    have hs := evolution_fixed a F hF hx s
    have hq := assay_fixed a ac ar Φ hΦ hs
    exact ⟨hs, hq, (fixed_iff_singleton_orbit _ _).mp hq,
      fun other => fixed_no_contingency a _ Φ hΦ other hs⟩

end CausalFoundations
