import CausalFoundations.FixedSet

/-!
# Published Theorem 2: symmetry-quotient erasure

Source: Causal Foundations v1.0, section 3.2, pages 5–6.
DOI: 10.5281/zenodo.22902457.

The orbit quotient is constructed from the actual group action. Factorization
and assay equivariance are required only on the declared group-stable domain.
Reachability stability is also derived for equivariant transition relations
and families whose intervention labels are transported by the group.
-/

namespace CausalFoundations.Symmetry

universe u v w z t

variable {Γ : Type u} {G : SymmetryGroup Γ} {X : Type v} {Y : Type w}

theorem inverse_act_act (a : Action G X) (g : Γ) (x : X) :
    a.act (G.inverse g) (a.act g x) = x := by
  rw [← a.product_act, G.inverse_left, a.identity_act]

theorem orbit_symm (a : Action G X) {x y : X} (h : Orbit a x y) :
    Orbit a y x := by
  obtain ⟨g, hg⟩ := h
  exact ⟨G.inverse g, (congrArg (a.act (G.inverse g)) hg).symm.trans
    (inverse_act_act a g x)⟩

theorem orbit_trans (a : Action G X) {x y z : X}
    (hxy : Orbit a x y) (hyz : Orbit a y z) : Orbit a x z := by
  obtain ⟨g, hg⟩ := hxy
  obtain ⟨h, hh⟩ := hyz
  exact ⟨G.product h g, (a.product_act h g x).trans
    ((congrArg (a.act h) hg).trans hh)⟩

def orbitSetoid (a : Action G X) : Setoid X where
  r := Orbit a
  iseqv := ⟨orbit_self a, orbit_symm a, orbit_trans a⟩

abbrev OrbitQuotient (a : Action G X) := Quotient (orbitSetoid a)

def orbitClass (a : Action G X) (x : X) : OrbitQuotient a :=
  Quotient.mk (orbitSetoid a) x

theorem orbit_class_eq_iff (a : Action G X) (x y : X) :
    orbitClass a x = orbitClass a y ↔ Orbit a x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem orbit_class_act (a : Action G X) (g : Γ) (x : X) :
    orbitClass a (a.act g x) = orbitClass a x :=
  (Quotient.sound (s := orbitSetoid a) ⟨g, rfl⟩).symm

def GroupStable (a : Action G X) (D : X → Prop) : Prop :=
  ∀ g x, D x → D (a.act g x)

def EquivariantOn (a : Action G X) (b : Action G Y) (D : X → Prop)
    (Φ : X → Y) : Prop := ∀ g x, D x → Φ (a.act g x) = b.act g (Φ x)

def FactorsOn (a : Action G X) (D : X → Prop) (Φ : X → Y) : Prop :=
  ∃ bar : OrbitQuotient a → Y, ∀ x, D x → Φ x = bar (orbitClass a x)

theorem stable_orbit_membership (a : Action G X) (D : X → Prop)
    (hD : GroupStable a D) {x y : X} (hxy : Orbit a x y) : D x ↔ D y := by
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := hxy
    exact hg ▸ hD g x hx
  · intro hy
    obtain ⟨g, hg⟩ := orbit_symm a hxy
    exact hg ▸ hD g y hy

theorem restrict_equivariance (a : Action G X) (b : Action G Y) (D : X → Prop)
    (Φ : X → Y) (hΦ : Equivariant a b Φ) : EquivariantOn a b D Φ :=
  fun g x _ => hΦ g x

theorem factor_restrict (a : Action G X) (D E : X → Prop) (Φ : X → Y)
    (hsub : ∀ x, E x → D x) (hf : FactorsOn a D Φ) : FactorsOn a E Φ := by
  obtain ⟨bar, hbar⟩ := hf
  exact ⟨bar, fun x hx => hbar x (hsub x hx)⟩

theorem factor_orbit_constant (a : Action G X) (D : X → Prop) (Φ : X → Y)
    (hf : FactorsOn a D Φ) {x y : X} (hx : D x) (hy : D y)
    (hxy : Orbit a x y) : Φ y = Φ x := by
  obtain ⟨bar, hbar⟩ := hf
  exact (hbar y hy).trans ((congrArg bar (Quotient.sound
    (s := orbitSetoid a) hxy).symm).trans (hbar x hx).symm)

theorem factor_invariant (a : Action G X) (D : X → Prop) (Φ : X → Y)
    (hD : GroupStable a D) (hf : FactorsOn a D Φ) {x : X} (hx : D x) :
    ∀ g, Φ (a.act g x) = Φ x :=
  fun g => factor_orbit_constant a D Φ hf hx (hD g x hx) ⟨g, rfl⟩

theorem factor_fixed (a : Action G X) (b : Action G Y) (D : X → Prop)
    (Φ : X → Y) (hD : GroupStable a D) (hΦ : EquivariantOn a b D Φ)
    (hf : FactorsOn a D Φ) {x : X} (hx : D x) : Fixed b (Φ x) :=
  fun g => (hΦ g x hx).symm.trans (factor_invariant a D Φ hD hf hx g)

theorem factor_singleton (a : Action G X) (b : Action G Y) (D : X → Prop)
    (Φ : X → Y) (hD : GroupStable a D) (hΦ : EquivariantOn a b D Φ)
    (hf : FactorsOn a D Φ) {x : X} (hx : D x) :
    ∀ y, Orbit b (Φ x) y ↔ y = Φ x :=
  (fixed_iff_singleton_orbit b (Φ x)).mp (factor_fixed a b D Φ hD hΦ hf hx)

theorem factor_no_contingency (a : Action G X) (b : Action G Y) (D : X → Prop)
    (Φ : X → Y) (hD : GroupStable a D) (hΦ : EquivariantOn a b D Φ)
    (hf : FactorsOn a D Φ) (other : X → Prop) {x : X} (hx : D x) :
    ¬ ContingentWith b Φ other x :=
  fun hc => fixed_no_nontrivial_orbit b (factor_fixed a b D Φ hD hΦ hf hx) hc.2

theorem nontrivial_prevents_factorization (a : Action G X) (b : Action G Y)
    (D : X → Prop) (Φ : X → Y) (hD : GroupStable a D)
    (hΦ : EquivariantOn a b D Φ) {x : X} (hx : D x)
    (hn : NontrivialOrbit b (Φ x)) : ¬ FactorsOn a D Φ :=
  fun hf => fixed_no_nontrivial_orbit b (factor_fixed a b D Φ hD hΦ hf hx) hn

/-- Finite admissible paths from the declared preparation set. -/
inductive Reachable (P : X → Prop) (R : X → X → Prop) : X → Prop
  | initial {x} : P x → Reachable P R x
  | step {x y} : Reachable P R x → R x y → Reachable P R y

def TransitionEquivariant (a : Action G X) (R : X → X → Prop) : Prop :=
  ∀ g x y, R x y → R (a.act g x) (a.act g y)

theorem reachable_least (P D : X → Prop) (R : X → X → Prop)
    (hP : ∀ x, P x → D x) (hR : ∀ x y, D x → R x y → D y) :
    ∀ x, Reachable P R x → D x := by
  intro x hx
  induction hx with
  | initial hp => exact hP _ hp
  | step _ hr ih => exact hR _ _ ih hr

theorem reachable_stable (a : Action G X) (P : X → Prop) (R : X → X → Prop)
    (hP : GroupStable a P) (hR : TransitionEquivariant a R) :
    GroupStable a (Reachable P R) := by
  intro g x hx
  induction hx with
  | initial hp => exact Reachable.initial (hP g _ hp)
  | step _ hr ih => exact Reachable.step ih (hR g _ _ hr)

def AllowedStep {Label : Type w} (family : Label → X → X → Prop) (x y : X) : Prop :=
  ∃ i, family i x y

def FamilyEquivariant {Label : Type w} (a : Action G X) (labels : Action G Label)
    (family : Label → X → X → Prop) : Prop :=
  ∀ g i x y, family i x y → family (labels.act g i) (a.act g x) (a.act g y)

theorem allowed_step_equivariant {Label : Type w} (a : Action G X)
    (labels : Action G Label) (family : Label → X → X → Prop)
    (hf : FamilyEquivariant a labels family) :
    TransitionEquivariant a (AllowedStep family) := by
  intro g x y ⟨i, hi⟩
  exact ⟨labels.act g i, hf g i x y hi⟩

theorem reachable_family_stable {Label : Type w} (a : Action G X)
    (labels : Action G Label) (P : X → Prop) (family : Label → X → X → Prop)
    (hP : GroupStable a P) (hf : FamilyEquivariant a labels family) :
    GroupStable a (Reachable P (AllowedStep family)) :=
  reachable_stable a P _ hP (allowed_step_equivariant a labels family hf)

theorem reachable_erasure_fixed (a : Action G X) (b : Action G Y)
    (P : X → Prop) (R : X → X → Prop) (Φ : X → Y)
    (hP : GroupStable a P) (hR : TransitionEquivariant a R)
    (hΦ : EquivariantOn a b (Reachable P R) Φ)
    (hf : FactorsOn a (Reachable P R) Φ) :
    ∀ x, Reachable P R x → Fixed b (Φ x) :=
  fun _ hx => factor_fixed a b _ Φ (reachable_stable a P R hP hR) hΦ hf hx

end CausalFoundations.Symmetry

namespace CausalFoundations

open Symmetry

/-- Published Theorem 2 on the actual orbit quotient and declared stable domain. -/
theorem theorem2 {Γ : Type u} (G : SymmetryGroup Γ)
    {State : Type v} {Challenge : Type w} {Response : Type z} {Value : Type t}
    (a : Action G State) (ac : Action G Challenge) (ar : Action G Response)
    (D : State → Prop) (Φ : State → Channel Challenge Response Value)
    (hD : GroupStable a D) (hΦ : EquivariantOn a (channelAction ac ar) D Φ)
    (hf : FactorsOn a D Φ) :
    ∀ x, D x →
      (∀ g, Φ (a.act g x) = Φ x) ∧
      Fixed (channelAction ac ar) (Φ x) ∧
      (∀ Q, Orbit (channelAction ac ar) (Φ x) Q ↔ Q = Φ x) ∧
      (∀ other, ¬ ContingentWith (channelAction ac ar) Φ other x) := by
  intro x hx
  exact ⟨factor_invariant a D Φ hD hf hx,
    factor_fixed a _ D Φ hD hΦ hf hx,
    factor_singleton a _ D Φ hD hΦ hf hx,
    fun other => factor_no_contingency a _ D Φ hD hΦ hf other hx⟩

end CausalFoundations
