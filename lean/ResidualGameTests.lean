import CausalFoundations.ResidualGame
import BoundaryTests

namespace CausalFoundations.Tests

/-- The truncated-addition example has no viable initial state at stock one. -/
theorem truncated_root_not_viable : ¬ CRK.Wmax saturated (CRK.root saturated Stock.one) := by
  intro h
  have hfirst : CRK.admissible saturated (CRK.root saturated Stock.one) ⟨.one, .zero⟩ :=
    ⟨Stock.zero, rfl⟩
  obtain ⟨r, hr, hn⟩ := (CRK.wmax_invariant saturated).2 _ h ⟨.one, .zero⟩ hfirst
  have he : r = Stock.zero := by
    change Stock.one = addStock Stock.one r at hr
    cases r with
    | zero => rfl
    | one => cases hr
    | two => cases hr
  subst r
  have hsecond : CRK.admissible saturated
      (CRK.next saturated (CRK.root saturated Stock.one) ⟨.one, .zero⟩ Stock.zero)
      ⟨.two, .one⟩ := ⟨Stock.zero, rfl⟩
  obtain ⟨s, hs, _⟩ := (CRK.wmax_invariant saturated).2 _ hn ⟨.two, .one⟩ hsecond
  change Stock.one = Stock.two at hs
  cases hs

theorem truncated_no_winning_policies : ¬ CRK.WinningPolicies saturated := by
  intro h
  exact truncated_root_not_viable ((theorem14 saturated).1.mp h Stock.one)

def booleanResources : CommResourceMonoid Bool where
  zero := false
  add := Bool.or
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  comm := by intro a b; cases a <;> cases b <;> rfl

theorem boolean_not_cancellative : ¬ LeftCancellative booleanResources := by
  intro h
  have bad : false = true := h true false true rfl
  cases bad

/-- An idempotent, noncancellative monoid with explicit viable residual subfibers. -/
theorem boolean_viable_subfibers : CRK.ViableSubfibers booleanResources := by
  refine ⟨(fun a b r => (a || b) = b ∧ r = b), ?_, ?_, ?_⟩
  · intro a b r hr
    rcases hr with ⟨hab, he⟩
    subst r
    exact hab
  · intro a b hab
    obtain ⟨q, hq⟩ := hab
    refine ⟨b, ?_, rfl⟩
    cases a <;> cases b <;> cases q <;> cases hq <;> rfl
  · intro a b r c i hr hm
    rcases hr with ⟨hab, he⟩
    subst r
    obtain ⟨q, hq⟩ := hm
    refine ⟨b || i, ?_, ?_, rfl⟩
    · cases a <;> cases b <;> cases c <;> cases i <;> cases q <;> cases hq <;> rfl
    · cases a <;> cases b <;> cases c <;> cases i <;> cases q <;> cases hq <;> rfl

theorem boolean_winning_policies : CRK.WinningPolicies booleanResources :=
  (theorem14 booleanResources).1.mpr
    ((theorem14 booleanResources).2.mpr boolean_viable_subfibers)

#print axioms truncated_root_not_viable
#print axioms truncated_no_winning_policies
#print axioms boolean_not_cancellative
#print axioms boolean_viable_subfibers
#print axioms boolean_winning_policies

end CausalFoundations.Tests
