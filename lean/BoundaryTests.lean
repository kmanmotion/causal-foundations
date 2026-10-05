import CausalFoundations

namespace CausalFoundations.Tests

/-- Zero-horizon semantics do not impose a spurious time-zero transition. -/
theorem zero_horizon {M : Type} (R : CommResourceMonoid M)
    (b : M) (c i : Nat → M) : SequentialFeasible R b c i 0 := by
  refine ⟨fun _ => b, rfl, ?_⟩
  intro t ht
  exact False.elim (Nat.not_lt_zero t ht)

/-- The target monoid in the published truncated-addition counterexample. -/
inductive Stock where
  | zero | one | two
  deriving DecidableEq, Repr

def addStock : Stock → Stock → Stock
  | .zero, b => b
  | .one, .zero => .one
  | .one, _ => .two
  | .two, _ => .two

def saturated : CommResourceMonoid Stock where
  zero := .zero
  add := addStock
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  comm := by intro a b; cases a <;> cases b <;> rfl

def demands : Nat → Stock
  | 0 => .one
  | _ + 1 => .two

def inflows : Nat → Stock
  | 0 => .zero
  | _ + 1 => .one

theorem not_cancellative : ¬ LeftCancellative saturated := by
  intro h
  have bad : Stock.zero = Stock.one := h .two .zero .one rfl
  cases bad

theorem aggregate_feasible : PrefixFeasible saturated .one demands inflows 2 := by
  intro t ht
  cases t with
  | zero => exact ⟨Stock.one, rfl⟩
  | succ t =>
    cases t with
    | zero => exact ⟨Stock.zero, rfl⟩
    | succ t =>
      cases t with
      | zero => exact ⟨Stock.zero, rfl⟩
      | succ k =>
        have bad : Nat.succ k ≤ 0 :=
          Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ ht)
        exact False.elim (Nat.not_succ_le_zero k bad)

theorem not_sequential : ¬ SequentialFeasible saturated .one demands inflows 2 := by
  intro h
  cases h with
  | intro stock hs =>
    have first := hs.2 0 (by decide)
    rw [hs.1] at first
    change Stock.one = addStock Stock.one (stock 1) at first
    have forced : stock 1 = Stock.zero := by
      cases hx : stock 1 with
      | zero => rfl
      | one => rw [hx] at first; cases first
      | two => rw [hx] at first; cases first
    have second := hs.2 1 (by decide)
    rw [forced] at second
    change Stock.one = Stock.two at second
    cases second

/-- Without cancellation, prefix feasibility is not sufficient in general.
This does NOT say cancellation is necessary for every prefix-complete monoid.
The quotient homomorphism from Nat is not part of this boundary test. -/
theorem omission_counterexample :
    PrefixFeasible saturated .one demands inflows 2 ∧
      ¬ SequentialFeasible saturated .one demands inflows 2 :=
  ⟨aggregate_feasible, not_sequential⟩

#print axioms zero_horizon
#print axioms not_cancellative
#print axioms aggregate_feasible
#print axioms not_sequential
#print axioms omission_counterexample

end CausalFoundations.Tests
