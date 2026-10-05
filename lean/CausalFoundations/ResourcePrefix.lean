import Init

/-!
# Published Theorem 13: Cancellative prefix theorem

Source: Kai Liang, Causal Foundations and Experimental Certification of
Contingent Assignment, Heredity, and Reflexive Maintenance, v1.0, section 10.2.
DOI: 10.5281/zenodo.22902457.

This module retains the published commutative, cancellative monoid hypothesis.
Monoid laws are explicit fields of a mathematical input structure, not global
axioms. Cancellation is an explicit theorem hypothesis. Time is finite and
discrete. Stocks are not ordered real numbers; feasibility means algebraic
decomposability. No conclusion about chemistry, dissipation, or a stochastic
process is asserted. Theorem 14 (the CRK characterization) is not formalized here.
-/

namespace CausalFoundations

universe u

/-- Exactly the algebraic structure declared in the paper, before cancellation. -/
structure CommResourceMonoid (M : Type u) where
  zero : M
  add : M → M → M
  zero_add : ∀ x, add zero x = x
  add_zero : ∀ x, add x zero = x
  assoc : ∀ x y z, add (add x y) z = add x (add y z)
  comm : ∀ x y, add x y = add y x

/-- In a commutative monoid, left cancellation is the paper's cancellation. -/
def LeftCancellative {M : Type u} (R : CommResourceMonoid M) : Prop :=
  ∀ a b c, R.add a b = R.add a c → b = c

/-- The paper's intrinsic algebraic resource preorder, not an external order. -/
def Decomposes {M : Type u} (R : CommResourceMonoid M) (x y : M) : Prop :=
  ∃ r, R.add x r = y

/-- Sum over indices 0,...,t-1, with empty prefix zero. -/
def prefixSum {M : Type u} (R : CommResourceMonoid M) (x : Nat → M) : Nat → M
  | 0 => R.zero
  | t + 1 => R.add (prefixSum R x t) (x t)

def PrefixFeasible {M : Type u} (R : CommResourceMonoid M)
    (initial : M) (demand inflow : Nat → M) (horizon : Nat) : Prop :=
  ∀ t, t ≤ horizon →
    Decomposes R (prefixSum R demand t) (R.add initial (prefixSum R inflow t))

def SequentialFeasible {M : Type u} (R : CommResourceMonoid M)
    (initial : M) (demand inflow : Nat → M) (horizon : Nat) : Prop :=
  ∃ stock : Nat → M, stock 0 = initial ∧
    ∀ t, t < horizon → R.add (stock t) (inflow t) = R.add (demand t) (stock (t + 1))

theorem prefix_zero {M : Type u} (R : CommResourceMonoid M) (x : Nat → M) :
    prefixSum R x 0 = R.zero := rfl

theorem prefix_succ {M : Type u} (R : CommResourceMonoid M) (x : Nat → M) (t : Nat) :
    prefixSum R x (t + 1) = R.add (prefixSum R x t) (x t) := rfl

/-- Cancellation turns two consecutive prefix equations into a local balance. -/
theorem balance_of_adjacent_prefixes {M : Type u} (R : CommResourceMonoid M)
    (hc : LeftCancellative R) (a b r c i s : M)
    (hnow : R.add a r = b) (hnext : R.add (R.add a c) s = R.add b i) :
    R.add r i = R.add c s := by
  apply hc a
  calc
    R.add a (R.add r i) = R.add (R.add a r) i := (R.assoc a r i).symm
    _ = R.add b i := congrArg (fun x => R.add x i) hnow
    _ = R.add (R.add a c) s := hnext.symm
    _ = R.add a (R.add c s) := R.assoc a c s

/-- Telescoping balance; this direction does not require cancellation. -/
theorem cumulative_balance {M : Type u} (R : CommResourceMonoid M)
    (initial : M) (demand inflow stock : Nat → M) (horizon : Nat)
    (hzero : stock 0 = initial)
    (hstep : ∀ t, t < horizon →
      R.add (stock t) (inflow t) = R.add (demand t) (stock (t + 1))) :
    ∀ t, t ≤ horizon →
      R.add (prefixSum R demand t) (stock t) = R.add initial (prefixSum R inflow t) := by
  intro t
  induction t with
  | zero =>
    intro _
    change R.add R.zero (stock 0) = R.add initial R.zero
    rw [R.zero_add, R.add_zero, hzero]
  | succ t ih =>
    intro ht
    have hle : t ≤ horizon := Nat.le_of_succ_le ht
    have hlt : t < horizon := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht
    change R.add (R.add (prefixSum R demand t) (demand t)) (stock (t + 1)) =
      R.add initial (R.add (prefixSum R inflow t) (inflow t))
    calc
      R.add (R.add (prefixSum R demand t) (demand t)) (stock (t + 1)) =
          R.add (prefixSum R demand t) (R.add (demand t) (stock (t + 1))) :=
        R.assoc _ _ _
      _ = R.add (prefixSum R demand t) (R.add (stock t) (inflow t)) :=
        congrArg (fun x => R.add (prefixSum R demand t) x) (hstep t hlt).symm
      _ = R.add (R.add (prefixSum R demand t) (stock t)) (inflow t) :=
        (R.assoc _ _ _).symm
      _ = R.add (R.add initial (prefixSum R inflow t)) (inflow t) :=
        congrArg (fun x => R.add x (inflow t)) (ih hle)
      _ = R.add initial (R.add (prefixSum R inflow t) (inflow t)) := R.assoc _ _ _

theorem sequential_implies_prefix {M : Type u} (R : CommResourceMonoid M)
    (initial : M) (demand inflow : Nat → M) (horizon : Nat)
    (h : SequentialFeasible R initial demand inflow horizon) :
    PrefixFeasible R initial demand inflow horizon := by
  cases h with
  | intro stock hs =>
    intro t ht
    exact ⟨stock t, cumulative_balance R initial demand inflow stock horizon
      hs.1 hs.2 t ht⟩

theorem prefix_implies_sequential {M : Type u} (R : CommResourceMonoid M)
    (hc : LeftCancellative R) (initial : M) (demand inflow : Nat → M)
    (horizon : Nat) (h : PrefixFeasible R initial demand inflow horizon) :
    SequentialFeasible R initial demand inflow horizon := by
  classical
  have hex : ∀ t, ∃ r, t ≤ horizon →
      R.add (prefixSum R demand t) r = R.add initial (prefixSum R inflow t) := by
    intro t
    by_cases ht : t ≤ horizon
    · cases h t ht with
      | intro r hr => exact ⟨r, fun _ => hr⟩
    · exact ⟨R.zero, fun ht' => False.elim (ht ht')⟩
  let stock : Nat → M := fun t => Classical.choose (hex t)
  have hs : ∀ t, t ≤ horizon →
      R.add (prefixSum R demand t) (stock t) = R.add initial (prefixSum R inflow t) := by
    intro t ht
    exact Classical.choose_spec (hex t) ht
  refine ⟨stock, ?_, ?_⟩
  · have h0 := hs 0 (Nat.zero_le horizon)
    change R.add R.zero (stock 0) = R.add initial R.zero at h0
    rw [R.zero_add, R.add_zero] at h0
    exact h0
  · intro t ht
    exact balance_of_adjacent_prefixes R hc
      (prefixSum R demand t) (R.add initial (prefixSum R inflow t))
      (stock t) (demand t) (inflow t) (stock (t + 1))
      (hs t (Nat.le_of_lt ht))
      (by
        have hn := hs (t + 1) (Nat.succ_le_of_lt ht)
        change R.add (R.add (prefixSum R demand t) (demand t)) (stock (t + 1)) =
          R.add initial (R.add (prefixSum R inflow t) (inflow t)) at hn
        exact hn.trans (R.assoc initial (prefixSum R inflow t) (inflow t)).symm)

/-- FULL published Theorem 13, for every finite horizon, including zero. -/
theorem theorem13 {M : Type u} (R : CommResourceMonoid M)
    (hc : LeftCancellative R) (initial : M) (demand inflow : Nat → M)
    (horizon : Nat) :
    SequentialFeasible R initial demand inflow horizon ↔
      PrefixFeasible R initial demand inflow horizon :=
  ⟨sequential_implies_prefix R initial demand inflow horizon,
    prefix_implies_sequential R hc initial demand inflow horizon⟩

theorem residual_unique {M : Type u} (R : CommResourceMonoid M)
    (hc : LeftCancellative R) (a b r s : M)
    (hr : R.add a r = b) (hs : R.add a s = b) : r = s :=
  hc a r s (hr.trans hs.symm)

/-- Equal current prefix totals force equal residuals; future inputs are unused. -/
theorem residual_prefix_locality {M : Type u} (R : CommResourceMonoid M)
    (hc : LeftCancellative R) (a b a' b' r r' : M)
    (ha : a = a') (hb : b = b')
    (hr : R.add a r = b) (hr' : R.add a' r' = b') : r = r' := by
  subst a'
  subst b'
  exact residual_unique R hc a b r r' hr hr'

/-- Within the horizon, all feasible stock paths have the same actual stock. -/
theorem sequential_stock_unique {M : Type u} (R : CommResourceMonoid M)
    (hc : LeftCancellative R) (initial : M) (demand inflow stock stock' : Nat → M)
    (horizon : Nat) (h0 : stock 0 = initial) (h0' : stock' 0 = initial)
    (h : ∀ t, t < horizon →
      R.add (stock t) (inflow t) = R.add (demand t) (stock (t + 1)))
    (h' : ∀ t, t < horizon →
      R.add (stock' t) (inflow t) = R.add (demand t) (stock' (t + 1))) :
    ∀ t, t ≤ horizon → stock t = stock' t := by
  intro t ht
  exact residual_unique R hc _ _ _ _
    (cumulative_balance R initial demand inflow stock horizon h0 h t ht)
    (cumulative_balance R initial demand inflow stock' horizon h0' h' t ht)

def natResources : CommResourceMonoid Nat where
  zero := 0
  add := Nat.add
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  assoc := Nat.add_assoc
  comm := Nat.add_comm

theorem natResources_cancellative : LeftCancellative natResources := by
  intro a b c h
  exact Nat.add_left_cancel h

/-- A nonzero-demand, nonzero-inflow instance for every finite horizon. -/
theorem nonvacuity_nonzero (horizon : Nat) :
    SequentialFeasible natResources 3 (fun _ => 1) (fun _ => 1) horizon := by
  refine ⟨fun _ => 3, rfl, ?_⟩
  intro _ _
  rfl

theorem nonvacuity_prefix (horizon : Nat) :
    PrefixFeasible natResources 3 (fun _ => 1) (fun _ => 1) horizon :=
  (theorem13 natResources natResources_cancellative 3
    (fun _ => 1) (fun _ => 1) horizon).mp (nonvacuity_nonzero horizon)

end CausalFoundations
