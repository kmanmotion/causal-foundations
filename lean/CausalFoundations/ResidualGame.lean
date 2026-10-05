import CausalFoundations.ResourcePrefix

/-!
# Published Theorem 14: exact causal residual kernel characterization

Baseline: Causal Foundations v1.0, section 11.2.
DOI: 10.5281/zenodo.22902457.
Policies may depend on arbitrary finite observed histories. Nonanticipation is
an explicit prefix-congruence property; no future move may affect current stock.
The selector constructed from invariance is set-theoretic. No measurability,
continuity, computability, cancellation, or finiteness of the monoid is assumed.
-/

namespace CausalFoundations
namespace CRK

universe u

structure Move (M : Type u) where
  demand : M
  inflow : M

structure State (M : Type u) where
  demand : M
  supply : M
  residual : M

variable {M : Type u} (R : CommResourceMonoid M)

def zeroMove : Move M := ⟨R.zero, R.zero⟩
def root (b : M) : State M := ⟨R.zero, b, b⟩
def Omega (x : State M) : Prop := R.add x.demand x.residual = x.supply

def admissible (x : State M) (m : Move M) : Prop :=
  Decomposes R (R.add x.demand m.demand) (R.add x.supply m.inflow)

def legal (x : State M) (m : Move M) (s : M) : Prop :=
  R.add x.residual m.inflow = R.add m.demand s

def next (x : State M) (m : Move M) (s : M) : State M :=
  ⟨R.add x.demand m.demand, R.add x.supply m.inflow, s⟩

def Invariant (W : State M → Prop) : Prop :=
  (∀ x, W x → Omega R x) ∧
  ∀ x, W x → ∀ m, admissible R x m →
    ∃ s, legal R x m s ∧ W (next R x m s)

def Wmax (x : State M) : Prop := ∃ W, Invariant R W ∧ W x

def AllRoots : Prop := ∀ b, Wmax R (root R b)

def ViableSubfibers : Prop := ∃ V : M → M → M → Prop,
  (∀ a b r, V a b r → R.add a r = b) ∧
  (∀ a b, Decomposes R a b → ∃ r, V a b r) ∧
  (∀ a b r c i, V a b r → Decomposes R (R.add a c) (R.add b i) →
    ∃ s, R.add r i = R.add c s ∧ V (R.add a c) (R.add b i) s)

theorem root_omega (b : M) : Omega R (root R b) := R.zero_add b

theorem next_omega (x : State M) (m : Move M) (s : M)
    (hx : Omega R x) (hs : legal R x m s) : Omega R (next R x m s) := by
  change R.add (R.add x.demand m.demand) s = R.add x.supply m.inflow
  calc
    R.add (R.add x.demand m.demand) s = R.add x.demand (R.add m.demand s) := R.assoc _ _ _
    _ = R.add x.demand (R.add x.residual m.inflow) := congrArg (R.add x.demand) hs.symm
    _ = R.add (R.add x.demand x.residual) m.inflow := (R.assoc _ _ _).symm
    _ = R.add x.supply m.inflow := congrArg (fun z => R.add z m.inflow) hx

theorem wmax_invariant : Invariant R (Wmax R) := by
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW⟩ := hx
    exact hW.1 x hxW
  · intro x hx m hm
    obtain ⟨W, hW, hxW⟩ := hx
    obtain ⟨s, hs, hn⟩ := hW.2 x hxW m hm
    exact ⟨s, hs, W, hW, hn⟩

def Stream (M : Type u) := Nat → Move M
/-- Stock after t observed moves, indexed by a full stream for extensional comparison. -/
def Policy (M : Type u) := Stream M → Nat → M

def SamePrefix (σ τ : Stream M) (n : Nat) : Prop := ∀ k, k < n → σ k = τ k

def Nonanticipating (π : Policy M) : Prop :=
  ∀ σ τ n, SamePrefix σ τ n → π σ n = π τ n

def AllPrefixes (b : M) (σ : Stream M) : Prop :=
  ∀ t, Decomposes R (prefixSum R (fun k => (σ k).demand) t)
    (R.add b (prefixSum R (fun k => (σ k).inflow) t))

def stateAt (b : M) (π : Policy M) (σ : Stream M) (t : Nat) : State M :=
  ⟨prefixSum R (fun k => (σ k).demand) t,
   R.add b (prefixSum R (fun k => (σ k).inflow) t), π σ t⟩

def Winning (b : M) (π : Policy M) : Prop :=
  Nonanticipating π ∧ (∀ σ, π σ 0 = b) ∧
  ∀ σ, AllPrefixes R b σ → ∀ t,
    R.add (π σ t) (σ t).inflow = R.add (σ t).demand (π σ (t + 1))

def WinningPolicies : Prop := ∀ b, ∃ π, Winning R b π

theorem prefix_congr (f g : Nat → M) (n : Nat)
    (h : ∀ k, k < n → f k = g k) : prefixSum R f n = prefixSum R g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change R.add (prefixSum R f n) (f n) = R.add (prefixSum R g n) (g n)
    rw [ih (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n))), h n (Nat.lt_succ_self n)]

theorem stateAt_prefix (b : M) (π : Policy M) (hπ : Nonanticipating π)
    (σ τ : Stream M) (t : Nat) (h : SamePrefix σ τ t) :
    stateAt R b π σ t = stateAt R b π τ t := by
  have hd := prefix_congr R (fun k => (σ k).demand) (fun k => (τ k).demand) t
    (fun k hk => congrArg Move.demand (h k hk))
  have hi := prefix_congr R (fun k => (σ k).inflow) (fun k => (τ k).inflow) t
    (fun k hk => congrArg Move.inflow (h k hk))
  unfold stateAt
  rw [hd, hi, hπ σ τ t h]

theorem stateAt_zero (b : M) (π : Policy M) (h0 : ∀ σ, π σ 0 = b) (σ : Stream M) :
    stateAt R b π σ 0 = root R b := by
  unfold stateAt root
  simp only [prefixSum, R.add_zero, h0]

theorem stateAt_succ (b : M) (π : Policy M) (σ : Stream M) (t : Nat) :
    stateAt R b π σ (t + 1) = next R (stateAt R b π σ t) (σ t) (π σ (t + 1)) := by
  unfold stateAt next
  simp only [prefixSum]
  rw [R.assoc]

theorem winning_state_omega (b : M) (π : Policy M) (hπ : Winning R b π)
    (σ : Stream M) (hσ : AllPrefixes R b σ) (t : Nat) : Omega R (stateAt R b π σ t) := by
  exact cumulative_balance R b (fun k => (σ k).demand) (fun k => (σ k).inflow)
    (π σ) t (hπ.2.1 σ) (fun k _ => hπ.2.2 σ hσ k) t (Nat.le_refl t)

/-- Preserve the past, insert an arbitrary current move, and pad the future with zero. -/
def extend (σ : Stream M) (n : Nat) (m : Move M) : Stream M := fun k =>
  if k < n then σ k else if k = n then m else zeroMove R

theorem extend_prefix (σ : Stream M) (n : Nat) (m : Move M) :
    SamePrefix (extend R σ n m) σ n := by
  intro k hk
  simp only [extend, if_pos hk]

theorem extend_current (σ : Stream M) (n : Nat) (m : Move M) :
    extend R σ n m n = m := by
  simp only [extend, Nat.lt_irrefl, if_false, if_true]

theorem extend_future (σ : Stream M) (n : Nat) (m : Move M) (k : Nat) (hk : n < k) :
    extend R σ n m k = zeroMove R := by
  simp only [extend, if_neg (Nat.not_lt_of_ge (Nat.le_of_lt hk)),
    if_neg (Nat.ne_of_gt hk)]

theorem prefix_zero_tail (f : Nat → M) (n : Nat)
    (hf : ∀ k, n ≤ k → f k = R.zero) (t : Nat) (ht : n ≤ t) :
    prefixSum R f t = prefixSum R f n := by
  induction t with
  | zero =>
    have hn : n = 0 := Nat.eq_zero_of_le_zero ht
    subst n
    rfl
  | succ t ih =>
    by_cases hn : n ≤ t
    · change R.add (prefixSum R f t) (f t) = prefixSum R f n
      rw [hf t hn, R.add_zero, ih hn]
    · have he : n = t + 1 := Nat.le_antisymm ht (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
      rw [he]

theorem extend_allPrefixes (b : M) (π : Policy M) (σ : Stream M)
    (hσ : AllPrefixes R b σ) (n : Nat) (m : Move M)
    (hm : admissible R (stateAt R b π σ n) m) : AllPrefixes R b (extend R σ n m) := by
  let τ := extend R σ n m
  have hd : ∀ t, t ≤ n → prefixSum R (fun k => (τ k).demand) t =
      prefixSum R (fun k => (σ k).demand) t := by
    intro t ht
    apply prefix_congr R
    intro k hk
    exact congrArg Move.demand (extend_prefix R σ n m k (Nat.lt_of_lt_of_le hk ht))
  have hi : ∀ t, t ≤ n → prefixSum R (fun k => (τ k).inflow) t =
      prefixSum R (fun k => (σ k).inflow) t := by
    intro t ht
    apply prefix_congr R
    intro k hk
    exact congrArg Move.inflow (extend_prefix R σ n m k (Nat.lt_of_lt_of_le hk ht))
  have hn : Decomposes R (prefixSum R (fun k => (τ k).demand) (n + 1))
      (R.add b (prefixSum R (fun k => (τ k).inflow) (n + 1))) := by
    change Decomposes R
      (R.add (prefixSum R (fun k => (τ k).demand) n) (τ n).demand)
      (R.add b (R.add (prefixSum R (fun k => (τ k).inflow) n) (τ n).inflow))
    rw [hd n (Nat.le_refl n), hi n (Nat.le_refl n)]
    change Decomposes R
      (R.add (prefixSum R (fun k => (σ k).demand) n) (extend R σ n m n).demand)
      (R.add b (R.add (prefixSum R (fun k => (σ k).inflow) n) (extend R σ n m n).inflow))
    rw [extend_current, ← R.assoc]
    exact hm
  intro t
  change Decomposes R (prefixSum R (fun k => (τ k).demand) t)
    (R.add b (prefixSum R (fun k => (τ k).inflow) t))
  by_cases ht : t ≤ n
  · rw [hd t ht, hi t ht]
    exact hσ t
  · have hnt : n + 1 ≤ t := Nat.succ_le_of_lt (Nat.lt_of_not_ge ht)
    have hd0 : ∀ k, n + 1 ≤ k → (τ k).demand = R.zero := by
      intro k hk
      exact congrArg Move.demand (extend_future R σ n m k (Nat.lt_of_succ_le hk))
    have hi0 : ∀ k, n + 1 ≤ k → (τ k).inflow = R.zero := by
      intro k hk
      exact congrArg Move.inflow (extend_future R σ n m k (Nat.lt_of_succ_le hk))
    rw [prefix_zero_tail R _ (n + 1) hd0 t hnt, prefix_zero_tail R _ (n + 1) hi0 t hnt]
    exact hn

theorem zero_prefix (t : Nat) : prefixSum R (fun _ => R.zero) t = R.zero := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change R.add (prefixSum R (fun _ => R.zero) t) R.zero = R.zero
    rw [R.add_zero, ih]

theorem zero_stream_feasible (b : M) : AllPrefixes R b (fun _ => zeroMove R) := by
  intro t
  change Decomposes R (prefixSum R (fun _ => R.zero) t)
    (R.add b (prefixSum R (fun _ => R.zero) t))
  rw [zero_prefix, R.add_zero]
  exact ⟨b, R.zero_add b⟩

def Reachable (b : M) (π : Policy M) (x : State M) : Prop :=
  ∃ σ, AllPrefixes R b σ ∧ ∃ t, stateAt R b π σ t = x

theorem reachable_invariant (b : M) (π : Policy M) (hπ : Winning R b π) :
    Invariant R (Reachable R b π) := by
  constructor
  · intro x hx
    obtain ⟨σ, hσ, t, rfl⟩ := hx
    exact winning_state_omega R b π hπ σ hσ t
  · intro x hx m hm
    obtain ⟨σ, hσ, t, rfl⟩ := hx
    let τ := extend R σ t m
    have hτ : AllPrefixes R b τ := extend_allPrefixes R b π σ hσ t m hm
    have hp : stateAt R b π τ t = stateAt R b π σ t :=
      stateAt_prefix R b π hπ.1 τ σ t (extend_prefix R σ t m)
    have hc : τ t = m := extend_current R σ t m
    refine ⟨π τ (t + 1), ?_, τ, hτ, t + 1, ?_⟩
    · have hb := hπ.2.2 τ hτ t
      have hr : π τ t = π σ t := congrArg State.residual hp
      rw [hr, hc] at hb
      exact hb
    · rw [stateAt_succ, hp, hc]

theorem winning_root (b : M) (π : Policy M) (hπ : Winning R b π) :
    Wmax R (root R b) := by
  refine ⟨Reachable R b π, reachable_invariant R b π hπ, ?_⟩
  exact ⟨(fun _ => zeroMove R), zero_stream_feasible R b, 0,
    stateAt_zero R b π hπ.2.1 (fun _ => zeroMove R)⟩

theorem policies_imply_roots (h : WinningPolicies R) : AllRoots R := by
  intro b
  obtain ⟨π, hπ⟩ := h b
  exact winning_root R b π hπ

/-- A set-theoretic successor selector. Its value outside the viable domain is immaterial. -/
noncomputable def response (x : State M) (m : Move M) : M := by
  classical
  exact if h : Wmax R x ∧ admissible R x m then
    Classical.choose ((wmax_invariant R).2 x h.1 m h.2) else R.zero

theorem response_spec (x : State M) (hx : Wmax R x) (m : Move M)
    (hm : admissible R x m) :
    legal R x m (response R x m) ∧ Wmax R (next R x m (response R x m)) := by
  unfold response
  rw [dif_pos ⟨hx, hm⟩]
  exact Classical.choose_spec ((wmax_invariant R).2 x hx m hm)

/-- Recursion consults the current state and current move, never future moves. -/
def play (F : State M → Move M → M) (b : M) (σ : Stream M) : Nat → State M
  | 0 => root R b
  | t + 1 => next R (play F b σ t) (σ t) (F (play F b σ t) (σ t))

def policyOf (F : State M → Move M → M) (b : M) : Policy M :=
  fun σ t => (play R F b σ t).residual

theorem play_prefix (F : State M → Move M → M) (b : M) (σ τ : Stream M)
    (t : Nat) (h : SamePrefix σ τ t) : play R F b σ t = play R F b τ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp : SamePrefix σ τ t := fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self t))
    simp only [play, ih hp, h t (Nat.lt_succ_self t)]

theorem policyOf_nonanticipating (F : State M → Move M → M) (b : M) :
    Nonanticipating (policyOf R F b) := by
  intro σ τ t h
  exact congrArg State.residual (play_prefix R F b σ τ t h)

theorem play_totals (F : State M → Move M → M) (b : M) (σ : Stream M) (t : Nat) :
    (play R F b σ t).demand = prefixSum R (fun k => (σ k).demand) t ∧
    (play R F b σ t).supply = R.add b (prefixSum R (fun k => (σ k).inflow) t) := by
  induction t with
  | zero => exact ⟨rfl, (R.add_zero b).symm⟩
  | succ t ih =>
    constructor
    · change R.add (play R F b σ t).demand (σ t).demand =
        R.add (prefixSum R (fun k => (σ k).demand) t) (σ t).demand
      rw [ih.1]
    · change R.add (play R F b σ t).supply (σ t).inflow =
        R.add b (R.add (prefixSum R (fun k => (σ k).inflow) t) (σ t).inflow)
      rw [ih.2, R.assoc]

theorem play_stateAt (F : State M → Move M → M) (b : M) (σ : Stream M) (t : Nat) :
    stateAt R b (policyOf R F b) σ t = play R F b σ t := by
  have hd := (play_totals R F b σ t).1
  have hi := (play_totals R F b σ t).2
  unfold stateAt policyOf
  rw [← hd, ← hi]

theorem play_admissible (F : State M → Move M → M) (b : M) (σ : Stream M)
    (hσ : AllPrefixes R b σ) (t : Nat) : admissible R (play R F b σ t) (σ t) := by
  unfold admissible
  rw [(play_totals R F b σ t).1, (play_totals R F b σ t).2, R.assoc]
  exact hσ (t + 1)

theorem play_stays (W : State M → Prop) (F : State M → Move M → M)
    (hF : ∀ x, W x → ∀ m, admissible R x m →
      legal R x m (F x m) ∧ W (next R x m (F x m)))
    (b : M) (hb : W (root R b)) (σ : Stream M) (hσ : AllPrefixes R b σ) (t : Nat) :
    W (play R F b σ t) := by
  induction t with
  | zero => exact hb
  | succ t ih => exact (hF (play R F b σ t) ih (σ t) (play_admissible R F b σ hσ t)).2

theorem memoryless_winning (W : State M → Prop) (F : State M → Move M → M)
    (hF : ∀ x, W x → ∀ m, admissible R x m →
      legal R x m (F x m) ∧ W (next R x m (F x m)))
    (b : M) (hb : W (root R b)) : Winning R b (policyOf R F b) := by
  refine ⟨policyOf_nonanticipating R F b, (fun _ => rfl), ?_⟩
  intro σ hσ t
  exact (hF (play R F b σ t) (play_stays R W F hF b hb σ hσ t)
    (σ t) (play_admissible R F b σ hσ t)).1

theorem roots_imply_memoryless (h : AllRoots R) :
    ∃ F : State M → Move M → M, ∀ b, Winning R b (policyOf R F b) := by
  exact ⟨response R, fun b => memoryless_winning R (Wmax R) (response R)
    (response_spec R) b (h b)⟩

theorem roots_imply_policies (h : AllRoots R) : WinningPolicies R := by
  obtain ⟨F, hF⟩ := roots_imply_memoryless R h
  exact fun b => ⟨policyOf R F b, hF b⟩

theorem roots_imply_subfibers (h : AllRoots R) : ViableSubfibers R := by
  refine ⟨(fun a b r => Wmax R ⟨a, b, r⟩), ?_, ?_, ?_⟩
  · intro a b r hr
    exact (wmax_invariant R).1 ⟨a, b, r⟩ hr
  · intro a b hab
    have hm : admissible R (root R b) ⟨a, R.zero⟩ := by
      simpa only [admissible, root, R.zero_add, R.add_zero] using hab
    obtain ⟨r, _, hr⟩ := (wmax_invariant R).2 (root R b) (h b) ⟨a, R.zero⟩ hm
    refine ⟨r, ?_⟩
    simpa only [next, root, R.zero_add, R.add_zero] using hr
  · intro a b r c i hr hm
    exact (wmax_invariant R).2 ⟨a, b, r⟩ hr ⟨c, i⟩ hm

theorem subfibers_imply_roots (h : ViableSubfibers R) : AllRoots R := by
  obtain ⟨V, hvalid, hnonempty, hclosed⟩ := h
  let W : State M → Prop := fun x => V x.demand x.supply x.residual
  have hW : Invariant R W := by
    constructor
    · intro x hx
      exact hvalid x.demand x.supply x.residual hx
    · intro x hx m hm
      exact hclosed x.demand x.supply x.residual m.demand m.inflow hx hm
  intro b
  obtain ⟨r, hr⟩ := hnonempty R.zero b ⟨b, R.zero_add b⟩
  have he : r = b := by
    have hv := hvalid R.zero b r hr
    rw [R.zero_add] at hv
    exact hv
  subst r
  exact ⟨W, hW, hr⟩

end CRK

/-- The three equivalent conditions of published Theorem 14, at its set-theoretic scope. -/
theorem theorem14 {M : Type u} (R : CommResourceMonoid M) :
    (CRK.WinningPolicies R ↔ CRK.AllRoots R) ∧
    (CRK.AllRoots R ↔ CRK.ViableSubfibers R) :=
  ⟨⟨CRK.policies_imply_roots R, CRK.roots_imply_policies R⟩,
    ⟨CRK.roots_imply_subfibers R, CRK.subfibers_imply_roots R⟩⟩
end CausalFoundations
