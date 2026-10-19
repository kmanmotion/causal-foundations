import CausalFoundations.FixedSet

/-!
# Finite structural foundations for published Theorem 4

Source: Causal Foundations v1.0, section 3.4, pages 6--7.
The two carriers are independently relabeled copies of `Fin n`. A state is an
actual partial matching, represented by its unique optional partner at each input.
This file proves structural and intervention facts only. It does not construct
a CTMC, a jump distribution, exponential clocks or a first-passage expectation.
-/

namespace CausalFoundations.FiniteMatching

open Symmetry

structure Permutation (n : Nat) where
  forward : Fin n → Fin n
  backward : Fin n → Fin n
  left : ∀ x, backward (forward x) = x
  right : ∀ x, forward (backward x) = x

theorem permutation_ext {n : Nat} {p q : Permutation n}
    (h : ∀ x, p.forward x = q.forward x) : p = q := by
  have hb : p.backward = q.backward := by
    funext x
    calc
      p.backward x = p.backward (q.forward (q.backward x)) := by rw [q.right]
      _ = p.backward (p.forward (q.backward x)) := by rw [h]
      _ = q.backward x := p.left _
  have hf : p.forward = q.forward := funext h
  cases p
  cases q
  cases hf
  cases hb
  rfl

def identity (n : Nat) : Permutation n := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def compose {n : Nat} (p q : Permutation n) : Permutation n where
  forward x := p.forward (q.forward x)
  backward x := q.backward (p.backward x)
  left x := by rw [p.left, q.left]
  right x := by rw [q.right, p.right]

def inverse {n : Nat} (p : Permutation n) : Permutation n :=
  ⟨p.backward, p.forward, p.right, p.left⟩

def relabelGroup (n : Nat) : SymmetryGroup (Permutation n × Permutation n) where
  identity := (identity n, identity n)
  product g h := (compose g.1 h.1, compose g.2 h.2)
  inverse g := (inverse g.1, inverse g.2)
  assoc := by intro g h k; apply Prod.ext <;> apply permutation_ext <;> intro x <;> rfl
  identity_left := by intro g; apply Prod.ext <;> apply permutation_ext <;> intro x <;> rfl
  identity_right := by intro g; apply Prod.ext <;> apply permutation_ext <;> intro x <;> rfl
  inverse_left := by
    intro g
    apply Prod.ext
    · apply permutation_ext; exact g.1.left
    · apply permutation_ext; exact g.2.left
  inverse_right := by
    intro g
    apply Prod.ext
    · apply permutation_ext; exact g.1.right
    · apply permutation_ext; exact g.2.right

def mapResponse {n : Nat} (p : Permutation n) : Option (Fin n) → Option (Fin n)
  | none => none
  | some v => some (p.forward v)

theorem map_response_inverse {n : Nat} (p : Permutation n) (r : Option (Fin n)) :
    mapResponse (inverse p) (mapResponse p r) = r := by
  cases r with
  | none => rfl
  | some v => exact congrArg some (p.left v)

theorem map_response_injective {n : Nat} (p : Permutation n)
    {r s : Option (Fin n)} (h : mapResponse p r = mapResponse p s) : r = s := by
  have hi := congrArg (mapResponse (inverse p)) h
  rw [map_response_inverse, map_response_inverse] at hi
  exact hi

structure Matching (n : Nat) where
  partner : Fin n → Option (Fin n)
  column_unique : ∀ u u' v, partner u = some v → partner u' = some v → u = u'

theorem matching_ext {n : Nat} {M N : Matching n}
    (h : ∀ u, M.partner u = N.partner u) : M = N := by
  have hf := funext h
  cases M
  cases N
  cases hf
  rfl

def Link {n : Nat} (M : Matching n) (u v : Fin n) : Prop := M.partner u = some v
def RowFree {n : Nat} (M : Matching n) (u : Fin n) : Prop := M.partner u = none
def ColumnFree {n : Nat} (M : Matching n) (v : Fin n) : Prop :=
  ∀ u, ¬ Link M u v
def Admissible {n : Nat} (M : Matching n) (u v : Fin n) : Prop :=
  RowFree M u ∧ ColumnFree M v
def Perfect {n : Nat} (M : Matching n) : Prop :=
  (∀ u, ∃ v, Link M u v) ∧ (∀ v, ∃ u, Link M u v)

def empty (n : Nat) : Matching n where
  partner _ := none
  column_unique := by intro u u' v h; cases h

theorem empty_no_links {n : Nat} (u v : Fin n) : ¬ Link (empty n) u v := by
  intro h; cases h

theorem empty_all_pairs_admissible {n : Nat} (u v : Fin n) :
    Admissible (empty n) u v := ⟨rfl, fun w => empty_no_links w v⟩

def transport {n : Nat} (g : Permutation n × Permutation n) (M : Matching n) : Matching n where
  partner u := mapResponse g.2 (M.partner (g.1.backward u))
  column_unique := by
    intro u u' v hu hu'
    have h := map_response_injective g.2 (hu.trans hu'.symm)
    cases hv : M.partner (g.1.backward u) with
    | none => simp [hv, mapResponse] at hu
    | some w =>
      have hi := M.column_unique _ _ w hv (h.symm.trans hv)
      have he := congrArg g.1.forward hi
      rw [g.1.right, g.1.right] at he
      exact he

def stateAction (n : Nat) : Action (relabelGroup n) (Matching n) where
  act := transport
  identity_act := by
    intro M
    apply matching_ext
    intro u
    change mapResponse (identity n) (M.partner u) = M.partner u
    cases M.partner u <;> rfl
  product_act := by
    intro g h M
    apply matching_ext
    intro u
    change mapResponse (compose g.2 h.2) (M.partner (h.1.backward (g.1.backward u))) =
      mapResponse g.2 (mapResponse h.2 (M.partner (h.1.backward (g.1.backward u))))
    cases M.partner (h.1.backward (g.1.backward u)) <;> rfl

def inputAction (n : Nat) : Action (relabelGroup n) (Fin n) where
  act g := g.1.forward
  identity_act := fun _ => rfl
  product_act := fun _ _ _ => rfl

def responseAction (n : Nat) : Action (relabelGroup n) (Option (Fin n)) where
  act g := mapResponse g.2
  identity_act := by intro r; cases r <;> rfl
  product_act := by intro g h r; cases r <;> rfl

theorem transport_link_iff {n : Nat} (g : Permutation n × Permutation n)
    (M : Matching n) (u v : Fin n) :
    Link (transport g M) (g.1.forward u) (g.2.forward v) ↔ Link M u v := by
  change mapResponse g.2 (M.partner (g.1.backward (g.1.forward u))) =
    mapResponse g.2 (some v) ↔ M.partner u = some v
  rw [g.1.left]
  exact ⟨map_response_injective g.2, congrArg (mapResponse g.2)⟩

theorem empty_fixed {n : Nat} : Fixed (stateAction n) (empty n) := by
  intro g
  apply matching_ext
  intro u
  rfl

theorem common_null_fixed {n : Nat} (g : Permutation n × Permutation n) :
    (responseAction n).act g none = none := rfl

/-- The frozen deterministic response is an event channel with one true output. -/
def assay {n : Nat} (M : Matching n) : Channel (Fin n) (Option (Fin n)) Prop :=
  fun u r => M.partner u = r

theorem assay_unique_response {n : Nat} (M : Matching n) (u : Fin n) :
    ∃ r, assay M u r ∧ ∀ s, assay M u s → s = r :=
  ⟨M.partner u, rfl, fun _ hs => hs.symm⟩

theorem assay_equivariant {n : Nat} :
    Equivariant (stateAction n) (channelAction (inputAction n) (responseAction n)) assay := by
  intro g M
  funext u r
  apply propext
  change mapResponse g.2 (M.partner (g.1.backward u)) = r ↔
    M.partner (g.1.backward u) = mapResponse (inverse g.2) r
  constructor
  · intro h
    have hi := congrArg (mapResponse (inverse g.2)) h
    rw [map_response_inverse] at hi
    exact hi
  · intro h
    rw [h]
    exact map_response_inverse (inverse g.2) r

theorem empty_assay_common_null {n : Nat} (u : Fin n) (r : Option (Fin n)) :
    assay (empty n) u r ↔ r = none := ⟨Eq.symm, Eq.symm⟩

def ablate {n : Nat} (M : Matching n) (u : Fin n) : Matching n where
  partner x := if x = u then none else M.partner x
  column_unique := by
    intro x y v hx hy
    by_cases hxu : x = u
    · simp [hxu] at hx
    · by_cases hyu : y = u
      · simp [hyu] at hy
      · exact M.column_unique x y v (by simpa [hxu] using hx) (by simpa [hyu] using hy)

theorem ablate_response {n : Nat} (M : Matching n) (u : Fin n) :
    (ablate M u).partner u = none := by simp [ablate]

theorem ablate_other_response {n : Nat} (M : Matching n) {u x : Fin n} (h : x ≠ u) :
    (ablate M u).partner x = M.partner x := by simp [ablate, h]

theorem ablate_exact_link {n : Nat} (M : Matching n) (u v : Fin n) (hl : Link M u v)
    (x y : Fin n) : Link (ablate M u) x y ↔ Link M x y ∧ (x, y) ≠ (u, v) := by
  by_cases hx : x = u
  · subst x
    constructor
    · intro h; change (if u = u then none else M.partner u) = some y at h; simp at h
    · intro ⟨h, hn⟩
      have hy : y = v := Option.some.inj (h.symm.trans hl)
      exact False.elim (hn (by rw [hy]))
  · constructor
    · intro h
      exact ⟨(ablate_other_response M hx).symm.trans h,
        fun he => hx (congrArg Prod.fst he)⟩
    · intro ⟨h, _⟩
      exact (ablate_other_response M hx).trans h

theorem realized_link_ablation_changes_response {n : Nat} (M : Matching n)
    {u v : Fin n} (h : Link M u v) :
    assay M u (some v) ∧ ¬ assay (ablate M u) u (some v) ∧
      assay (ablate M u) u none := by
  refine ⟨h, ?_, ablate_response M u⟩
  intro hn
  have bad := (ablate_response M u).symm.trans hn
  cases bad

theorem ablate_transport {n : Nat} (g : Permutation n × Permutation n)
    (M : Matching n) (u : Fin n) :
    transport g (ablate M u) = ablate (transport g M) (g.1.forward u) := by
  apply matching_ext
  intro x
  by_cases hx : g.1.backward x = u
  · have he : x = g.1.forward u := by
      rw [← hx, g.1.right]
    simp [transport, ablate, he, g.1.left, mapResponse]
  · have he : x ≠ g.1.forward u := by
      intro he; apply hx; rw [he, g.1.left]
    simp [transport, ablate, hx, he]

def extend {n : Nat} (M : Matching n) (u v : Fin n) (ha : Admissible M u v) : Matching n where
  partner x := if x = u then some v else M.partner x
  column_unique := by
    intro x y w hx hy
    by_cases hxu : x = u
    · subst x
      have hw : v = w := Option.some.inj (by simpa using hx)
      by_cases hyu : y = u
      · exact hyu.symm
      · have hh : M.partner y = some v := by simpa [hyu, ← hw] using hy
        exact False.elim (ha.2 y hh)
    · by_cases hyu : y = u
      · subst y
        have hw : v = w := Option.some.inj (by simpa using hy)
        have hh : M.partner x = some v := by simpa [hxu, ← hw] using hx
        exact False.elim (ha.2 x hh)
      · exact M.column_unique x y w (by simpa [hxu] using hx) (by simpa [hyu] using hy)

theorem extension_exact_link {n : Nat} (M : Matching n) (u v : Fin n)
    (ha : Admissible M u v) (x y : Fin n) :
    Link (extend M u v ha) x y ↔ Link M x y ∨ (x = u ∧ y = v) := by
  by_cases hx : x = u
  · subst x
    have hfree := ha.1
    change M.partner u = none at hfree
    simp [Link, extend, hfree, eq_comm]
  · simp [Link, extend, hx]

theorem extension_ablation_recovers {n : Nat} (M : Matching n) (u v : Fin n)
    (ha : Admissible M u v) : ablate (extend M u v ha) u = M := by
  apply matching_ext
  intro x
  by_cases hx : x = u
  · subst x; exact (ablate_response _ u).trans ha.1.symm
  · simp [ablate, extend, hx]

theorem transport_admissible {n : Nat} (g : Permutation n × Permutation n)
    (M : Matching n) {u v : Fin n} (ha : Admissible M u v) :
    Admissible (transport g M) (g.1.forward u) (g.2.forward v) := by
  constructor
  · change mapResponse g.2 (M.partner (g.1.backward (g.1.forward u))) = none
    rw [g.1.left, ha.1]
    rfl
  · intro x hx
    have he : g.1.forward (g.1.backward x) = x := g.1.right x
    have hl := (transport_link_iff g M (g.1.backward x) v).mp (by rw [he]; exact hx)
    exact ha.2 _ hl

theorem extend_transport {n : Nat} (g : Permutation n × Permutation n)
    (M : Matching n) (u v : Fin n) (ha : Admissible M u v) :
    transport g (extend M u v ha) =
      extend (transport g M) (g.1.forward u) (g.2.forward v) (transport_admissible g M ha) := by
  apply matching_ext
  intro x
  by_cases hx : g.1.backward x = u
  · have he : x = g.1.forward u := by rw [← hx, g.1.right]
    simp [transport, extend, he, g.1.left, mapResponse]
  · have he : x ≠ g.1.forward u := by intro he; apply hx; rw [he, g.1.left]
    simp [transport, extend, hx, he]

def permutationMatching {n : Nat} (p : Permutation n) : Matching n where
  partner u := some (p.forward u)
  column_unique := by
    intro x y v hx hy
    have he := congrArg p.backward (Option.some.inj (hx.trans hy.symm))
    rw [p.left, p.left] at he
    exact he

theorem permutation_matching_perfect {n : Nat} (p : Permutation n) :
    Perfect (permutationMatching p) :=
  ⟨fun u => ⟨p.forward u, rfl⟩, fun v => ⟨p.backward v, congrArg some (p.right v)⟩⟩

noncomputable def perfectPermutation {n : Nat} (M : Matching n) (hp : Perfect M) :
    Permutation n where
  forward u := Classical.choose (hp.1 u)
  backward v := Classical.choose (hp.2 v)
  left u := M.column_unique _ _ _
    (Classical.choose_spec (hp.2 (Classical.choose (hp.1 u))))
    (Classical.choose_spec (hp.1 u))
  right v := Option.some.inj
    ((Classical.choose_spec (hp.1 (Classical.choose (hp.2 v)))).symm.trans
      (Classical.choose_spec (hp.2 v)))

theorem perfect_iff_permutation {n : Nat} (M : Matching n) :
    Perfect M ↔ ∃ p : Permutation n, M = permutationMatching p := by
  constructor
  · intro hp
    refine ⟨perfectPermutation M hp, ?_⟩
    apply matching_ext
    exact fun u => Classical.choose_spec (hp.1 u)
  · intro ⟨p, he⟩
    rw [he]
    exact permutation_matching_perfect p

theorem perfect_matchings_same_orbit {n : Nat} (M N : Matching n)
    (hm : Perfect M) (hn : Perfect N) : Orbit (stateAction n) M N := by
  obtain ⟨p, rfl⟩ := (perfect_iff_permutation M).mp hm
  obtain ⟨q, rfl⟩ := (perfect_iff_permutation N).mp hn
  refine ⟨(identity n, compose q (inverse p)), ?_⟩
  apply matching_ext
  intro u
  change some (q.forward (p.backward (p.forward u))) = some (q.forward u)
  rw [p.left]

def GenesisStep {n : Nat} (M N : Matching n) : Prop :=
  ∃ u v, ∃ ha : Admissible M u v, N = extend M u v ha

theorem genesis_step_transport {n : Nat} (g : Permutation n × Permutation n)
    {M N : Matching n} (h : GenesisStep M N) :
    GenesisStep (transport g M) (transport g N) := by
  obtain ⟨u, v, ha, rfl⟩ := h
  exact ⟨g.1.forward u, g.2.forward v, transport_admissible g M ha,
    extend_transport g M u v ha⟩

theorem ablate_empty {n : Nat} (u : Fin n) : ablate (empty n) u = empty n := by
  apply matching_ext
  intro x
  by_cases h : x = u <;> simp [ablate, empty, h]

def deletionMinor {n : Nat} : Matching n → List (Fin n) → Matching n
  | M, [] => M
  | M, u :: rest => deletionMinor (ablate M u) rest

theorem empty_deletion_minors {n : Nat} (deletions : List (Fin n)) :
    deletionMinor (empty n) deletions = empty n := by
  induction deletions with
  | nil => rfl
  | cons u rest ih =>
    change deletionMinor (ablate (empty n) u) rest = empty n
    rw [ablate_empty]
    exact ih

theorem genesis_step_changes_realized_state {n : Nat} {M N : Matching n}
    (h : GenesisStep M N) : M ≠ N := by
  obtain ⟨u, v, ha, rfl⟩ := h
  intro he
  have hp := congrArg (fun P : Matching n => P.partner u) he
  change M.partner u = (extend M u v ha).partner u at hp
  rw [ha.1] at hp
  simp [extend] at hp

theorem genesis_step_preserves_links {n : Nat} {M N : Matching n}
    (h : GenesisStep M N) {u v : Fin n} (hl : Link M u v) : Link N u v := by
  obtain ⟨x, y, ha, rfl⟩ := h
  exact (extension_exact_link M x y ha u v).mpr (Or.inl hl)

theorem assay_faithful {n : Nat} {M N : Matching n} (h : assay M = assay N) : M = N := by
  apply matching_ext
  intro u
  have hp := congrArg (fun Q : Channel (Fin n) (Option (Fin n)) Prop => Q u (M.partner u)) h
  exact (Eq.mp hp rfl).symm

theorem perfect_has_no_admissible_pair {n : Nat} (M : Matching n) (hp : Perfect M)
    (u v : Fin n) : ¬ Admissible M u v := by
  intro ha
  obtain ⟨w, hw⟩ := hp.1 u
  have bad := ha.1.symm.trans hw
  cases bad

theorem perfect_each_challenge_ablatable {n : Nat} (M : Matching n) (hp : Perfect M)
    (u : Fin n) : ∃ v, assay M u (some v) ∧ ¬ assay (ablate M u) u (some v) := by
  obtain ⟨v, hv⟩ := hp.1 u
  exact ⟨v, hv, (realized_link_ablation_changes_response M hv).2.1⟩

def swap {n : Nat} (a b : Fin n) (x : Fin n) : Fin n :=
  if x = a then b else if x = b then a else x

theorem swap_involution {n : Nat} (a b x : Fin n) : swap a b (swap a b x) = x := by
  by_cases ha : x = a
  · subst x; by_cases hb : b = a <;> simp [swap, hb]
  · by_cases hb : x = b
    · subst x; simp [swap, ha]
    · simp [swap, ha, hb]

def transposition {n : Nat} (a b : Fin n) : Permutation n :=
  ⟨swap a b, swap a b, swap_involution a b, swap_involution a b⟩

theorem distinct_perfect_relabelings {n : Nat} (a b : Fin n) (hab : a ≠ b) :
    ∃ M N : Matching n, Perfect M ∧ Perfect N ∧
      Orbit (stateAction n) M N ∧ M.partner a ≠ N.partner a := by
  let M := permutationMatching (identity n)
  let g := (identity n, transposition a b)
  let N := transport g M
  have hN : N = permutationMatching (transposition a b) := by
    apply matching_ext; intro u; rfl
  refine ⟨M, N, permutation_matching_perfect _, ?_, ⟨g, rfl⟩, ?_⟩
  · rw [hN]; exact permutation_matching_perfect _
  · intro he
    change some a = some (swap a b a) at he
    have hx := Option.some.inj he
    simp [swap] at hx
    exact hab hx

theorem at_least_two_contingent_matchings {n : Nat} (hn : 2 ≤ n) :
    ∃ M N : Matching n, Perfect M ∧ Perfect N ∧
      Orbit (stateAction n) M N ∧ ∃ u, M.partner u ≠ N.partner u := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have hv := congrArg Fin.val h; change 0 = 1 at hv; cases hv
  obtain ⟨M, N, hm, hn', ho, hd⟩ := distinct_perfect_relabelings a b hab
  exact ⟨M, N, hm, hn', ho, a, hd⟩

theorem perfect_channel_has_nontrivial_example {n : Nat} (hn : 2 ≤ n) :
    ∃ M : Matching n, Perfect M ∧
      NontrivialOrbit (channelAction (inputAction n) (responseAction n)) (assay M) := by
  obtain ⟨M, N, hm, _, ⟨g, hg⟩, u, hd⟩ := at_least_two_contingent_matchings hn
  refine ⟨M, hm, g, ?_⟩
  intro he
  have ht := assay_equivariant g M
  rw [hg, he] at ht
  have hs := assay_faithful ht
  exact hd (congrArg (fun P : Matching n => P.partner u) hs.symm)

/-- Structural endpoint only; the stochastic endpoint of Theorem 4 is pending. -/
theorem finite_matching_foundations {n : Nat} (hn : 2 ≤ n) :
    Fixed (stateAction n) (empty n) ∧
    Equivariant (stateAction n) (channelAction (inputAction n) (responseAction n)) assay ∧
    (∀ M : Matching n, Perfect M → ∀ u,
      ∃ v, assay M u (some v) ∧ ¬ assay (ablate M u) u (some v)) ∧
    (∀ M N : Matching n, Perfect M → Perfect N → Orbit (stateAction n) M N) ∧
    (∃ M : Matching n, Perfect M ∧
      NontrivialOrbit (channelAction (inputAction n) (responseAction n)) (assay M)) :=
  ⟨empty_fixed, assay_equivariant, perfect_each_challenge_ablatable,
    perfect_matchings_same_orbit, perfect_channel_has_nontrivial_example hn⟩

end CausalFoundations.FiniteMatching
