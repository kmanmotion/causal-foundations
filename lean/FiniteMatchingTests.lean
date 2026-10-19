import CausalFoundations.FiniteMatching

namespace CausalFoundations.FiniteMatchingTests

open Symmetry FiniteMatching

theorem zero_carrier_is_vacuously_perfect : Perfect (empty 0) := by
  constructor <;> intro x <;> exact Fin.elim0 x

theorem empty_origin_has_no_challenge_contrast (n : Nat) (u w : Fin n)
    (r : Option (Fin n)) : assay (empty n) u r = assay (empty n) w r := rfl

theorem empty_origin_survives_any_finite_deletion_list (n : Nat) (xs : List (Fin n)) :
    deletionMinor (empty n) xs = empty n := empty_deletion_minors xs

theorem two_carriers_have_distinct_equivalent_perfect_organizations :
    ∃ M N : Matching 2, Perfect M ∧ Perfect N ∧
      Orbit (stateAction 2) M N ∧ ∃ u, M.partner u ≠ N.partner u :=
  at_least_two_contingent_matchings (by decide)

def firstLink : Matching 2 := extend (empty 2) 0 0 (empty_all_pairs_admissible 0 0)

theorem reused_input_is_forbidden : ¬ Admissible firstLink 0 1 := by
  intro h
  have bad := h.1
  change some (0 : Fin 2) = none at bad
  cases bad

theorem reused_output_is_forbidden : ¬ Admissible firstLink 1 0 := by
  intro h
  exact h.2 0 rfl

theorem new_pair_really_changes_state : firstLink ≠ empty 2 := by
  exact (genesis_step_changes_realized_state
    ⟨0, 0, empty_all_pairs_admissible 0 0, rfl⟩).symm

theorem ablation_recovers_origin_and_only_changes_selected_challenge :
    ablate firstLink 0 = empty 2 ∧
    assay firstLink 0 (some 0) ∧ ¬ assay (ablate firstLink 0) 0 (some 0) ∧
    (ablate firstLink 0).partner 1 = firstLink.partner 1 := by
  exact ⟨extension_ablation_recovers _ _ _ _, rfl,
    (realized_link_ablation_changes_response firstLink (u := 0) (v := 0) rfl).2.1,
    ablate_other_response firstLink (by decide)⟩

theorem many_to_one_map_is_not_a_matching :
    ¬ (∀ u u' v : Fin 2,
      (some (0 : Fin 2)) = some v → some (0 : Fin 2) = some v → u = u') := by
  intro h
  have bad := congrArg Fin.val (h 0 1 0 rfl rfl)
  change 0 = 1 at bad
  cases bad

def cycleThree : Permutation 3 where
  forward x := ⟨(x.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  backward x := ⟨(x.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
  left := by decide
  right := by decide

theorem input_relabeling_uses_inverse_and_null_stays_common :
    (transport (cycleThree, identity 3) (permutationMatching (identity 3))).partner 0 = some 2 ∧
    (transport (identity 3, cycleThree) (permutationMatching (identity 3))).partner 0 = some 1 ∧
    mapResponse cycleThree none = none := ⟨rfl, rfl, rfl⟩

theorem singleton_permutation_matching_has_no_challenge_contrast :
    ∀ u w : Fin 1, (permutationMatching (identity 1)).partner u =
      (permutationMatching (identity 1)).partner w := by
  intro u w
  have he : u = w := Fin.ext (by omega)
  rw [he]

theorem two_carriers_support_nontrivial_channel_orbit :
    ∃ M : Matching 2, Perfect M ∧
      NontrivialOrbit (channelAction (inputAction 2) (responseAction 2)) (assay M) :=
  perfect_channel_has_nontrivial_example (by decide)

#print axioms CausalFoundations.FiniteMatchingTests.zero_carrier_is_vacuously_perfect
#print axioms CausalFoundations.FiniteMatchingTests.empty_origin_has_no_challenge_contrast
#print axioms CausalFoundations.FiniteMatchingTests.empty_origin_survives_any_finite_deletion_list
#print axioms CausalFoundations.FiniteMatchingTests.two_carriers_have_distinct_equivalent_perfect_organizations
#print axioms CausalFoundations.FiniteMatchingTests.reused_input_is_forbidden
#print axioms CausalFoundations.FiniteMatchingTests.reused_output_is_forbidden
#print axioms CausalFoundations.FiniteMatchingTests.new_pair_really_changes_state
#print axioms CausalFoundations.FiniteMatchingTests.ablation_recovers_origin_and_only_changes_selected_challenge
#print axioms CausalFoundations.FiniteMatchingTests.many_to_one_map_is_not_a_matching
#print axioms CausalFoundations.FiniteMatchingTests.input_relabeling_uses_inverse_and_null_stays_common
#print axioms CausalFoundations.FiniteMatchingTests.singleton_permutation_matching_has_no_challenge_contrast
#print axioms CausalFoundations.FiniteMatchingTests.two_carriers_support_nontrivial_channel_orbit

end CausalFoundations.FiniteMatchingTests
