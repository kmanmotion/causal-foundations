import CausalFoundations.OrbitErasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open scoped ENNReal

/-!
# Published Theorem 3: equal-orbit first hitting

Source: Causal Foundations v1.0, section 3.3, page 6.
The path law is an actual probability measure. An attained minimum, its
measurable time and label, and an invariant null exception set are explicit
premises. The label is extended by `none` and the time by top off the attained
hit domain. The time type can be natural or real; visits use the closed finite
window from zero to the declared horizon. No attainment follows from an
infimum or from continuity alone.
-/

namespace CausalFoundations.FirstHitting

open MeasureTheory Set
open CausalFoundations.Symmetry

variable {Γ Ω State Θ Time : Type*} {G : SymmetryGroup Γ}
variable [LinearOrder Time] [Zero Time]

def Visit (X : Time → Ω → State) (B : Θ → Set State) (T : Time)
    (ω : Ω) (t : Time) : Prop :=
  0 ≤ t ∧ t ≤ T ∧ ∃ θ, X t ω ∈ B θ

def Hit (X : Time → Ω → State) (B : Θ → Set State) (T : Time) : Set Ω :=
  {ω | ∃ t, Visit X B T ω t}

def FirstEntry (X : Time → Ω → State) (B : Θ → Set State) (T : Time)
    (ω : Ω) (t : Time) : Prop :=
  Visit X B T ω t ∧ ∀ s, Visit X B T ω s → t ≤ s

theorem first_entry_unique (X : Time → Ω → State) (B : Θ → Set State)
    (T : Time) (ω : Ω) (t s : Time)
    (ht : FirstEntry X B T ω t) (hs : FirstEntry X B T ω s) : t = s :=
  le_antisymm (ht.2 s hs.1) (hs.2 t ht.1)

variable [MeasurableSpace Ω] [MeasurableSpace State] [MeasurableSpace Time]

/-- The declared time space extended by a separate measurable infinity point. -/
def extendedTimeSpace (Time : Type*) [MeasurableSpace Time] : MeasurableSpace (WithTop Time) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0} Time) inferInstance

local instance : MeasurableSpace (WithTop Time) := extendedTimeSpace Time

/-- Finite orientation labels, including the cemetery label, have the discrete space. -/
local instance orientationSpace : MeasurableSpace (Option Θ) := ⊤

/-- Complete source premises, including the actual first-entry witness. -/
structure Model (G : SymmetryGroup Γ) (pa : Action G Ω) (sa : Action G State)
    (oa : Action G Θ) (μ : Measure Ω) where
  horizon : Time
  process : Time → Ω → State
  cells : Θ → Set State
  path_measurable : ∀ g, Measurable (pa.act g)
  state_measurable : ∀ g, Measurable (sa.act g)
  cells_measurable : ∀ θ, MeasurableSet (cells θ)
  cells_disjoint : ∀ θ η x, x ∈ cells θ → x ∈ cells η → θ = η
  cells_transport : ∀ g θ x, sa.act g x ∈ cells (oa.act g θ) ↔ x ∈ cells θ
  process_equivariant : ∀ g t ω, process t (pa.act g ω) = sa.act g (process t ω)
  transitive : ∀ θ η, ∃ g, oa.act g θ = η
  hit_measurable : MeasurableSet (Hit process cells horizon)
  exceptional : Set Ω
  exceptional_null : μ exceptional = 0
  exceptional_invariant : ∀ g ω, pa.act g ω ∈ exceptional ↔ ω ∈ exceptional
  firstTime : Ω → WithTop Time
  orientation : Ω → Option Θ
  time_measurable : Measurable firstTime
  orientation_measurable : Measurable orientation
  attained : ∀ ω, ω ∈ Hit process cells horizon → ω ∉ exceptional →
    ∃ (t : Time) (θ : Θ), firstTime ω = (t : WithTop Time) ∧
      FirstEntry process cells horizon ω t ∧ orientation ω = some θ ∧
      process t ω ∈ cells θ
  off_time : ∀ ω, (ω ∉ Hit process cells horizon ∨ ω ∈ exceptional) → firstTime ω = ⊤
  off_orientation : ∀ ω, (ω ∉ Hit process cells horizon ∨ ω ∈ exceptional) →
    orientation ω = none
  path_law_invariant : ∀ g, μ.map (pa.act g) = μ

variable {pa : Action G Ω} {sa : Action G State} {oa : Action G Θ} {μ : Measure Ω}
variable (D : Model (Time := Time) G pa sa oa μ)

def labelEvent (θ : Θ) : Set Ω :=
  Hit D.process D.cells D.horizon ∩ {ω | D.orientation ω = some θ}

theorem visit_transport (g : Γ) (ω : Ω) (t : Time)
    (h : Visit D.process D.cells D.horizon ω t) :
    Visit D.process D.cells D.horizon (pa.act g ω) t := by
  obtain ⟨h0, hT, θ, hθ⟩ := h
  refine ⟨h0, hT, oa.act g θ, ?_⟩
  rw [D.process_equivariant]
  exact (D.cells_transport g θ _).2 hθ

theorem visit_transport_iff (g : Γ) (ω : Ω) (t : Time) :
    Visit D.process D.cells D.horizon (pa.act g ω) t ↔
      Visit D.process D.cells D.horizon ω t := by
  constructor
  · intro h
    simpa only [inverse_act_act] using visit_transport D (G.inverse g) (pa.act g ω) t h
  · exact visit_transport D g ω t

theorem hit_invariant (g : Γ) (ω : Ω) :
    pa.act g ω ∈ Hit D.process D.cells D.horizon ↔
      ω ∈ Hit D.process D.cells D.horizon := by
  exact exists_congr fun t => visit_transport_iff D g ω t

theorem first_entry_transport (g : Γ) (ω : Ω) (t : Time)
    (h : FirstEntry D.process D.cells D.horizon ω t) :
    FirstEntry D.process D.cells D.horizon (pa.act g ω) t := by
  exact ⟨visit_transport D g ω t h.1,
    fun s hs => h.2 s ((visit_transport_iff D g ω s).1 hs)⟩

theorem attained_time_label_transport (g : Γ) (ω : Ω)
    (hH : ω ∈ Hit D.process D.cells D.horizon) (hN : ω ∉ D.exceptional) :
    D.firstTime (pa.act g ω) = D.firstTime ω ∧
      D.orientation (pa.act g ω) = (D.orientation ω).map (oa.act g) := by
  obtain ⟨t, θ, ht, hfirst, hlabel, hcell⟩ := D.attained ω hH hN
  obtain ⟨s, η, hs, hfirst', hlabel', hcell'⟩ := D.attained (pa.act g ω)
    ((hit_invariant D g ω).2 hH) (fun h => hN ((D.exceptional_invariant g ω).1 h))
  have hst : s = t := first_entry_unique _ _ _ _ _ _ hfirst'
    (first_entry_transport D g ω t hfirst)
  subst s
  have hη : η = oa.act g θ := D.cells_disjoint η (oa.act g θ) _ hcell' (by
    rw [D.process_equivariant]
    exact (D.cells_transport g θ _).2 hcell)
  exact ⟨hs.trans ht.symm, by simp only [hlabel, hlabel', Option.map_some, hη]⟩

theorem time_transport (g : Γ) (ω : Ω) :
    D.firstTime (pa.act g ω) = D.firstTime ω := by
  by_cases hH : ω ∈ Hit D.process D.cells D.horizon
  · by_cases hN : ω ∈ D.exceptional
    · rw [D.off_time ω (Or.inr hN),
        D.off_time (pa.act g ω) (Or.inr ((D.exceptional_invariant g ω).2 hN))]
    · exact (attained_time_label_transport D g ω hH hN).1
  · rw [D.off_time ω (Or.inl hH), D.off_time (pa.act g ω)
      (Or.inl (fun h => hH ((hit_invariant D g ω).1 h)))]

theorem orientation_transport (g : Γ) (ω : Ω) :
    D.orientation (pa.act g ω) = (D.orientation ω).map (oa.act g) := by
  by_cases hH : ω ∈ Hit D.process D.cells D.horizon
  · by_cases hN : ω ∈ D.exceptional
    · rw [D.off_orientation ω (Or.inr hN), D.off_orientation (pa.act g ω)
        (Or.inr ((D.exceptional_invariant g ω).2 hN))]
      rfl
    · exact (attained_time_label_transport D g ω hH hN).2
  · rw [D.off_orientation ω (Or.inl hH), D.off_orientation (pa.act g ω)
      (Or.inl (fun h => hH ((hit_invariant D g ω).1 h)))]
    rfl

theorem label_event_measurable (θ : Θ) : MeasurableSet (labelEvent D θ) :=
  D.hit_measurable.inter (D.orientation_measurable (measurableSet_singleton (some θ)))

theorem orientation_action_injective (oa : Action G Θ) (g : Γ) : Function.Injective (oa.act g) := by
  intro θ η h
  simpa only [inverse_act_act] using congrArg (oa.act (G.inverse g)) h

theorem label_event_preimage (g : Γ) (θ : Θ) :
    pa.act g ⁻¹' labelEvent D (oa.act g θ) = labelEvent D θ := by
  ext ω
  simp only [mem_preimage, labelEvent, mem_inter_iff, mem_setOf_eq,
    hit_invariant D, orientation_transport D]
  constructor
  · rintro ⟨hH, hL⟩
    refine ⟨hH, ?_⟩
    cases hω : D.orientation ω with
    | none => simp [hω] at hL
    | some η =>
      have he : oa.act g η = oa.act g θ := by simpa [hω] using hL
      rw [orientation_action_injective oa g he]
  · rintro ⟨hH, hL⟩
    exact ⟨hH, by simp only [hL, Option.map_some]⟩

theorem related_label_probabilities (g : Γ) (θ : Θ) :
    μ (labelEvent D (oa.act g θ)) = μ (labelEvent D θ) := by
  calc
    μ (labelEvent D (oa.act g θ)) =
        μ.map (pa.act g) (labelEvent D (oa.act g θ)) := by rw [D.path_law_invariant]
    _ = μ (pa.act g ⁻¹' labelEvent D (oa.act g θ)) :=
      Measure.map_apply (D.path_measurable g) (label_event_measurable D _)
    _ = μ (labelEvent D θ) := by rw [label_event_preimage D]

theorem equal_label_probabilities (θ η : Θ) : μ (labelEvent D θ) = μ (labelEvent D η) := by
  obtain ⟨g, hg⟩ := D.transitive θ η
  exact (hg ▸ related_label_probabilities D g θ).symm

theorem label_events_disjoint : Pairwise (fun θ η => Disjoint (labelEvent D θ) (labelEvent D η)) := by
  intro θ η hne
  apply Set.disjoint_left.2
  intro ω hθ hη
  exact hne (Option.some.inj (hθ.2.symm.trans hη.2))

theorem label_union : (⋃ θ, labelEvent D θ) = Hit D.process D.cells D.horizon \ D.exceptional := by
  ext ω
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := mem_iUnion.1 h
    refine ⟨hθ.1, ?_⟩
    intro hN
    have he := D.off_orientation ω (Or.inr hN)
    rw [hθ.2] at he
    exact Option.noConfusion he
  · rintro ⟨hH, hN⟩
    obtain ⟨t, θ, _, _, hθ, _⟩ := D.attained ω hH hN
    exact mem_iUnion.2 ⟨θ, hH, hθ⟩

theorem sum_label_probabilities [Fintype Θ] :
    (∑ θ, μ (labelEvent D θ)) = μ (Hit D.process D.cells D.horizon) := by
  rw [← tsum_fintype (L := .unconditional Θ), ← measure_iUnion (label_events_disjoint D) (label_event_measurable D),
    label_union D, measure_diff_null D.exceptional_null]

theorem card_positive [Fintype Θ] [Nonempty Θ] : (0 : ℝ≥0∞) < Fintype.card Θ := by
  exact_mod_cast Fintype.card_pos

theorem equal_orbit_first_hit [Fintype Θ] [Nonempty Θ] (θ : Θ) :
    μ (labelEvent D θ) = μ (Hit D.process D.cells D.horizon) / Fintype.card Θ := by
  have hsum := sum_label_probabilities D
  have hc : (Fintype.card Θ : ℝ≥0∞) ≠ 0 := ne_of_gt (card_positive (Θ := Θ))
  have hct : (Fintype.card Θ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc
    μ (labelEvent D θ) =
        (Fintype.card Θ : ℝ≥0∞) * μ (labelEvent D θ) / Fintype.card Θ :=
      by rw [mul_comm (Fintype.card Θ : ℝ≥0∞)]; exact (ENNReal.mul_div_cancel_right hc hct).symm
    _ = (∑ η, μ (labelEvent D η)) / Fintype.card Θ := by
      congr 1
      simp only [equal_label_probabilities D _ θ, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    _ = μ (Hit D.process D.cells D.horizon) / Fintype.card Θ := by rw [hsum]

/-- Event-probability ratio; its conditional interpretation requires positive hit probability. -/
noncomputable def conditionalOrientation (θ : Θ) : ℝ≥0∞ :=
  μ (labelEvent D θ) / μ (Hit D.process D.cells D.horizon)

theorem conditional_uniform [Fintype Θ] [Nonempty Θ] [IsProbabilityMeasure μ]
    (hH : 0 < μ (Hit D.process D.cells D.horizon)) (θ : Θ) :
    conditionalOrientation D θ = 1 / (Fintype.card Θ : ℝ≥0∞) := by
  unfold conditionalOrientation
  rw [equal_orbit_first_hit D θ, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm
    ((Fintype.card Θ : ℝ≥0∞)⁻¹), ← mul_assoc,
    ENNReal.mul_inv_cancel (ne_of_gt hH) (measure_ne_top μ _), one_mul, one_div]

theorem null_hit_zero [Fintype Θ] [Nonempty Θ]
    (hH : μ (Hit D.process D.cells D.horizon) = 0) (θ : Θ) :
    μ (labelEvent D θ) = 0 := by
  rw [equal_orbit_first_hit D θ, hH, ENNReal.zero_div]

end CausalFoundations.FirstHitting

namespace CausalFoundations

open FirstHitting MeasureTheory Symmetry

/-- Published Theorem 3, with actual attained entry and invariant path measure. -/
theorem theorem3 {Γ Ω State Θ Time : Type*} (G : SymmetryGroup Γ)
    [Fintype Γ] [Fintype Θ] [Nonempty Θ] [LinearOrder Time] [Zero Time]
    [MeasurableSpace Ω] [MeasurableSpace State] [MeasurableSpace Time]
    (pa : Action G Ω) (sa : Action G State) (oa : Action G Θ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Model (Time := Time) G pa sa oa μ) :
    (∀ θ, μ (labelEvent D θ) = μ (Hit D.process D.cells D.horizon) / Fintype.card Θ) ∧
    (0 < μ (Hit D.process D.cells D.horizon) →
      ∀ θ, conditionalOrientation D θ = 1 / (Fintype.card Θ : ℝ≥0∞)) :=
  ⟨equal_orbit_first_hit D, fun h => conditional_uniform D h⟩

end CausalFoundations
