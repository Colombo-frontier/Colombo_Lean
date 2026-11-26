import Smoothness2601.PrefixSimulator
import Smoothness2601.DeferredPrefix

/-! Actual regular conditional frame laws after observing a whole prefix.
This permits applying concentration to each adaptive query directly, without
conditioning on any preceding good-event restriction. -/
noncomputable section
namespace Smoothness2601.PrefixPosterior
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior ProjectionStabilizer OrthogonalAction
open PrefixSimulator DeferredPrefix
open scoped RealInnerProductSpace ENNReal
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

def knownSpan {d T : ℕ} (y : Frame d T) : Submodule ℝ (Space d) :=
  Submodule.span ℝ (Set.range y)

theorem knownSpan_dimension {d T : ℕ} (y : Frame d T) : Module.finrank ℝ (knownSpan y) ≤ T := by
  classical
  have h := finrank_span_le_card (R := ℝ) (Set.range y)
  rw [Set.toFinset_card] at h
  exact h.trans (by simpa using Fintype.card_range_le y)

theorem prefix_posterior_invariant (d T k : ℕ)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T ⊥ μ) :
    ∀ᵐ y ∂μ.map (fun U => truncate U k),
      Invariant d T (knownSpan y) (condDistrib id (fun U => truncate U k) μ y) := by
  have he : ∀ (A : subgroup d ⊥) (U : Frame d T), truncate (A • U) k = A • truncate U k := by
    intro A U
    funext i
    by_cases hi : i.val < k
    · simp [truncate,hi]
    · simp only [truncate,if_neg hi,Pi.smul_apply]
      exact (isometry d A.val).map_zero.symm
  have hp := ConditionalSupport.equivariant_observation μ (fun U => truncate U k)
    (truncate_measurable d T k) (ProjectionStabilizer.law d ⊥) hμ he
  filter_upwards [hp] with y hy
  intro A
  let B : subgroup d ⊥ := ⟨A.val,(membership d ⊥ A.val).2 (by
    intro z hz
    have hz' : z = 0 := hz
    rw [hz']
    exact (isometry d A.val).map_zero)⟩
  have hfix : B • y = y := by
    funext i
    exact (membership d (knownSpan y) A.val).1 A.property (y i)
      (Submodule.subset_span ⟨i,rfl⟩)
  exact hy B hfix

theorem prefix_fiber (d T k : ℕ) (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] :
    ∀ᵐ y ∂μ.map (fun U => truncate U k),
      ∀ᵐ U ∂condDistrib id (fun U => truncate U k) μ y, truncate U k = y := by
  apply ConditionalSupport.fiber μ _ (truncate_measurable d T k)
  exact measurableSet_eq_fun ((truncate_measurable d T k).comp measurable_snd) measurable_fst

theorem prefix_posterior_unseen (d T k : ℕ)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) :
    ∀ᵐ y ∂μ.map (fun U => truncate U k),
      ∀ᵐ U ∂condDistrib id (fun U => truncate U k) μ y, UnseenOrthogonal d T k (knownSpan y) U := by
  filter_upwards [prefix_fiber d T k μ,ProjectionConcentration.conditioned_orthonormal d T μ hU
    (fun U => truncate U k) (truncate_measurable d T k)] with y hy hyU
  filter_upwards [hy,hyU] with U hUy hUU
  intro i hi
  apply (Submodule.mem_orthogonal _ _).mpr
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j,rfl⟩ := hv
    rw [← hUy]
    by_cases hj : j.val < k
    · simp only [truncate,if_pos hj]
      exact hUU.inner_eq_zero (by intro hji; have := congrArg Fin.val hji; omega)
    · simp [truncate,hj]
  | zero => simp
  | add x z _ _ hx hz => simp only [inner_add_left,hx,hz,add_zero]
  | smul c x _ hx => simp only [real_inner_smul_left,hx,mul_zero]

theorem prefix_query_tail (d T k n : ℕ) (hd : T+(n+1) ≤ d)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T ⊥ μ)
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U)
    (q : Frame d T → Space d) (hq : Measurable q) (hqR : ∀ y, ‖q y‖ ≤ R) :
    μ {U | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪q (truncate U k),U i⟫|} ≤
      failurePerInspection T n δ R := by
  let o := fun U : Frame d T => truncate U k
  letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map (truncate_measurable d T k).aemeasurable
  have hs : MeasurableSet {p : Frame d T × Frame d T |
      ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪q p.1,p.2 i⟫|} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : k ≤ i.val
    · simp only [hi,true_and]
      have hm : Measurable (fun p : Frame d T × Frame d T => ⟪q p.1,p.2 i⟫) :=
        (continuous_fst.inner continuous_snd).measurable.comp
          ((hq.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
      exact measurableSet_le measurable_const hm.abs
    · simp only [hi,false_and,Set.setOf_false]
      exact MeasurableSet.empty
  have he := ConditionalSupport.event_disintegration μ o (truncate_measurable d T k) _ hs
  change μ {U | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪q (truncate U k),U i⟫|} = _ at he
  rw [he]
  calc
    _ ≤ ∫⁻ _y, failurePerInspection T n δ R ∂μ.map o := by
      apply lintegral_mono_ae
      filter_upwards [prefix_posterior_invariant d T k μ hμ,
        ProjectionConcentration.conditioned_orthonormal d T μ hU o (truncate_measurable d T k),
        prefix_posterior_unseen d T k μ hU] with y hy hyU hyO
      have hn : n+1 ≤ Module.finrank ℝ (knownSpan y)ᗮ := by
        have he := (knownSpan y).finrank_add_finrank_orthogonal
        have hknown := knownSpan_dimension y
        have hdE : Module.finrank ℝ (Space d) = d := by simp [Space]
        omega
      exact bounded_query_tail d T k n (knownSpan y) hn hδ hR hδR
        (condDistrib id o μ y) hy hyU hyO (q y) (hqR y)
    _ = _ := by simp

end Smoothness2601.PrefixPosterior
