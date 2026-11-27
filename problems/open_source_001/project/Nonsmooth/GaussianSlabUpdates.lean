import Nonsmooth.GaussianSlabKernel
import Nonsmooth.ObservationEventStability
import Nonsmooth.GaussianHalfspaceCovariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianSlabKernel_scalar_covariance {u : E} (hu : ‖u‖ = 1) (a b : ℝ) :
    ∀ᵐ y ∂(gaussianSlabKernel u (a, b)).map (fun z : E => ⟪z, u⟫_ℝ),
      ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ)
        (condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (gaussianSlabKernel u (a, b)) y) ≤
          ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  by_cases hp : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} = 0
  · simp only [gaussianSlabKernel_apply_zero u a b hp]
    exact gaussianAmbientRow_scalar_covariance hu
  · simp only [gaussianSlabKernel_apply u a b hp]
    exact condDistrib_property_condition_observation (gaussianAmbientRowLaw E)
      (fun z : E => ⟪z, u⟫_ℝ) (continuous_id.inner continuous_const).measurable
      (Icc a b) measurableSet_Icc
      (fun ν : Measure E => ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) ν ≤
        ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ)) (gaussianAmbientRow_scalar_covariance hu)

theorem gaussianSlabKernel_upper_condition_covariance {u : E} (hu : ‖u‖ = 1)
    (a b t : ℝ) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ)
      ((gaussianSlabKernel u (a, b))[|{z : E | ⟪z, u⟫_ℝ ≤ t}]) ≤
        ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hA : MeasurableSet {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} :=
    (measurableSet_le measurable_const hr).inter (measurableSet_le hr measurable_const)
  have hC : MeasurableSet {z : E | ⟪z, u⟫_ℝ ≤ t} := measurableSet_le hr measurable_const
  by_cases hp : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} = 0
  · rw [gaussianSlabKernel_apply_zero u a b hp]
    by_cases ht : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ t} = 0
    · rw [cond_eq_zero_of_meas_eq_zero ht]
      simp only [variance, evariance, lintegral_zero_measure, ENNReal.toReal_zero]
      positivity
    · have hk : gaussianHalfspaceKernel u t = (gaussianAmbientRowLaw E)[|{z : E | ⟪z, u⟫_ℝ ≤ t}] := by
        rw [gaussianHalfspaceKernel, parametricEventKernel_apply _ _ _ _ ht]
        rfl
      rw [← hk]
      exact gaussianHalfspaceKernel_covariance hu t v
  · rw [gaussianSlabKernel_apply u a b hp, cond_cond_eq_cond_inter hA hC]
    have he : {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} ∩ {z : E | ⟪z, u⟫_ℝ ≤ t} =
        {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ min b t} := by
      ext z
      simp only [mem_inter_iff, mem_setOf_eq, le_min_iff]
      tauto
    rw [he]
    exact gaussianAmbientRow_slab_covariance hu a (min b t) v

theorem gaussianSlabKernel_lower_condition_covariance {u : E} (hu : ‖u‖ = 1)
    (a b t : ℝ) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ)
      ((gaussianSlabKernel u (a, b))[|{z : E | t ≤ ⟪z, u⟫_ℝ}]) ≤
        ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hu' : ‖-u‖ = 1 := by simpa only [norm_neg] using hu
  have h := gaussianSlabKernel_upper_condition_covariance hu' (-b) (-a) (-t) v
  rw [gaussianSlabKernel_neg] at h
  simpa only [inner_neg_right, neg_le_neg_iff] using h

theorem gaussianSlabKernel_interval_condition_covariance {u : E} (hu : ‖u‖ = 1)
    (a b c d : ℝ) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ)
      ((gaussianSlabKernel u (a, b))[|{z : E | c ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ d}]) ≤
        ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hs (l r : ℝ) : MeasurableSet {z : E | l ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ r} :=
    (measurableSet_le measurable_const hr).inter (measurableSet_le hr measurable_const)
  by_cases hp : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} = 0
  · rw [gaussianSlabKernel_apply_zero u a b hp]
    exact gaussianAmbientRow_slab_covariance hu c d v
  · rw [gaussianSlabKernel_apply u a b hp, cond_cond_eq_cond_inter (hs a b) (hs c d)]
    have he : {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} ∩
        {z : E | c ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ d} =
        {z : E | max a c ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ min b d} := by
      ext z
      simp only [mem_inter_iff, mem_setOf_eq, max_le_iff, le_min_iff]
      tauto
    rw [he]
    exact gaussianAmbientRow_slab_covariance hu (max a c) (min b d) v

end
end Nonsmooth
