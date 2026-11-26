import NCConcave16991.PartialIsometryCompletion
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # The literal Gaussian inverse-reveal vector and its one-slot span bound -/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (D R : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] R)

def residual (D : Submodule ℝ E) (g : E) : E := g - D.starProjection g

def knownInverse (x : E) : E := U.symm (R.orthogonalProjectionOnto x)

def inverseCandidate (x g : E) : E :=
  knownInverse D R U x + (‖residual R x‖ / ‖residual D g‖) • residual D g

theorem residual_continuous : Continuous (residual D) := continuous_id.sub D.starProjection.continuous

theorem knownInverse_continuous : Continuous (knownInverse D R U) :=
  continuous_subtype_val.comp (U.symm.continuous.comp R.orthogonalProjectionOnto.continuous)

theorem inverseCandidate_measurable : Measurable (fun p : E × E ↦ inverseCandidate D R U p.1 p.2) := by
  have hd := (residual_continuous D).measurable.comp (measurable_snd : Measurable (fun p : E × E ↦ p.2))
  have hr := (residual_continuous R).measurable.comp (measurable_fst : Measurable (fun p : E × E ↦ p.1))
  exact ((knownInverse_continuous D R U).measurable.comp measurable_fst).add ((hr.norm.div hd.norm).smul hd)

theorem residual_mem_orthogonal (g : E) : residual D g ∈ Dᗮ := D.sub_starProjection_mem_orthogonal g

theorem knownInverse_mem (x : E) : knownInverse D R U x ∈ D := (U.symm (R.orthogonalProjectionOnto x)).property

theorem knownInverse_norm (x : E) : ‖knownInverse D R U x‖ = ‖R.starProjection x‖ := by
  change ‖U.symm (R.orthogonalProjectionOnto x)‖ = _
  rw [U.symm.norm_map]
  rfl

theorem knownInverse_residual_inner (x g : E) : ⟪knownInverse D R U x,residual D g⟫_ℝ = 0 :=
  (D.mem_orthogonal _).mp (residual_mem_orthogonal D g) _ (knownInverse_mem D R U x)

/-- The formal answer uses only the old exposed formal span and its one
assigned fresh Gaussian. This remains true for repeated or dependent probes. -/
theorem inverseCandidate_mem_old_sup_gaussian (x g : E) :
    inverseCandidate D R U x g ∈ D ⊔ Submodule.span ℝ ({g} : Set E) := by
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (knownInverse_mem D R U x)
  · apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton g))
    · exact Submodule.mem_sup_left (Submodule.coe_mem _)

theorem scaled_residual_norm (x g : E) (hg : residual D g ≠ 0) :
    ‖(‖residual R x‖ / ‖residual D g‖) • residual D g‖ = ‖residual R x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hg)]

theorem inverseCandidate_norm (x g : E) (hg : residual D g ≠ 0) :
    ‖inverseCandidate D R U x g‖ = ‖x‖ := by
  have hsq : ‖inverseCandidate D R U x g‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [inverseCandidate, norm_add_sq_real, real_inner_smul_right, knownInverse_residual_inner,
      mul_zero, mul_zero, add_zero, knownInverse_norm, scaled_residual_norm D R x g hg]
    have hh := R.norm_sq_eq_add_norm_sq_starProjection x
    rw [R.starProjection_orthogonal_val] at hh
    change ‖x‖ ^ 2 = ‖R.starProjection x‖ ^ 2 + ‖residual R x‖ ^ 2 at hh
    linarith only [hh]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem inverseCandidate_old_inner (x g : E) (z : D) :
    ⟪(z : E),inverseCandidate D R U x g⟫_ℝ = ⟪(z : E),knownInverse D R U x⟫_ℝ := by
  rw [inverseCandidate, inner_add_right, real_inner_smul_right]
  have hh := (D.mem_orthogonal _).mp (residual_mem_orthogonal D g) (z : E) z.property
  rw [hh, mul_zero, add_zero]

end NCConcave16991.MixedHaar
