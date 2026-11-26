import NCConcave16991.MixedHaarProjectedCompletionLaw

/-! # A fixed stabilizer source for every public unit inverse target -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

attribute [local irreducible] sphereSelector householder householderOrthogonal orthogonalOfIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

def targetedProjectedInverseCompletion (D : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] SphereSpace k)
    (e₀ e : SphereSpace k) (p : E × pointStabilizer e₀) : Haar.OrthogonalGroup k :=
  sphereSelector e₀ e * projectedInverseCompletion D U e₀ p

/-- The independent subgroup Haar source fixes e0 once and for all. A public
target e only changes a measurable left translation. -/
theorem targetedProjectedInverseCompletion_preserving (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e₀ : SphereSpace k) (he₀ : ‖e₀‖ = 1) (e : SphereSpace k) :
    MeasurePreserving (targetedProjectedInverseCompletion D U e₀ e)
      ((stdGaussian E).prod (pointStabilizerLaw e₀)) (Haar.haarLaw k) := by
  exact (measurePreserving_mul_left (Haar.haarLaw k) (sphereSelector e₀ e)).comp
    (projectedInverseCompletion_preserving D U e₀ he₀)

theorem targetedProjectedInverseCompletion_joint_measurable (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e₀ : SphereSpace k) (he₀ : ‖e₀‖ = 1) :
    Measurable (fun p : SphereSpace k × (E × pointStabilizer e₀) ↦
      targetedProjectedInverseCompletion D U e₀ p.1 p.2) := by
  have hs := (sphereSelector_measurable e₀).comp
    (measurable_fst : Measurable (Prod.fst : SphereSpace k × (E × pointStabilizer e₀) → SphereSpace k))
  have hc := (projectedInverseCompletion_preserving D U e₀ he₀).measurable.comp
    (measurable_snd : Measurable (Prod.snd : SphereSpace k × (E × pointStabilizer e₀) → E × pointStabilizer e₀))
  rw [show (fun p : SphereSpace k × (E × pointStabilizer e₀) ↦
      targetedProjectedInverseCompletion D U e₀ p.1 p.2) =
      ((fun p : SphereSpace k × (E × pointStabilizer e₀) ↦ sphereSelector e₀ p.1) *
        (fun p : SphereSpace k × (E × pointStabilizer e₀) ↦ projectedInverseCompletion D U e₀ p.2)) from rfl]
  exact hs.mul hc

theorem targetedProjectedInverseCompletion_image (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e₀ e : SphereSpace k) (he₀ : ‖e₀‖ = 1) (he : ‖e‖ = 1)
    (g : E) (hg : D.orthogonalProjectionOnto g ≠ 0) (h : pointStabilizer e₀) :
    Haar.orthogonalLinearIsometryEquiv (targetedProjectedInverseCompletion D U e₀ e (g,h))
      (projectedSample D U g) = e := by
  have hbase : Haar.orthogonalLinearIsometryEquiv (projectedInverseCompletion D U e₀ (g,h))
      (projectedSample D U g) = e₀ := by
    rw [← projectedForwardCompletion_image D U e₀ he₀ g hg h,projectedInverseCompletion,
      ← Haar.action_mul,inv_mul_cancel,Haar.action_one]
  rw [targetedProjectedInverseCompletion,Haar.action_mul,hbase]
  exact sphereSelector_action e₀ e (he₀.trans he.symm)

/-- The exact local joint transition law with a fixed-dimensional Gaussian
slot and a fixed reference point-stabilizer Haar source. -/
theorem targetedProjectedInverseCompletion_jointLaw (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e₀ e : SphereSpace k) (he₀ : ‖e₀‖ = 1) (he : ‖e‖ = 1) :
    ((stdGaussian E).prod (pointStabilizerLaw e₀)).map
        (fun p ↦ (projectedSample D U p.1,targetedProjectedInverseCompletion D U e₀ e p)) =
      (Haar.haarLaw k).map (fun Q ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)) := by
  let μ := (stdGaussian E).prod (pointStabilizerLaw e₀)
  let observe := fun Q : Haar.OrthogonalGroup k ↦ (Haar.orthogonalLinearIsometryEquiv Q⁻¹ e,Q)
  have ho : Measurable observe :=
    ((Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable.comp measurable_inv).prodMk measurable_id
  have hgen := targetedProjectedInverseCompletion_preserving D U e₀ he₀ e
  have hfst : MeasurePreserving (Prod.fst : E × pointStabilizer e₀ → E) μ (stdGaussian E) := measurePreserving_fst
  have hunit : ‖U.symm e₀‖ = 1 := (U.symm.norm_map e₀).trans he₀
  have hgood := hfst.quasiMeasurePreserving.ae (stdGaussian_projection_ne_zero_ae_of_unit D (U.symm e₀) hunit)
  have heq : (fun p : E × pointStabilizer e₀ ↦
      (projectedSample D U p.1,targetedProjectedInverseCompletion D U e₀ e p)) =ᵐ[μ]
      observe ∘ targetedProjectedInverseCompletion D U e₀ e := by
    filter_upwards [hgood] with p hp
    apply Prod.ext
    · change projectedSample D U p.1 =
        Haar.orthogonalLinearIsometryEquiv (targetedProjectedInverseCompletion D U e₀ e p)⁻¹ e
      apply (Haar.orthogonalLinearIsometryEquiv (targetedProjectedInverseCompletion D U e₀ e p)).injective
      rw [← Haar.action_mul,mul_inv_cancel,Haar.action_one]
      exact targetedProjectedInverseCompletion_image D U e₀ e he₀ he p.1 hp p.2
    · rfl
  rw [Measure.map_congr heq]
  have hm := Measure.map_map (μ := μ) ho hgen.measurable
  rw [← hm,hgen.map_eq]

end NCConcave16991.MixedHaar
