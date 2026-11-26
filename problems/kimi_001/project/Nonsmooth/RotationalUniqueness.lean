import Nonsmooth.OrthogonalSphere
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

open MeasureTheory Metric Filter Function
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Uniqueness of the actual rotation-invariant unit-sphere probability, via orthogonal
Haar averaging and bounded continuous tests. -/
theorem rotational_unit_probability_unique (μ : Measure E) [IsProbabilityMeasure μ]
    (hu : ∀ᵐ z ∂μ, ‖z‖ = 1)
    (hi : ∀ e : E ≃ₗᵢ[ℝ] E, Measure.map e μ = μ) : μ = sphericalLaw E := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hc : Continuous (fun p : OrthogonalTransform E × E => f (p.1.val p.2)) :=
    f.continuous.comp orthogonalAction_continuous
  have hint : Integrable (fun p : OrthogonalTransform E × E => f (p.1.val p.2))
      ((orthogonalHaar E).prod μ) :=
    (integrable_const ‖f‖).mono' hc.measurable.aestronglyMeasurable
      (Eventually.of_forall (fun p => f.norm_coe_le_norm (p.1.val p.2)))
  have hfirst (Q : OrthogonalTransform E) :
      (∫ z : E, f (Q.val z) ∂μ) = ∫ z : E, f z ∂μ := by
    let e : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv Q
    have hp : MeasurePreserving e μ μ := ⟨e.continuous.measurable, hi e⟩
    exact hp.integral_comp e.toMeasurableEquiv.measurableEmbedding f
  have hsecond : (∫ z : E, (∫ Q : OrthogonalTransform E, f (Q.val z) ∂orthogonalHaar E) ∂μ) =
      ∫ z : E, f z ∂sphericalLaw E := by
    calc
      _ = ∫ _z : E, (∫ w : E, f w ∂sphericalLaw E) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hu] with z hz
        exact orthogonalHaar_sphere_integral hz f.continuous
      _ = _ := by simp
  have hswap := integral_integral_swap (μ := orthogonalHaar E) (ν := μ)
    (f := fun (Q : OrthogonalTransform E) (z : E) => f (Q.val z)) hint
  simp_rw [hfirst] at hswap
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hswap.trans hsecond

end
end Nonsmooth
