import Nonsmooth.ScalarConcentrationRank
import Nonsmooth.DeterminedScalarPosterior
import Nonsmooth.SupportWinnerRank

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem spanning_unit_projection_rank (μ : Measure E) [IsProbabilityMeasure μ]
    {u : E} (hu : ‖u‖ = 1) (hspan : (ℝ ∙ u : Submodule ℝ E) = ⊤)
    (hatom : ∀ y, μ {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hi : ∀ r : ℝ, Integrable (fun z : E =>
      Real.exp (r * (⟪z, u⟫_ℝ - ∫ w : E, ⟪w, u⟫_ℝ ∂μ))) μ)
    (hb : ∀ r : ℝ, (∫ z : E,
      Real.exp (r * (⟪z, u⟫_ℝ - ∫ w : E, ⟪w, u⟫_ℝ ∂μ)) ∂μ) ≤ Real.exp (r ^ 2 / 2)) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        2 * rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y) := by
  let X : E → ℝ := fun z => ⟪z, u⟫_ℝ
  let m := ∫ z : E, X z ∂μ
  have hX : Measurable X := by fun_prop
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hs (z : E) : z = X z • u := by
    have hz : z ∈ (ℝ ∙ u : Submodule ℝ E) := by rw [hspan]; trivial
    exact (((ℝ ∙ u : Submodule ℝ E).starProjection_eq_self_iff).mpr hz).symm.trans
      (unit_orthogonalProjection_formula hu z)
  have hm : (∫ z : E, z ∂μ) = m • u := by
    calc
      _ = ∫ z : E, X z • u ∂μ := integral_congr_ae (Eventually.of_forall hs)
      _ = _ := integral_smul_const _ _
  have hat : ∀ y : ℝ, (μ.map X) {y} = 0 := by
    intro y
    rw [Measure.map_apply hX (measurableSet_singleton y)]
    exact hatom y
  have hExp (r : ℝ) : StronglyMeasurable (fun y : ℝ => Real.exp (r * (y - m))) :=
    (by fun_prop : Continuous (fun y : ℝ => Real.exp (r * (y - m)))).stronglyMeasurable
  have hi' (r : ℝ) : Integrable (fun y : ℝ => Real.exp (r * (y - m))) (μ.map X) :=
    (integrable_map_measure (hExp r).aestronglyMeasurable hX.aemeasurable).mpr (hi r)
  have hb' (r : ℝ) : (∫ y : ℝ, Real.exp (r * (y - m)) ∂μ.map X) ≤ Real.exp (r ^ 2 / 2) := by
    rw [integral_map_of_stronglyMeasurable hX (hExp r)]
    exact hb r
  filter_upwards [scalar_unit_mgf_rank_ae (μ.map X) m hat hi' hb',
    spanning_unit_observation_posterior μ hu hspan] with y hy hp
  unfold projectionPosteriorShift
  rw [hp, integral_dirac, hm, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  exact hy

end
end Nonsmooth
