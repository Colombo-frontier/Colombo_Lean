import Bilevel.GaussianDirectionTail
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The genuine isotropic Gaussian law and its orthogonal invariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace Bilevel.EuclideanGaussian

theorem preserving_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {g : α → β} (hg : MeasurePreserving g μ ν)
    (f : β → ℝ≥0∞) (hf : Measurable f) :
    MeasurePreserving g (μ.withDensity (f ∘ g)) (ν.withDensity f) := by
  refine ⟨hg.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hg.measurable hs, withDensity_apply _ (hg.measurable hs), withDensity_apply _ hs]
  exact hg.setLIntegral_comp_preimage hs hf

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def density (d : ℕ) (x : Space d) : ℝ := GaussianAffinity.density d 0 1 (fun i => x i)
def law (d : ℕ) : Measure (Space d) := volume.withDensity (fun x => ENNReal.ofReal (density d x))

theorem density_measurable (d : ℕ) : Measurable (density d) :=
  (GaussianProductLaw.density_measurable d 0 1).comp (EuclideanSpace.measurableEquiv (Fin d)).measurable

theorem coordinates_preserving (d : ℕ) :
    MeasurePreserving (EuclideanSpace.measurableEquiv (Fin d)) (law d)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  rw [GaussianProductLaw.gaussian_pi_eq_withDensity d 0 1 (by norm_num)]
  exact preserving_withDensity (EuclideanSpace.volume_preserving_measurableEquiv (Fin d))
    (fun x => ENNReal.ofReal (GaussianAffinity.density d 0 1 x))
    (GaussianProductLaw.density_measurable d 0 1).ennreal_ofReal

instance law_probability (d : ℕ) : IsProbabilityMeasure (law d) := by
  have h := congrArg (fun μ : Measure (Fin d → ℝ) => μ Set.univ) (coordinates_preserving d).map_eq
  dsimp only at h
  rw [Measure.map_apply (EuclideanSpace.measurableEquiv (Fin d)).measurable MeasurableSet.univ,
    Set.preimage_univ, measure_univ (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1))] at h
  exact ⟨h⟩

theorem density_radial (d : ℕ) (x : Space d) :
    density d x = (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2) := by
  simp only [density, GaussianAffinity.density, gaussianPDFReal, NNReal.coe_one,
    sub_zero, mul_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 1
  congr 1
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, ← Finset.sum_div, ← Finset.sum_neg_distrib]

theorem density_isometry (d : ℕ) (U : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d) :
    density d (U x) = density d x := by rw [density_radial, density_radial, U.norm_map]

theorem orthogonal_invariance (d : ℕ) (U : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving U (law d) (law d) := by
  have h := preserving_withDensity U.measurePreserving
    (fun x => ENNReal.ofReal (density d x)) (density_measurable d).ennreal_ofReal
  simpa only [Function.comp_def, density_isometry, law] using h

end Bilevel.EuclideanGaussian
