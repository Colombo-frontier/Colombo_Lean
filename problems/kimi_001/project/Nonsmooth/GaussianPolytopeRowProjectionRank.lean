import Nonsmooth.AffinePolytopeProjectionRank
import Nonsmooth.DeterminedProjectionShift

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeModel_projection_rank {s : ℝ} (hs : 0 < s)
    (M : GaussianPolytopeModel E) (q : E) :
    let ν := gaussianPolytopeModelLaw s M
    ∀ᵐ y ∂ν.map (fun z : E => ⟪z, q⟫_ℝ),
      ‖projectionPosteriorShift ν q y‖ ^ 2 ≤
        (s ^ 2 * 72) * (1 + rankQuantileLog (cdf (ν.map (fun z : E => ⟪z, q⟫_ℝ)) y)) := by
  by_cases hv : gaussianPolytopeQueryVector M q = 0
  · have hf := gaussianPolytopeModelMap_measurable s M
    have hX : Measurable (fun z : E => ⟪z, q⟫_ℝ) := by fun_prop
    have hconst : ∀ᵐ z ∂gaussianPolytopeModelLaw s M, ⟪z, q⟫_ℝ = ⟪M.origin, q⟫_ℝ := by
      apply (ae_map_iff hf.aemeasurable (measurableSet_eq_fun hX measurable_const)).mpr
      apply Eventually.of_forall
      intro z
      rw [gaussianPolytopeModelMap_inner, hv, inner_zero_right, mul_zero, add_zero]
    exact projection_rank_of_constant (gaussianPolytopeModelLaw s M)
      ((gaussianPolytopeRow_memLp s _ (Or.inr ⟨M, rfl⟩)).integrable (by norm_num))
      q ⟪M.origin, q⟫_ℝ hconst (by positivity)
  · exact gaussianPolytopeModel_nondegenerate_projection_rank hs M q hv

theorem gaussianPolytopeRow_projection_rank {s : ℝ} (hs : 0 < s)
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : GaussianPolytopeRow s ν) (q : E) :
    ∀ᵐ y ∂ν.map (fun z : E => ⟪z, q⟫_ℝ),
      ‖projectionPosteriorShift ν q y‖ ^ 2 ≤
        (s ^ 2 * 72) * (1 + rankQuantileLog (cdf (ν.map (fun z : E => ⟪z, q⟫_ℝ)) y)) := by
  rcases hν with ⟨x, rfl⟩ | ⟨M, rfl⟩
  · exact projection_rank_of_constant (Measure.dirac x) (integrable_dirac (by simp)) q ⟪x, q⟫_ℝ
      (ae_eq_dirac (fun z => ⟪z, q⟫_ℝ)) (by positivity)
  · exact gaussianPolytopeModel_projection_rank hs M q

end
end Nonsmooth
