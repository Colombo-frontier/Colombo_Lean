import Nonsmooth.InteriorDepthCenter
import Nonsmooth.CenteredBodyTranslation
import Nonsmooth.QuarterDepthNormalization
import Nonsmooth.LinearDepthTransport

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Geometry and a uniform volume depth are chosen from the body alone. -/
theorem exists_general_body_normalization {K : Set E} (hconv : Convex ℝ K)
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty) :
    ∃ c ∈ interior K, ∃ L : E ≃L[ℝ] E,
      let G := L '' centeredBody c K
      Convex ℝ G ∧ IsCompact G ∧
      Metric.closedBall (0 : E) (1 / (Module.finrank ℝ E : ℝ)) ⊆ G ∧
      G ⊆ Metric.closedBall (0 : E) (4 * (Module.finrank ℝ E : ℝ) ^ 2) ∧
      ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
        ENNReal.ofReal (1 / 4 : ℝ) * volume G ≤ volume (G ∩ {z | 0 ≤ ℓ z}) := by
  obtain ⟨c, hc, hdepth⟩ := exists_interior_quarter_depth_center K hconv hcompact hinterior
  obtain ⟨r, hr, hinner⟩ := centeredBody_contains_ball hc
  have hconv0 := centeredBody_convex c hconv
  have hcompact0 := centeredBody_compact c hcompact
  have hdepth0 := centeredBody_quarter_depth hdepth
  obtain ⟨L, hLi, hLo⟩ := exists_quarter_depth_normalization hconv0 hcompact0 hr hinner hdepth0
  exact ⟨c, hc, L, hconv0.linear_image L.toLinearMap, hcompact0.image L.continuous,
    hLi, hLo, linear_equiv_quarter_depth L hdepth0⟩

end
end Nonsmooth
