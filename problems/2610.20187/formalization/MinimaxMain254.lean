import NormalizedMinimax254

noncomputable section
open MeasureTheory
namespace Paper254

/-- The matching result in one loss class. The upper learner is chosen
before losses and the comparator; the lower hard sequence is chosen
outside the randomized learner's expectation. The logarithm is explicit. -/
def DimensionOptimalStatement.{u} : Prop :=
  ∃ C c c₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < c₀ ∧
  ∀ d T : ℕ, 0 < d → 0 < T → c₀*(d : ℝ)^2 ≤ T →
    (∀ W : Domain d 1, ∃ A : OnlineLearner W T,
      ∀ f : Fin T → Loss d, (∀ t,AdmissibleLoss W (3/2) (4/9) (f t)) →
      ∀ v : Fin T → W.carrier,
        regret A f v ≤ C*logFactor T^2*normalizedFrontier d T (pathLength v)) ∧
    (∀ P : ℝ, 0 ≤ P →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ A : Ω → OnlineLearner (ballDomain d) T,SeedMeasurable A →
      ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
        (∀ t,AdmissibleLoss (ballDomain d) (3/2) (4/9) (hardSequence s t)) ∧
        pathLength v ≤ P ∧
        c*normalizedFrontier d T P ≤ ∫ ω,regret (A ω) (hardSequence s) v ∂μ)

theorem dimension_optimal : DimensionOptimalStatement.{u} := by
  obtain ⟨C,hC,hupper⟩ := normalized_upper 1 (3/2) (4/9) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c,c₀,hc,hc₀,hlower⟩ := main_lower.{u}
  refine ⟨C,c,c₀,hC,hc,hc₀,?_⟩
  intro d T hd hT hlarge
  constructor
  · intro W
    exact hupper d T hd hT W
  · intro P hP Ω mΩ μ hμ A hA
    obtain ⟨s,v,hv,hr⟩ := hlower d T hd hT hlarge P hP Ω μ hμ A hA
    refine ⟨s,v,?_,hv,hr⟩
    intro t
    exact hard_loss_admissible (s t).1 (s t).2

end Paper254
#print axioms Paper254.dimension_optimal
