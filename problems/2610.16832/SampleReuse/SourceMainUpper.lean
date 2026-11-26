import SampleReuse.SourceUpperAlgorithm
import SampleReuse.CurvatureFirstOutputLaw

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem source_gradient_cap_ratio (P : Parameters) (d : ℕ) {ε γ : ℝ}
    (hε : 0<ε) (hγ : 0<γ) :
    optimizerGradientExpectedBudget P ε γ (sourceConfidenceScale d (sourceIterationCap P ε γ) ε)
      (binaryDepth (sourceIterationCap P ε γ)) / ((sourceGradientQueryCap P d ε γ:ℝ)+1) ≤ 1/48 := by
  apply (div_le_iff₀ (by positivity : 0<(sourceGradientQueryCap P d ε γ:ℝ)+1)).mpr
  have hb := source_gradient_expected_budget P d (sourceIterationCap P ε γ) hε hγ
  have hc := Nat.le_ceil (48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*sourceGradientBudget P ε γ)
  change optimizerGradientExpectedBudget P ε γ _ _ ≤ _ at hb
  change _ ≤ (sourceGradientQueryCap P d ε γ:ℝ) at hc
  linarith

theorem source_hessian_cap_ratio (P : Parameters) (d : ℕ) {ε γ : ℝ}
    (hε : 0<ε) (hγ : 0<γ) :
    optimizerHessianExpectedBudget P ε γ (sourceConfidenceScale d (sourceIterationCap P ε γ) γ)
      (binaryDepth (sourceIterationCap P ε γ)) / ((sourceHessianQueryCap P d ε γ:ℝ)+1) ≤ 1/48 := by
  apply (div_le_iff₀ (by positivity : 0<(sourceHessianQueryCap P d ε γ:ℝ)+1)).mpr
  have hb := source_hessian_expected_budget P d (sourceIterationCap P ε γ) hε hγ
  have hc := Nat.le_ceil (48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*sourceHessianBudget P ε γ)
  change optimizerHessianExpectedBudget P ε γ _ _ ≤ _ at hb
  change _ ≤ (sourceHessianQueryCap P d ε γ:ℝ) at hc
  linarith

/-- Main upper bound for the actual stopped algorithm and one iid persistent
sample tape. Accuracy, descent, finite stopping and both costs are derived
from the common scalar-loss assumptions; none is a premise of this theorem. -/
theorem Admissible.source_main_upper {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d→ℝ} {F : Ω→Point d→ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    (2/3:ℝ) ≤ ((sampleTapeLaw (sourceHandleCount P d ε γ) μ).prod
      (PMF.uniformOfFintype (Fin (sourceIterationCap P ε γ)→Bool)).toMeasure).real
        {w | IsSOSP f ε γ (sourceUpperOutput P d ε γ x₀ F w.1 w.2)} := by
  let T := sourceIterationCap P ε γ
  let Bg := sourceGradientRootBatch P d ε γ
  let BH := sourceHessianRootBatch P d ε γ
  let scaleG := sourceConfidenceScale d T ε
  let scaleH := sourceConfidenceScale d T γ
  let Cg := sourceGradientQueryCap P d ε γ
  let CH := sourceHessianQueryCap P d ε γ
  let q₀ := sourceUpperDefaultQuery P d ε γ x₀
  have hBg : 0<Bg := sourceGradientRootBatch_pos P d ε γ
  have hBH : 0<BH := sourceHessianRootBatch_pos P d ε γ
  have hsg : 0≤scaleG := confidenceBatchScale_nonneg _ _ _
  have hsh : 0≤scaleH := confidenceBatchScale_nonneg _ _ _
  obtain ⟨z₀,_⟩ := nonempty_of_measure_ne_zero (show μ Set.univ≠0 by simp)
  have hp := had.curvatureFirst_cap_success (M := T) hBg hBH hε hγ scaleG scaleH hsg hsh z₀
    (δG := 1/96) (δH := 1/96) (by norm_num) (by norm_num) rfl rfl rfl rfl
    (sourceIterationCap_pos P ε γ) (Nat.le_succ T) (binaryDepth T) (binaryDepth_sufficient le_rfl) Cg CH q₀
  have hg := source_gradient_cap_ratio P d hε hγ
  have hh := source_hessian_cap_ratio P d hε hγ
  have he := sourceIterationCap_exhaustion P hε hγ
  have hs : (2/3:ℝ) ≤ (((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod
      (PMF.uniformOfFintype (Fin T→Bool)).toMeasure).real {w | ∃x,
        cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH
          (derivativeTapes w.1.1 w.1.2) w.2=some x ∧ IsSOSP f ε γ x} := by
    change _ ≤ _ at hp
    dsimp only [T,scaleG,scaleH,Cg,CH] at hp
    linarith
  simp_rw [sourceUpperOutput_eq_padded]
  exact hs.trans (cappedCurvatureFirstOutput_fallback_probability hBg hBH P ε γ scaleG scaleH
    f F had.population_smooth had.gradient_measurable had.hessian_measurable q₀ x₀ Cg CH μ)

/-- A single parameter-selected algorithm, uniformly valid over every
admissible scalar loss and iid sample distribution in this dimension. -/
structure SourceUpperGuarantee (P : Parameters) (d : ℕ) (ε γ : ℝ) : Prop where
  observable : ∀ x₀ : Point d, OracleProgram.MeasurableFamily (sourceUpperDefaultQuery P d ε γ x₀) none
    (sourceUpperProgram P d ε γ x₀)
  stops : ∀ {Ω : Type} (x₀ : Point d) (F : Ω→Point d→ℝ)
    (tape : SampleTape (sourceHandleCount P d ε γ) Ω) (bits : Fin (sourceIterationCap P ε γ)→Bool),
    sourceUpperStop P d ε γ x₀ F tape bits≤sourceGradientQueryCap P d ε γ+sourceHessianQueryCap P d ε γ
  counts : ∀ {Ω : Type} (x₀ : Point d) (F : Ω→Point d→ℝ)
    (tape : SampleTape (sourceHandleCount P d ε γ) Ω) (bits : Fin (sourceIterationCap P ε γ)→Bool),
    (sourceUpperQueryCounts P d ε γ x₀ F tape bits).1≤sourceGradientQueryCap P d ε γ ∧
      (sourceUpperQueryCounts P d ε γ x₀ F tape bits).2≤sourceHessianQueryCap P d ε γ
  success : ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Point d→ℝ) (F : Ω→Point d→ℝ) (x₀ : Point d), Admissible μ P f F x₀ →
    (2/3:ℝ) ≤ ((sampleTapeLaw (sourceHandleCount P d ε γ) μ).prod
      (PMF.uniformOfFintype (Fin (sourceIterationCap P ε γ)→Bool)).toMeasure).real
        {w | IsSOSP f ε γ (sourceUpperOutput P d ε γ x₀ F w.1 w.2)}

theorem source_upper_guarantee (P : Parameters) (d : ℕ) {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    SourceUpperGuarantee P d ε γ where
  observable := sourceUpperProgram_measurableFamily P d ε γ
  stops := fun x₀ F tape bits => sourceUpperStop_le P d ε γ x₀ F tape bits
  counts := fun x₀ F tape bits => sourceUpperQueryCounts_le P d ε γ x₀ F tape bits
  success := by
    intro Ω instΩ μ instμ f F x₀ had
    exact had.source_main_upper hε hγ

end
end SampleReuse
