import SampleReuse.CurvatureFirstActualSuccess
import SampleReuse.CurvatureFirstCountsMeasurable
import SampleReuse.CurvatureFirstGradientCostCoupling
import SampleReuse.CurvatureFirstHessianCostCoupling
import SampleReuse.OracleCapEventProbability

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def optimizerGradientExpectedBudget (P : Parameters) (ε γ scaleG : ℝ) (depth : ℕ) : ℝ :=
  1+2*(32*P.gradientLip*P.gap/(3*ε^2)) +
    scaleG*(P.gradientNoise^2+4*(depth:ℝ)*
      (P.gradientNoise*P.gradientLip*(8*P.gap/(3*ε))+P.gradientLip^2*(12*P.gap/γ)))

def optimizerHessianExpectedBudget (P : Parameters) (ε γ scaleH : ℝ) (depth : ℕ) : ℝ :=
  1+2*((32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3)*P.gap) +
    scaleH*(P.hessianNoise^2+4*(depth:ℝ)*
      (P.hessianNoise*P.hessianLip*(8*P.gap/(3*ε))+P.hessianLip^2*(12*P.gap/γ)))

theorem optimizerGradientExpectedBudget_nonneg (P : Parameters) {ε γ scaleG : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) (hs : 0 ≤ scaleG) (depth : ℕ) :
    0 ≤ optimizerGradientExpectedBudget P ε γ scaleG depth := by
  unfold optimizerGradientExpectedBudget
  have := P.gradientLip_pos
  have := P.gradientNoise_pos
  have := P.gap_pos
  positivity

theorem optimizerHessianExpectedBudget_nonneg (P : Parameters) {ε γ scaleH : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) (hs : 0 ≤ scaleH) (depth : ℕ) :
    0 ≤ optimizerHessianExpectedBudget P ε γ scaleH depth := by
  unfold optimizerHessianExpectedBudget
  have := P.gradientLip_pos
  have := P.hessianLip_pos
  have := P.hessianNoise_pos
  have := P.gap_pos
  positivity

theorem Admissible.curvatureFirst_gradient_cap_probability {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH M : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ) (hs : 0 ≤ scaleG)
    (hcap : Bg = batchSize scaleG (P.gradientNoise^2)) (horizon : M ≤ T+1)
    (depth : ℕ) (hd : M < 2^depth) (Cg : ℕ) :
    (((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod
      (PMF.uniformOfFintype (Fin M → Bool)).toMeasure).real {w |
        MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4) f F x₀
          (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2) ∧
        Cg < (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F
          (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2) M 0 (optimizerInitial x₀)).1} ≤
      optimizerGradientExpectedBudget P ε γ scaleG depth/((Cg:ℝ)+1) := by
  let A := (SampleTape ((T+1)*Bg) Ω × SampleTape ((T+1)*BH) Ω) × (Fin M → Bool)
  have hg : MeasurableSet {w : A | MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4)
      f F x₀ (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2)} :=
    had.macroAccurate_measurableSet hBg hBH ε γ scaleG scaleH (ε/4) (γ/4)
      _ ((derivativeTapes_measurable _ _).comp measurable_fst)
      _ ((extendFiniteSigns_measurable M).comp measurable_snd)
  have hc : Measurable (fun w : A => curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F
      (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2) M 0 (optimizerInitial x₀)) :=
    curvatureFirstDerivativeCounts_measurable hBg hBH P ε γ scaleG scaleH F
      had.gradient_measurable had.hessian_measurable _
      ((derivativeTapes_measurable _ _).comp measurable_fst)
      _ ((extendFiniteSigns_measurable M).comp measurable_snd) M 0 _ measurable_const
  apply product_event_real_bound_of_sections _ _ _
    (hg.inter (measurableSet_lt measurable_const hc.fst))
    (div_nonneg (optimizerGradientExpectedBudget_nonneg P hε hγ hs depth) (by positivity))
  intro tapes
  apply good_queryCount_exceed_probability _ _ _
    (stoppedGradientCost hBg hBH P ε γ scaleG scaleH f F (derivativeTapes tapes.1 tapes.2) x₀ depth)
  · intro bits hgood
    exact actual_gradient_queries_le_cost hBg hBH P ε γ scaleG scaleH f F tapes.1 tapes.2 x₀ bits
      horizon depth hd hcap
      (macroAccurate_initial_finiteValid hBg hBH P ε γ scaleG scaleH f F x₀ _ bits horizon hgood)
  · exact Integrable.of_finite
  · rw [PMF.integral_eq_sum]
    exact had.stopped_gradient_cost_bound hBg hBH hε hγ scaleG scaleH hs _ depth

theorem Admissible.curvatureFirst_hessian_cap_probability {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH M : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ) (hs : 0 ≤ scaleH)
    (hcap : BH = batchSize scaleH (P.hessianNoise^2)) (horizon : M ≤ T+1)
    (depth : ℕ) (hd : M < 2^depth) (CH : ℕ) :
    (((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod
      (PMF.uniformOfFintype (Fin M → Bool)).toMeasure).real {w |
        MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4) f F x₀
          (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2) ∧
        CH < (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F
          (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2) M 0 (optimizerInitial x₀)).2} ≤
      optimizerHessianExpectedBudget P ε γ scaleH depth/((CH:ℝ)+1) := by
  let A := (SampleTape ((T+1)*Bg) Ω × SampleTape ((T+1)*BH) Ω) × (Fin M → Bool)
  have hg : MeasurableSet {w : A | MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4)
      f F x₀ (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2)} :=
    had.macroAccurate_measurableSet hBg hBH ε γ scaleG scaleH (ε/4) (γ/4)
      _ ((derivativeTapes_measurable _ _).comp measurable_fst)
      _ ((extendFiniteSigns_measurable M).comp measurable_snd)
  have hc : Measurable (fun w : A => curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F
      (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2) M 0 (optimizerInitial x₀)) :=
    curvatureFirstDerivativeCounts_measurable hBg hBH P ε γ scaleG scaleH F
      had.gradient_measurable had.hessian_measurable _
      ((derivativeTapes_measurable _ _).comp measurable_fst)
      _ ((extendFiniteSigns_measurable M).comp measurable_snd) M 0 _ measurable_const
  apply product_event_real_bound_of_sections _ _ _
    (hg.inter (measurableSet_lt measurable_const hc.snd))
    (div_nonneg (optimizerHessianExpectedBudget_nonneg P hε hγ hs depth) (by positivity))
  intro tapes
  apply good_queryCount_exceed_probability _ _ _
    (stoppedHessianCost hBg hBH P ε γ scaleG scaleH f F (derivativeTapes tapes.1 tapes.2) x₀ depth)
  · intro bits hgood
    have hv := macroAccurate_initial_finiteValid hBg hBH P ε γ scaleG scaleH f F x₀ _ bits horizon hgood
    have he := curvatureStoppedQueryCounts_eq_actual_of_valid hBg hBH P ε γ scaleG scaleH f F
      (derivativeTapes tapes.1 tapes.2) (extendFiniteSigns bits) M 0 (optimizerInitial x₀) bits
      (by intro i; simp only [Nat.zero_add,extendFiniteSigns,dif_pos i.isLt]) hv
    rw [← he]
    exact curvatureStoppedQueryCounts_hessian_le_tree hBg hBH P ε γ scaleG scaleH f F
      (derivativeTapes tapes.1 tapes.2) x₀ bits depth hd hcap
  · exact Integrable.of_finite
  · rw [PMF.integral_eq_sum]
    exact had.stopped_hessian_cost_bound hBg hBH hε hγ scaleG scaleH hs _ depth

end
end SampleReuse
