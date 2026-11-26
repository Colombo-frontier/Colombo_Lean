import SecondOrder.FullScaleUpper

open MeasureTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

def manuscriptCurvatureCount (P : Parameters) (ν γ : ℝ) : ℝ :=
  P.gap*P.hessianHolder^(2/ν)*γ^(-(1+2/ν))

def holderMoveFactor (ν : ℝ) : ℝ := 1+(16/3:ℝ)*8^(2/ν)

/-- Exactly the scale terms displayed in the manuscript's full upper
bound. The constrained minimum is attained and uses Nbar=1+ceil(ΔL/ε²). -/
def manuscriptUpperScale (P : Parameters) (ν ε γ : ℝ) : ℝ :=
  1+P.gradientNoise^2/ε^2+P.gap*P.gradientLip/ε^2+manuscriptCurvatureCount P ν γ+
  P.gap*chordVarianceScale P/(ε^2*γ)+epochMinimum P ε+
  (1+manuscriptCurvatureCount P ν γ)*(eigenHessianBound P)^2/γ^2

theorem curvatureCountCoefficient_factor (P : Parameters) (ν γ : ℝ) :
    curvatureCountCoefficient P ν*γ^(-(1+2/ν)) =
      ((16/3:ℝ)*8^(2/ν))*manuscriptCurvatureCount P ν γ := by
  unfold curvatureCountCoefficient manuscriptCurvatureCount
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) P.hessianHolder_pos.le]
  ring

theorem manuscriptUpperScale_nonneg (P : Parameters) (ν : ℝ) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) : 0 ≤ manuscriptUpperScale P ν ε γ := by
  have he := epochMinimum_nonneg P hε
  have hΔ := P.gap_pos
  have hL := P.gradientLip_pos
  have hH := P.hessianHolder_pos
  have hV := chordVarianceScale_pos P
  unfold manuscriptUpperScale manuscriptCurvatureCount
  positivity

theorem fullUpperScale_le_manuscript (P : Parameters) (ν : ℝ) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) :
    fullUpperScale P ν ε γ ≤ holderMoveFactor ν*manuscriptUpperScale P ν ε γ := by
  let c : ℝ := (16/3:ℝ)*8^(2/ν)
  let K := manuscriptCurvatureCount P ν γ
  let T := 1+P.gradientNoise^2/ε^2+P.gap*P.gradientLip/ε^2+
    P.gap*chordVarianceScale P/(ε^2*γ)+epochMinimum P ε
  let Z := (eigenHessianBound P)^2/γ^2
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hK : 0 ≤ K := by
    have hΔ := P.gap_pos
    have hH := P.hessianHolder_pos
    dsimp only [K, manuscriptCurvatureCount]
    positivity
  have hT : 0 ≤ T := by
    have he := epochMinimum_nonneg P hε
    have hΔ := P.gap_pos
    have hL := P.gradientLip_pos
    have hV := chordVarianceScale_pos P
    dsimp only [T]
    positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hb : T+c*K+(1+c*K)*Z ≤ (1+c)*(T+K+(1+K)*Z) := by
    nlinarith [mul_nonneg hc hT, mul_nonneg hc hZ, mul_nonneg hK hZ]
  rw [fullUpperScale_expansion P ν ε hγ, curvatureCountCoefficient_factor]
  convert hb using 1 <;>
    dsimp only [T, K, Z, c, holderMoveFactor, manuscriptUpperScale] <;> ring

theorem fullUpperLogFactor_nonneg (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) :
    0 ≤ fullUpperLogFactor P ν d ε γ := by
  have hh := chordConfidenceFactor_nonneg
    (localFailureTolerance_pos (physicalCap P ν (ε/10) γ)) (localFailureTolerance_le_one _)
  have hf := ojaFullPriceFactor_nonneg d (localFailureTolerance (physicalCap P ν (ε/10) γ))
  unfold fullUpperLogFactor
  positivity

/-- A ceiling-free envelope consisting only of polynomials in logarithms
of dimension and the deterministic move budget. -/
def manuscriptLogEnvelope (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) : ℝ :=
  25+24*(6144*10000*(depthLogEnvelope P ν (ε/10) γ)^3*confidenceLogEnvelope P ν (ε/10) γ+
    400*(104976+4000*2336)*(1+Real.log (4*(d:ℝ)))^2*
      (1+Real.log 384+Real.log (26+24*idealMoveBudget P ν (ε/10) γ))^2)

theorem fullUpperLogFactor_log_bound (P : Parameters) (ν : ℝ) (d : ℕ) (ε : ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    fullUpperLogFactor P ν d ε γ ≤ manuscriptLogEnvelope P ν d ε γ := by
  let M := physicalCap P ν (ε/10) γ
  let δ := localFailureTolerance M
  have hl := selected_log_factors_bound P ν (ε/10) hγ
  have hc := selectedConfidence_log_bound P ν (ε/10) hγ
  have ho : ojaConfidenceLog δ ≤ 1+Real.log 384+Real.log (26+24*idealMoveBudget P ν (ε/10) γ) := by
    unfold confidenceLogEnvelope at hc
    dsimp only [ojaConfidenceLog, δ, M]
    linarith
  have ho0 : 0 ≤ ojaConfidenceLog δ :=
    le_trans (by norm_num) (one_le_ojaConfidenceLog (localFailureTolerance_pos M) (localFailureTolerance_le_one M))
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ho0 ho 2)
    (show 0 ≤ 400*(104976+4000*2336)*(1+Real.log (4*(d:ℝ)))^2 by positivity)
  unfold fullUpperLogFactor manuscriptLogEnvelope ojaFullPriceFactor
  dsimp only [δ, M] at hs
  nlinarith [hl, hs]

theorem stochasticUpperCap_manuscript (P : Parameters) (ν : ℝ) (d : ℕ)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    (stochasticUpperCap P ν d ε γ : ℝ) <
      (holderMoveFactor ν*fullUpperLogFactor P ν d ε γ)*manuscriptUpperScale P ν ε γ := by
  apply (stochasticUpperCap_full_scale P ν d hε hγ).trans_le
  have hb := mul_le_mul_of_nonneg_left (fullUpperScale_le_manuscript P ν hε hγ)
    (fullUpperLogFactor_nonneg P ν d ε γ)
  exact hb.trans_eq (by ring)

theorem stochasticUpperCap_manuscript_log (P : Parameters) (ν : ℝ) (d : ℕ)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    (stochasticUpperCap P ν d ε γ : ℝ) <
      (holderMoveFactor ν*manuscriptLogEnvelope P ν d ε γ)*manuscriptUpperScale P ν ε γ := by
  apply (stochasticUpperCap_manuscript P ν d hε hγ).trans_le
  have hν : 0 ≤ holderMoveFactor ν := by unfold holderMoveFactor; positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (fullUpperLogFactor_log_bound P ν d ε hγ) hν)
    (manuscriptUpperScale_nonneg P ν hε hγ)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The full manuscript upper scale, with explicit logarithmic overhead
and success at least 2/3, for the implemented gradient/HVP algorithm. -/
theorem CommonLoss.stochasticUpperRun_manuscript (h : CommonLoss μ P ν F f)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    (∀ w : StochasticUpperTape Ω d P ν ε γ,
      ((stochasticUpperTrace P ν f ε γ w).length : ℝ) <
        (holderMoveFactor ν*manuscriptLogEnvelope P ν d ε γ)*manuscriptUpperScale P ν ε γ) ∧
    ENNReal.ofReal (2/3:ℝ) ≤ stochasticUpperLaw μ P ν d ε hγ
      {w | BudgetedSuccess F ε γ (stochasticUpperRun P ν f ε γ w)} := by
  refine ⟨fun w => ?_, ?_⟩
  · exact (Nat.cast_le.mpr (stochasticUpperTrace_cap P ν f ε γ w)).trans_lt
      (stochasticUpperCap_manuscript_log P ν d hε hγ)
  · exact (ENNReal.ofReal_le_ofReal (by norm_num : (2/3:ℝ) ≤ 29/32)).trans
      (h.stochasticUpperRun_success hε hγ)

end
end SecondOrder
