import SecondOrder.LowerPolylogFactors
import SecondOrder.PolylogQueryCap

open scoped ENNReal

namespace SecondOrder
noncomputable section

def holderMinimaxLowerCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  min (firstOrderEndpointThreshold P.gap (firstOrderHolderNoiseBudget P) 1)
    (curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P) 1 1 ν/
      (curvatureBlockLogCoefficient P.gap P.hessianHolder (curvatureNoiseBudget P) ν)^2)/2

def richMinimaxLowerCoefficient (P : Parameters) (σ₀ : ℝ) : ℝ :=
  min (firstOrderEndpointThreshold P.gap (firstOrderNoiseBudget P σ₀) 1)
    (curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P) 1 1/
      (curvatureBlockLogCoefficient P.gap (2*P.hessianHolder) (curvatureNoiseBudget P) 1)^2)/2

theorem holderMinimaxLowerCoefficient_pos (P : Parameters) {ν : ℝ} (hν : 0<ν) :
    0<holderMinimaxLowerCoefficient P ν := by
  have ha := firstOrderEndpointThreshold_pos P.gap_pos
    (firstOrderNoiseBudget_pos P P.gradientNoise_pos) (show (0:ℝ)<1 by norm_num)
  have hb := curvatureHolderThreshold_pos (ν := ν) P.gap_pos P.hessianHolder_pos
    (curvatureNoiseBudget_pos P) (show (0:ℝ)<1 by norm_num) (show (0:ℝ)<1 by norm_num)
  have hK := curvatureBlockLogCoefficient_pos (σ := curvatureNoiseBudget P) P.gap_pos.le P.hessianHolder_pos hν
  unfold holderMinimaxLowerCoefficient firstOrderHolderNoiseBudget
  positivity

theorem richMinimaxLowerCoefficient_pos (P : Parameters) {σ₀ : ℝ} (hσ₀ : 0<σ₀) :
    0<richMinimaxLowerCoefficient P σ₀ := by
  have ha := firstOrderEndpointThreshold_pos P.gap_pos
    (firstOrderNoiseBudget_pos P hσ₀) (show (0:ℝ)<1 by norm_num)
  have hb := curvatureEndpointThreshold_pos P.gap_pos P.hessianHolder_pos
    (curvatureNoiseBudget_pos P) (show (0:ℝ)<1 by norm_num) (show (0:ℝ)<1 by norm_num)
  have hK := curvatureBlockLogCoefficient_pos (σ := curvatureNoiseBudget P) P.gap_pos.le
    (mul_pos (show (0:ℝ)<2 by norm_num) P.hessianHolder_pos) (show (0:ℝ)<1 by norm_num)
  unfold richMinimaxLowerCoefficient
  positivity

theorem holderEndpoint_half_sum_rate (P : Parameters) {ν ε γ : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1) :
    holderMinimaxLowerCoefficient P ν/(toleranceLog ε γ)^2*holderEndpointRate ν ε γ≤
      (firstOrderEndpointThreshold P.gap (firstOrderHolderNoiseBudget P) ε+
        curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
          (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) γ ν)/2 := by
  let a := firstOrderEndpointThreshold P.gap (firstOrderHolderNoiseBudget P) 1
  let c := curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P) 1 1 ν
  let K := curvatureBlockLogCoefficient P.gap P.hessianHolder (curvatureNoiseBudget P) ν
  let D : ℝ := curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
  have ha : 0<a := firstOrderEndpointThreshold_pos P.gap_pos
    (firstOrderNoiseBudget_pos P P.gradientNoise_pos) (by norm_num)
  have hc : 0<c := curvatureHolderThreshold_pos P.gap_pos P.hessianHolder_pos
    (curvatureNoiseBudget_pos P) (by norm_num) (by norm_num)
  have hK : 0<K := curvatureBlockLogCoefficient_pos P.gap_pos.le P.hessianHolder_pos hν
  have hj := one_le_toleranceLog hε hε1 hγ hγ1
  have hD : 0<D := by
    have hh := (curvatureHolderBlockSize_bounds (σ := curvatureNoiseBudget P)
      P.gap_pos.le P.hessianHolder_pos hγ hν hν1).1
    dsimp only [D]
    exact_mod_cast (show 0<curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν by omega)
  have hDK : D≤K*toleranceLog ε γ := curvatureHolderBlockSize_le_toleranceLog
    P.gap_pos.le P.hessianHolder_pos hν hν1 hε hε1 hγ hγ1
  have hB := mul_le_mul_of_nonneg_right
    (inverse_block_sq_lower hc.le hD hK (by linarith only [hj]) hDK)
    (Real.rpow_nonneg hγ.le (-holderRateExponent ν))
  rw [←curvatureHolderThreshold_scale hγ] at hB
  apply endpoint_half_sum_polylog ha.le (div_nonneg hc.le (sq_nonneg K)) hj
    (by positivity) (Real.rpow_nonneg hγ.le (-holderRateExponent ν)) _ hB
  rw [firstOrderEndpointThreshold_scale]
  exact le_of_eq (by dsimp only [a]; ring)

theorem richEndpoint_half_sum_rate (P : Parameters) {σ₀ ε γ : ℝ}
    (hσ₀ : 0<σ₀) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1) :
    richMinimaxLowerCoefficient P σ₀/(toleranceLog ε γ)^2*holderEndpointRate 1 ε γ≤
      (firstOrderEndpointThreshold P.gap (firstOrderNoiseBudget P σ₀) ε+
        curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
          (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ) γ)/2 := by
  let a := firstOrderEndpointThreshold P.gap (firstOrderNoiseBudget P σ₀) 1
  let c := curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P) 1 1
  let K := curvatureBlockLogCoefficient P.gap (2*P.hessianHolder) (curvatureNoiseBudget P) 1
  let D : ℝ := curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ
  have ha : 0<a := firstOrderEndpointThreshold_pos P.gap_pos (firstOrderNoiseBudget_pos P hσ₀) (by norm_num)
  have hc : 0<c := curvatureEndpointThreshold_pos P.gap_pos P.hessianHolder_pos
    (curvatureNoiseBudget_pos P) (by norm_num) (by norm_num)
  have hK : 0<K := curvatureBlockLogCoefficient_pos P.gap_pos.le (mul_pos (show (0:ℝ)<2 by norm_num) P.hessianHolder_pos) (by norm_num)
  have hj := one_le_toleranceLog hε hε1 hγ hγ1
  have hD : 0<D := by
    dsimp only [D]
    rw [curvatureEndpointBlockSize_holder hγ]
    have hh := (curvatureHolderBlockSize_bounds (σ := curvatureNoiseBudget P)
      P.gap_pos.le (mul_pos (show (0:ℝ)<2 by norm_num) P.hessianHolder_pos) hγ (by norm_num) (le_refl (1:ℝ))).1
    exact_mod_cast (show 0<curvatureHolderBlockSize P.gap (2*P.hessianHolder) (curvatureNoiseBudget P) γ 1 by omega)
  have hDK : D≤K*toleranceLog ε γ := curvatureEndpointBlockSize_le_toleranceLog
    P.gap_pos.le P.hessianHolder_pos hε hε1 hγ hγ1
  have hB := mul_le_mul_of_nonneg_right
    (inverse_block_sq_lower hc.le hD hK (by linarith only [hj]) hDK)
    (Real.rpow_nonneg hγ.le (-holderRateExponent 1))
  rw [←curvatureEndpointThreshold_scale hγ] at hB
  apply endpoint_half_sum_polylog ha.le (div_nonneg hc.le (sq_nonneg K)) hj
    (by positivity) (Real.rpow_nonneg hγ.le (-holderRateExponent 1)) _ hB
  rw [firstOrderEndpointThreshold_scale]
  exact le_of_eq (by dsimp only [a]; ring)

/-- The Hölder minimax lower frontier, with an explicit squared logarithm
and one positive constant depending only on the fixed model parameters. -/
theorem holderEnvelope_minimax_polylog_lower (P : Parameters) {ν κ : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (hκ : 1+2/ν<κ) :
    ∃ ε₀ γ₀ : ℝ, 0<ε₀ ∧ 0<γ₀ ∧ ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      ENNReal.ofReal (holderMinimaxLowerCoefficient P ν/(toleranceLog ε γ)^2*
        holderEndpointRate ν ε γ)≤hvpEnvelopeComplexity P ν κ ε γ := by
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hlo⟩ := holderEnvelope_minimax_lower_small P hν hν1 hκ
  refine ⟨min ε₀ 1,min γ₀ 1,lt_min hε₀ (by norm_num),lt_min hγ₀ (by norm_num),?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  exact (ENNReal.ofReal_le_ofReal (holderEndpoint_half_sum_rate P hν hν1 hε
    (hεsmall.trans (min_le_right _ _)) hγ (hγsmall.trans (min_le_right _ _)))).trans
      (hlo ε γ hε (hεsmall.trans (min_le_left _ _)) hγ (hγsmall.trans (min_le_left _ _)))

/-- The rich-response minimax lower frontier includes all value, gradient
and Hessian entries and has the same tolerance exponents. -/
theorem richEnvelope_minimax_polylog_lower (P : Parameters) {σ₀ κ : ℝ}
    (hσ₀ : 0<σ₀) (hκ : 3<κ) :
    ∃ ε₀ γ₀ : ℝ, 0<ε₀ ∧ 0<γ₀ ∧ ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      ENNReal.ofReal (richMinimaxLowerCoefficient P σ₀/(toleranceLog ε γ)^2*
        (1/ε^3+1/γ^5))≤richEnvelopeComplexity P σ₀ κ ε γ := by
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hlo⟩ := richEnvelope_minimax_lower_small P hσ₀ hκ
  refine ⟨min ε₀ 1,min γ₀ 1,lt_min hε₀ (by norm_num),lt_min hγ₀ (by norm_num),?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  rw [←holderEndpointRate_lipschitz ε hγ.le]
  exact (ENNReal.ofReal_le_ofReal (richEndpoint_half_sum_rate P hσ₀ hε
    (hεsmall.trans (min_le_right _ _)) hγ (hγsmall.trans (min_le_right _ _)))).trans
      (hlo ε γ hε (hεsmall.trans (min_le_left _ _)) hγ (hγsmall.trans (min_le_left _ _)))

theorem lipschitzEnvelope_minimax_polylog_lower (P : Parameters) {κ : ℝ} (hκ : 3<κ) :
    ∃ ε₀ γ₀ : ℝ, 0<ε₀ ∧ 0<γ₀ ∧ ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      ENNReal.ofReal (holderMinimaxLowerCoefficient P 1/(toleranceLog ε γ)^2*
        (1/ε^3+1/γ^5))≤hvpEnvelopeComplexity P 1 κ ε γ := by
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hlo⟩ := holderEnvelope_minimax_polylog_lower P
    (show (0:ℝ)<1 by norm_num) (le_refl (1:ℝ)) (show 1+2/(1:ℝ)<κ by norm_num; exact hκ)
  refine ⟨ε₀,γ₀,hε₀,hγ₀,?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  simpa only [holderEndpointRate_lipschitz ε hγ.le] using hlo ε γ hε hεsmall hγ hγsmall

end
end SecondOrder
