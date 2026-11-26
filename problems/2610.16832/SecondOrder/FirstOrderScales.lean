import SecondOrder.ScaledFirstOrderCompletion
import SecondOrder.ScaledFirstOrderInformation

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

def firstOrderOutputScale (ε : ℝ) : ℝ := 4*ε/firstOrderGradientConstant
def firstOrderCoefficientScale (s A : ℝ) : ℝ := s/(2*firstOrderNoiseConstant*A)
def firstOrderNoiseBudget (P : Parameters) (σ₀ : ℝ) : ℝ :=
  min σ₀ (min P.gradientNoise (min P.hessianNoise P.hessianBound))

theorem firstOrderOutputScale_pos {ε : ℝ} (hε : 0<ε) : 0<firstOrderOutputScale ε :=
  div_pos (by positivity) firstOrderGradientConstant_pos

theorem firstOrderOutputScale_separation (ε : ℝ) :
    firstOrderOutputScale ε*firstOrderGradientConstant=4*ε := by
  unfold firstOrderOutputScale
  exact div_mul_cancel₀ _ firstOrderGradientConstant_pos.ne'

theorem firstOrderNoiseBudget_pos (P : Parameters) {σ₀ : ℝ} (hσ₀ : 0<σ₀) :
    0<firstOrderNoiseBudget P σ₀ :=
  lt_min hσ₀ (lt_min P.gradientNoise_pos (lt_min P.hessianNoise_pos P.hessianBound_pos))

theorem firstOrderNoiseBudget_bounds (P : Parameters) (σ₀ : ℝ) :
    firstOrderNoiseBudget P σ₀≤σ₀ ∧ firstOrderNoiseBudget P σ₀≤P.gradientNoise ∧
    firstOrderNoiseBudget P σ₀≤min P.hessianNoise P.hessianBound :=
  ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

theorem firstOrderCoefficientScale_ge_two {s A : ℝ} (hA : 0<A)
    (hsmall : 4*firstOrderNoiseConstant*A≤s) : 2≤firstOrderCoefficientScale s A := by
  have hC := firstOrderNoiseConstant_pos
  apply (le_div_iff₀ (by positivity : 0<2*firstOrderNoiseConstant*A)).2
  nlinarith only [hsmall]

theorem firstOrderScales_noise {s A : ℝ} (hA : 0<A)
    (hsmall : 4*firstOrderNoiseConstant*A≤s) :
    A*(firstOrderNoiseConstant*(firstOrderCoefficientScale s A+1))≤s := by
  have hC := firstOrderNoiseConstant_pos
  have he : A*(firstOrderNoiseConstant*(firstOrderCoefficientScale s A+1))=s/2+firstOrderNoiseConstant*A := by
    unfold firstOrderCoefficientScale
    field_simp
    <;> ring
  rw [he]
  nlinarith [mul_pos hC hA]

theorem firstOrderScales_information (D s A : ℝ) :
    D/(firstOrderCoefficientScale s A)^2=4*firstOrderNoiseConstant^2*D*A^2/s^2 := by
  simp only [firstOrderCoefficientScale,div_pow,div_div_eq_mul_div]
  ring

/-- The manuscript's A=4 epsilon/c0 and bounded coefficient noise give a
genuine rich common loss under explicit gap and smoothness inequalities. -/
theorem firstOrderHardFamily_admissible {d T : ℕ} (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) (P : Parameters) {σ₀ ε : ℝ} (hσ₀ : 0<σ₀) (hε : 0<ε)
    (hsmall : 4*firstOrderNoiseConstant*firstOrderOutputScale ε≤firstOrderNoiseBudget P σ₀)
    (hgap : 20*firstOrderOutputScale ε*(T+1:ℕ)≤P.gap)
    (hLip : firstOrderOutputScale ε*firstOrderGeometryConstant≤P.gradientLip)
    (hHolder : firstOrderOutputScale ε*(firstOrderGeometryConstant*Real.sqrt d)≤P.hessianHolder) :
    RichCommonLoss (firstOrderChainCoefficientLaw Θ
      (firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) (firstOrderOutputScale ε))
      (firstOrderCoefficientScale_ge_two (firstOrderOutputScale_pos hε) hsmall)).toMeasure P σ₀
      (scaledFirstOrderPopulation Θ (firstOrderOutputScale ε) 1)
      (scaledFirstOrderSample Θ (firstOrderOutputScale ε) 1) := by
  have hA := firstOrderOutputScale_pos hε
  have hn := firstOrderScales_noise hA hsmall
  have hb := firstOrderNoiseBudget_bounds P σ₀
  apply scaledFirstOrderRichCommonLoss Θ hd P hA.le (by norm_num) hσ₀ _ _ hgap
  · simpa only [one_pow,mul_one] using hLip
  · simpa only [one_pow,mul_one] using hHolder
  · exact hn.trans hb.1
  · simpa only [mul_one] using hn.trans hb.2.1
  · simpa only [one_pow,mul_one] using hn.trans hb.2.2

theorem firstOrderHardFamily_gradient_progress {d T : ℕ} (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {ε : ℝ} (hε : 0<ε) {x : Point (FirstOrderDimension d T)}
    (hx : ‖gradient (scaledFirstOrderPopulation Θ (firstOrderOutputScale ε) 1) x‖≤ε) :
    firstOrderProgress Θ (firstOrderDilation d T 1 x)=T+1 := by
  apply scaledFirstOrderPopulation_gradient_progress Θ hd (firstOrderOutputScale_pos hε).le (by norm_num) _ hx
  rw [mul_one,firstOrderOutputScale_separation]
  linarith

end
end SecondOrder
