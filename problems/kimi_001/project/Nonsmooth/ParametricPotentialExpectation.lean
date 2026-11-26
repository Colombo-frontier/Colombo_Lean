import Nonsmooth.ParametricPotentialMoment

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def potentialPartition (V : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (-V t x)

def potentialExpectation (V F : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, F t x ∂realDensityLaw (fun x => Real.exp (-V t x))

theorem potentialExpectation_eq_ratio (V F : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : Measurable (V t)) (hi : Integrable (fun x => Real.exp (-V t x))) :
    potentialExpectation V F t = potentialWeightedIntegral V F t / potentialPartition V t :=
  realDensityLaw_integral _ (Real.continuous_exp.measurable.comp hV.neg) hi
    (fun _ => (Real.exp_pos _).le) (F t)

theorem potentialPartition_derivative (V s : ℝ → ℝ → ℝ) (t : ℝ)
    (hreg : PotentialMomentRegularAt V s (fun _ _ => 1) (fun _ _ => 0) t) :
    HasDerivAt (potentialPartition V) (-potentialWeightedIntegral V s t) t := by
  have hd := (potentialWeightedIntegral_derivative V s (fun _ _ => 1) (fun _ _ => 0) t hreg).2
  have hfun : potentialWeightedIntegral V (fun _ _ => 1) = potentialPartition V := by
    funext r
    simp only [potentialPartition, potentialWeightedIntegral, one_mul]
  rw [hfun] at hd
  simpa only [potentialWeightedIntegral, one_mul, zero_sub, neg_mul, integral_neg] using hd

/-- The derivative of the actual normalized expectation, justified by the
dominated moment hypotheses for both numerator and partition function. -/
theorem potentialExpectation_derivative (V s F F' : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : ∀ r, Measurable (V r)) (hi : ∀ r, Integrable (fun x => Real.exp (-V r x)))
    (hnum : PotentialMomentRegularAt V s F F' t)
    (hden : PotentialMomentRegularAt V s (fun _ _ => 1) (fun _ _ => 0) t) :
    HasDerivAt (potentialExpectation V F)
      (potentialExpectation V (fun r x => F' r x - F r x * s r x) t +
        potentialExpectation V F t * potentialExpectation V s t) t := by
  have hN := (potentialWeightedIntegral_derivative V s F F' t hnum).2
  have hD := potentialPartition_derivative V s t hden
  have hZ : potentialPartition V t ≠ 0 := (integral_exp_pos (hi t)).ne'
  have hquot := hN.div hD hZ
  convert! hquot using 1
  · funext r
    exact potentialExpectation_eq_ratio V F r (hV r) (hi r)
  · rw [potentialExpectation_eq_ratio V (fun r x => F' r x - F r x * s r x) t (hV t) (hi t),
      potentialExpectation_eq_ratio V F t (hV t) (hi t),
      potentialExpectation_eq_ratio V s t (hV t) (hi t)]
    dsimp only [potentialWeightedIntegral]
    field_simp [hZ]
    ring

theorem potentialNegativeLogPartition_derivative (V s : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : Measurable (V t)) (hi : Integrable (fun x => Real.exp (-V t x)))
    (hden : PotentialMomentRegularAt V s (fun _ _ => 1) (fun _ _ => 0) t) :
    HasDerivAt (fun r => -Real.log (potentialPartition V r)) (potentialExpectation V s t) t := by
  have hZ : potentialPartition V t ≠ 0 := (integral_exp_pos hi).ne'
  have hd := ((potentialPartition_derivative V s t hden).log hZ).neg
  convert! hd using 1
  rw [potentialExpectation_eq_ratio V s t hV hi]
  ring

end
end Nonsmooth
