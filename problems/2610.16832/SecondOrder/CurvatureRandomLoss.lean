import SecondOrder.ConservativeSelector
import SecondOrder.CurvatureChain
import SecondOrder.ScalarJetAlgebra

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

abbrev CurvatureCoefficients (m T : ℕ) (R : ℝ) :=
  Fin (T+1) → UpperPair (2*m) → SignedCoefficient R

def curvatureCoefficientLaw (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2 ≤ R) :
    PMF (CurvatureCoefficients m T R) :=
  finitePiPMF (fun i => periodicCoefficientLaw (Θ i).1 R hR)

def curvaturePayloadScale (j : ℕ) : ℝ := if j=0 then 1 else 2

/-- Payload zero is the first block error, later payloads are twice the next
block error, and the terminal payload is zero. The terminal gate is retained. -/
def curvatureNoisePayload (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (j : ℕ) (x : CurvatureSpace m T) : ℝ :=
  if hj : j<T+1 then curvaturePayloadScale j *
    periodicBlockNoise (Θ ⟨j,hj⟩) (z ⟨j,hj⟩) (x ⟨j,hj⟩) else 0

def curvatureChainNoise (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) : CurvatureSpace m T → ℝ :=
  reverseBlockSelector (fun i => periodicCompletion (Θ i)) (curvatureNoisePayload Θ z)

def curvatureRandomLoss (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) : CurvatureSpace m T → ℝ :=
  conservativeSelectorLoss (curvatureChain Θ) (fun i => periodicCompletion (Θ i))
    (curvatureNoisePayload Θ) z

theorem curvatureNoisePayload_contDiff (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (j : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (curvatureNoisePayload Θ z j) := by
  by_cases hj : j<T+1
  · change ContDiff ℝ k (fun x => if _ : j<T+1 then _ else _)
    simp only [dif_pos hj]
    exact contDiff_const.mul ((periodicBlockNoise_contDiff (Θ ⟨j,hj⟩) (z ⟨j,hj⟩) k).comp
      (blockProj (E := Point (2*m)) (⟨j,hj⟩ : Fin (T+1))).contDiff)
  · have he : curvatureNoisePayload Θ z j = fun _ => (0:ℝ) := by
      funext x
      simp only [curvatureNoisePayload, dif_neg hj]
    rw [he]
    exact contDiff_const

theorem curvatureChainNoise_contDiff (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) : ContDiff ℝ 3 (curvatureChainNoise Θ z) :=
  reverseBlockSelector_contDiff _ _ (fun i => periodicCompletion_contDiff (Θ i))
    (fun j _ => curvatureNoisePayload_contDiff Θ z j 3)

theorem curvatureRandomLoss_contDiff (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) : ContDiff ℝ 3 (curvatureRandomLoss Θ z) :=
  (curvatureChain_contDiff Θ).add (curvatureChainNoise_contDiff Θ z)

theorem curvatureNoisePayload_mean (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (x : CurvatureSpace m T) :
    pmfMean (curvatureCoefficientLaw Θ R hR) (fun z => curvatureNoisePayload Θ z j x) = 0 := by
  by_cases hj : j<T+1
  · simp only [curvatureNoisePayload, dif_pos hj, pmfMean_mul, curvatureCoefficientLaw]
    have hc := finitePiPMF_coordinate_mean (fun i : Fin (T+1) => periodicCoefficientLaw (Θ i).1 R hR) (⟨j,hj⟩ : Fin (T+1))
      (fun zi => periodicBlockNoise (Θ ⟨j,hj⟩) zi (x ⟨j,hj⟩))
    have hh := (periodicBlockNoise_zero_means (Θ ⟨j,hj⟩) hm R hR (x ⟨j,hj⟩)).1
    have hz : pmfMean (periodicCoefficientLaw (Θ ⟨j,hj⟩).1 R hR)
        (fun zi => periodicBlockNoise (Θ ⟨j,hj⟩) zi (x ⟨j,hj⟩)) = 0 := by
      simpa only [PMF.integral_eq_sum, pmfMean] using hh
    rw [hz] at hc
    apply mul_eq_zero_of_right
    unfold pmfMean at hc ⊢
    refine Eq.trans ?_ hc
    apply Finset.sum_congr (by ext w; simp)
    intro w _
    rfl
  · simp only [curvatureNoisePayload, dif_neg hj, pmfMean_const]

/-- Actual independent coefficient arrays give exact unbiased rich derivatives. -/
theorem curvatureRandomLoss_unbiased (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (x : CurvatureSpace m T) :
    (∫ z, curvatureRandomLoss Θ z x ∂(curvatureCoefficientLaw Θ R hR).toMeasure) = curvatureChain Θ x ∧
    (∫ z, gradient (curvatureRandomLoss Θ z) x ∂(curvatureCoefficientLaw Θ R hR).toMeasure) = gradient (curvatureChain Θ) x ∧
    (∫ z, fderiv ℝ (gradient (curvatureRandomLoss Θ z)) x ∂(curvatureCoefficientLaw Θ R hR).toMeasure) =
      fderiv ℝ (gradient (curvatureChain Θ)) x := by
  exact conservativeSelectorLoss_unbiased (curvatureCoefficientLaw Θ R hR) (curvatureChain Θ)
    (fun i => periodicCompletion (Θ i)) (curvatureNoisePayload Θ)
    ((curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))
    (fun i => (periodicCompletion_contDiff (Θ i)).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))
    (fun z j _ => curvatureNoisePayload_contDiff Θ z j 2)
    (fun y j _ => curvatureNoisePayload_mean Θ hm R hR j y) x

end
end SecondOrder
