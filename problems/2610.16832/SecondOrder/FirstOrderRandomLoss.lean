import SecondOrder.ConservativeSelector
import SecondOrder.FirstOrderGeometry
import SecondOrder.ScalarJetAlgebra

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

abbrev FirstOrderCoefficients (d T : ℕ) (R : ℝ) :=
  Fin (T+1) → Fin d → SignedCoefficient R

def firstOrderChainCoefficientLaw (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2 ≤ R) :
    PMF (FirstOrderCoefficients d T R) :=
  finitePiPMF (fun i => firstOrderCoefficientLaw (Θ i) R hR)

def firstOrderPayloadScale (j : ℕ) : ℝ := if j=0 then 1 else 2

/-- Payload zero is the first block error, later payloads are twice the next
block error, and the terminal payload is zero. The terminal gate is retained. -/
def firstOrderNoisePayload (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (j : ℕ) (x : FirstOrderSpace d T) : ℝ :=
  if hj : j<T+1 then firstOrderPayloadScale j *
    firstOrderBlockNoise (Θ ⟨j,hj⟩) (z ⟨j,hj⟩) (x ⟨j,hj⟩) else 0

def firstOrderChainNoise (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) : FirstOrderSpace d T → ℝ :=
  reverseBlockSelector (fun i => firstOrderBlockCompletion (Θ i)) (firstOrderNoisePayload Θ z)

def firstOrderRandomLoss (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) : FirstOrderSpace d T → ℝ :=
  conservativeSelectorLoss (firstOrderChain Θ) (fun i => firstOrderBlockCompletion (Θ i))
    (firstOrderNoisePayload Θ) z

theorem firstOrderNoisePayload_contDiff (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (j : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (firstOrderNoisePayload Θ z j) := by
  by_cases hj : j<T+1
  · change ContDiff ℝ k (fun x => if _ : j<T+1 then _ else _)
    simp only [dif_pos hj]
    exact contDiff_const.mul ((firstOrderBlockNoise_contDiff (Θ ⟨j,hj⟩) (z ⟨j,hj⟩) k).comp
      (blockProj (E := Point d) (⟨j,hj⟩ : Fin (T+1))).contDiff)
  · have he : firstOrderNoisePayload Θ z j = fun _ => (0:ℝ) := by
      funext x
      simp only [firstOrderNoisePayload, dif_neg hj]
    rw [he]
    exact contDiff_const

theorem firstOrderChainNoise_contDiff (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) : ContDiff ℝ 3 (firstOrderChainNoise Θ z) :=
  reverseBlockSelector_contDiff _ _ (fun i => firstOrderBlockCompletion_contDiff (Θ i))
    (fun j _ => firstOrderNoisePayload_contDiff Θ z j 3)

theorem firstOrderRandomLoss_contDiff (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) : ContDiff ℝ 3 (firstOrderRandomLoss Θ z) :=
  (firstOrderChain_contDiff Θ).add (firstOrderChainNoise_contDiff Θ z)

theorem firstOrderNoisePayload_mean (Θ : Fin (T+1) → (Fin d → Bool)) (hd : 0 < d)
    (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (x : FirstOrderSpace d T) :
    pmfMean (firstOrderChainCoefficientLaw Θ R hR) (fun z => firstOrderNoisePayload Θ z j x) = 0 := by
  by_cases hj : j<T+1
  · simp only [firstOrderNoisePayload, dif_pos hj, pmfMean_mul, firstOrderChainCoefficientLaw]
    have hc := finitePiPMF_coordinate_mean (fun i : Fin (T+1) => firstOrderCoefficientLaw (Θ i) R hR) (⟨j,hj⟩ : Fin (T+1))
      (fun zi => firstOrderBlockNoise (Θ ⟨j,hj⟩) zi (x ⟨j,hj⟩))
    have hh := (firstOrderBlockNoise_zero_means (Θ ⟨j,hj⟩) R hR (x ⟨j,hj⟩)).1
    have hz : pmfMean (firstOrderCoefficientLaw (Θ ⟨j,hj⟩) R hR)
        (fun zi => firstOrderBlockNoise (Θ ⟨j,hj⟩) zi (x ⟨j,hj⟩)) = 0 := by
      simpa only [PMF.integral_eq_sum, pmfMean] using hh
    rw [hz] at hc
    apply mul_eq_zero_of_right
    unfold pmfMean at hc ⊢
    refine Eq.trans ?_ hc
    apply Finset.sum_congr (by ext w; simp)
    intro w _
    rfl
  · simp only [firstOrderNoisePayload, dif_neg hj, pmfMean_const]

/-- Actual independent coefficient arrays give exact unbiased rich derivatives. -/
theorem firstOrderRandomLoss_unbiased (Θ : Fin (T+1) → (Fin d → Bool)) (hd : 0 < d)
    (R : ℝ) (hR : 2 ≤ R) (x : FirstOrderSpace d T) :
    (∫ z, firstOrderRandomLoss Θ z x ∂(firstOrderChainCoefficientLaw Θ R hR).toMeasure) = firstOrderChain Θ x ∧
    (∫ z, gradient (firstOrderRandomLoss Θ z) x ∂(firstOrderChainCoefficientLaw Θ R hR).toMeasure) = gradient (firstOrderChain Θ) x ∧
    (∫ z, fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) x ∂(firstOrderChainCoefficientLaw Θ R hR).toMeasure) =
      fderiv ℝ (gradient (firstOrderChain Θ)) x := by
  exact conservativeSelectorLoss_unbiased (firstOrderChainCoefficientLaw Θ R hR) (firstOrderChain Θ)
    (fun i => firstOrderBlockCompletion (Θ i)) (firstOrderNoisePayload Θ)
    ((firstOrderChain_contDiff Θ).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))
    (fun i => (firstOrderBlockCompletion_contDiff (Θ i)).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))
    (fun z j _ => firstOrderNoisePayload_contDiff Θ z j 2)
    (fun y j _ => firstOrderNoisePayload_mean Θ hd R hR j y) x

end
end SecondOrder

