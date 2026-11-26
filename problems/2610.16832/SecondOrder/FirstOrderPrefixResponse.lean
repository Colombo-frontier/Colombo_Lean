import SecondOrder.FirstOrderPrefixSampling

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T k : ℕ}

/-- The response law for an arbitrary product of coefficient-array laws,
with every unused array marginalized out. -/
theorem scaledFirstOrderTruncatedReply_product_law (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ)
    (p : Fin (T+1) → PMF (Fin d → SignedCoefficient R))
    (hk : k≤T) (x : Point (FirstOrderDimension d T)) :
    (finitePiPMF p).toMeasure.map (fun z => scaledFirstOrderTruncatedReply Θ A β z k x) =
      ((finitePiPMF (fun i : Fin k => p ⟨i.val,by omega⟩)).toMeasure.prod
        (p ⟨k,by omega⟩).toMeasure).map
        (scaledFirstOrderFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β x) := by
  let π : FirstOrderCoefficients d T R →
      FirstOrderPastCoefficients d k R × (Fin d → SignedCoefficient R) :=
    fun z => ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩)
  let pastΘ : Fin k → (Fin d → Bool) := fun i => Θ ⟨i.val,by omega⟩
  have he : (fun z : FirstOrderCoefficients d T R => scaledFirstOrderTruncatedReply Θ A β z k x) =
      scaledFirstOrderFrontierReply θ₀ pastΘ A β x ∘ π :=
    funext (fun z => scaledFirstOrderTruncatedReply_frontier_map Θ θ₀ A β z hk x)
  rw [he, ←Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hmarg := finitePiPMF_prefix_next p (show k<T+1 by omega)
  change (finitePiPMF p).toMeasure.map π =
    (finitePiPMF (fun i : Fin k => p ⟨i.val,by omega⟩)).toMeasure.prod
      (p ⟨k,by omega⟩).toMeasure at hmarg
  rw [hmarg]

theorem firstOrderPrefixCoefficientLaw_true_response (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (hk : k≤T)
    (x : Point (FirstOrderDimension d T)) :
    (firstOrderPrefixCoefficientLaw Θ R hR (k+1)).toMeasure.map
      (fun z => scaledFirstOrderTruncatedReply Θ A β z k x) =
      scaledFirstOrderFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) A β R hR x := by
  unfold firstOrderPrefixCoefficientLaw
  rw [scaledFirstOrderTruncatedReply_product_law Θ θ₀ A β R _ hk x]
  have hp : (fun i : Fin k => firstOrderPrefixArray Θ R hR (k+1) ⟨i.val,by omega⟩) =
      (fun i : Fin k => firstOrderCoefficientLaw (Θ ⟨i.val,by omega⟩) R hR) := by
    funext i
    simp only [firstOrderPrefixArray, if_pos (show i.val<k+1 by omega)]
  rw [hp]
  simp only [firstOrderPrefixArray, if_pos (show k<k+1 by omega)]
  rfl

/-- Fair filling of the unused future is invisible to the actual extended
value/gradient/Hessian response, at every query point. -/
theorem firstOrderPrefixCoefficientLaw_extended_response (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (hk : k≤T)
    (x : Point (FirstOrderDimension d T)) :
    (firstOrderPrefixCoefficientLaw Θ R hR (k+1)).toMeasure.map
      (fun z => scaledFirstOrderTruncatedReply Θ A β z k x) =
      scaledFirstOrderExtendedKernel Θ A β R hR k x := by
  rw [firstOrderPrefixCoefficientLaw_true_response Θ θ₀ A β R hR hk x]
  exact (scaledFirstOrderTruncatedReply_law_frontier Θ θ₀ A β R hR hk x).symm

theorem firstOrderPrefixCoefficientLaw_reference_response (Θ : Fin (T+1) → (Fin d → Bool))
    (θ₀ : (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (hk : k≤T)
    (x : Point (FirstOrderDimension d T)) :
    (firstOrderPrefixCoefficientLaw Θ R hR k).toMeasure.map
      (fun z => scaledFirstOrderTruncatedReply Θ A β z k x) =
      scaledFirstOrderReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β R hR x := by
  unfold firstOrderPrefixCoefficientLaw
  rw [scaledFirstOrderTruncatedReply_product_law Θ θ₀ A β R _ hk x]
  have hp : (fun i : Fin k => firstOrderPrefixArray Θ R hR k ⟨i.val,by omega⟩) =
      (fun i : Fin k => firstOrderCoefficientLaw (Θ ⟨i.val,by omega⟩) R hR) := by
    funext i
    simp only [firstOrderPrefixArray, if_pos i.isLt]
  rw [hp]
  simp only [firstOrderPrefixArray, lt_self_iff_false, if_false]
  rfl

theorem firstOrderPrefixCoefficientLaw_full (Θ : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) : firstOrderPrefixCoefficientLaw Θ R hR (T+1)=firstOrderChainCoefficientLaw Θ R hR := by
  unfold firstOrderPrefixCoefficientLaw firstOrderChainCoefficientLaw
  congr 1
  funext i
  simp only [firstOrderPrefixArray, if_pos i.isLt]

end
end SecondOrder

