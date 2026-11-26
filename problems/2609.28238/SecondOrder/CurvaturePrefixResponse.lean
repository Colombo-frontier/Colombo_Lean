import SecondOrder.CurvaturePrefixSampling

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T k : ℕ}

/-- The response law for an arbitrary product of coefficient-array laws,
with every unused array marginalized out. -/
theorem scaledCurvatureTruncatedReply_product_law (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ)
    (p : Fin (T+1) → PMF (UpperPair (2*m) → SignedCoefficient R))
    (hk : k≤T) (x : Point (CurvatureDimension m T)) :
    (finitePiPMF p).toMeasure.map (fun z => scaledCurvatureTruncatedReply Θ A β z k x) =
      ((finitePiPMF (fun i : Fin k => p ⟨i.val,by omega⟩)).toMeasure.prod
        (p ⟨k,by omega⟩).toMeasure).map
        (scaledCurvatureFrontierReply θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β x) := by
  let π : CurvatureCoefficients m T R →
      CurvaturePastCoefficients m k R × (UpperPair (2*m) → SignedCoefficient R) :=
    fun z => ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩)
  let pastΘ : Fin k → BalancedVector m := fun i => Θ ⟨i.val,by omega⟩
  have he : (fun z : CurvatureCoefficients m T R => scaledCurvatureTruncatedReply Θ A β z k x) =
      scaledCurvatureFrontierReply θ₀ pastΘ A β x ∘ π :=
    funext (fun z => scaledCurvatureTruncatedReply_frontier_map Θ θ₀ A β z hk x)
  rw [he, ←Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hmarg := finitePiPMF_prefix_next p (show k<T+1 by omega)
  change (finitePiPMF p).toMeasure.map π =
    (finitePiPMF (fun i : Fin k => p ⟨i.val,by omega⟩)).toMeasure.prod
      (p ⟨k,by omega⟩).toMeasure at hmarg
  rw [hmarg]

theorem curvaturePrefixCoefficientLaw_true_response (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (hk : k≤T)
    (x : Point (CurvatureDimension m T)) :
    (curvaturePrefixCoefficientLaw Θ R hR (k+1)).toMeasure.map
      (fun z => scaledCurvatureTruncatedReply Θ A β z k x) =
      scaledCurvatureFrontierTrueLaw θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩)
        (Θ ⟨k,by omega⟩) A β R hR x := by
  unfold curvaturePrefixCoefficientLaw
  rw [scaledCurvatureTruncatedReply_product_law Θ θ₀ A β R _ hk x]
  have hp : (fun i : Fin k => curvaturePrefixArray Θ R hR (k+1) ⟨i.val,by omega⟩) =
      (fun i : Fin k => periodicCoefficientLaw (Θ ⟨i.val,by omega⟩).1 R hR) := by
    funext i
    simp only [curvaturePrefixArray, if_pos (show i.val<k+1 by omega)]
  rw [hp]
  simp only [curvaturePrefixArray, if_pos (show k<k+1 by omega)]
  rfl

/-- Fair filling of the unused future is invisible to the actual extended
value/gradient/Hessian response, at every query point. -/
theorem curvaturePrefixCoefficientLaw_extended_response (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (hk : k≤T)
    (x : Point (CurvatureDimension m T)) :
    (curvaturePrefixCoefficientLaw Θ R hR (k+1)).toMeasure.map
      (fun z => scaledCurvatureTruncatedReply Θ A β z k x) =
      scaledCurvatureExtendedKernel Θ A β R hR k x := by
  rw [curvaturePrefixCoefficientLaw_true_response Θ θ₀ A β R hR hk x]
  exact (scaledCurvatureTruncatedReply_law_frontier Θ θ₀ A β R hR hk x).symm

theorem curvaturePrefixCoefficientLaw_reference_response (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (A β R : ℝ) (hR : 2≤R) (hk : k≤T)
    (x : Point (CurvatureDimension m T)) :
    (curvaturePrefixCoefficientLaw Θ R hR k).toMeasure.map
      (fun z => scaledCurvatureTruncatedReply Θ A β z k x) =
      scaledCurvatureReferenceKernel θ₀ (fun i : Fin k => Θ ⟨i.val,by omega⟩) A β R hR x := by
  unfold curvaturePrefixCoefficientLaw
  rw [scaledCurvatureTruncatedReply_product_law Θ θ₀ A β R _ hk x]
  have hp : (fun i : Fin k => curvaturePrefixArray Θ R hR k ⟨i.val,by omega⟩) =
      (fun i : Fin k => periodicCoefficientLaw (Θ ⟨i.val,by omega⟩).1 R hR) := by
    funext i
    simp only [curvaturePrefixArray, if_pos i.isLt]
  rw [hp]
  simp only [curvaturePrefixArray, lt_self_iff_false, if_false]
  rfl

theorem curvaturePrefixCoefficientLaw_full (Θ : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) : curvaturePrefixCoefficientLaw Θ R hR (T+1)=curvatureCoefficientLaw Θ R hR := by
  unfold curvaturePrefixCoefficientLaw curvatureCoefficientLaw
  congr 1
  funext i
  simp only [curvaturePrefixArray, if_pos i.isLt]

end
end SecondOrder
