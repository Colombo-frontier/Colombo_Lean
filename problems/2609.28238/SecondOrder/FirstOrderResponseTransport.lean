import SecondOrder.FirstOrderComparisonFarHistory
import SecondOrder.FiniteObservableTransport

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderPrefixCoefficientLaw_full_of_le (Θ : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (k : ℕ) (hk : T+1≤k) :
    firstOrderPrefixCoefficientLaw Θ R hR k=firstOrderChainCoefficientLaw Θ R hR := by
  unfold firstOrderPrefixCoefficientLaw firstOrderChainCoefficientLaw
  congr 1
  funext i
  simp only [firstOrderPrefixArray, if_pos (show i.val<k by omega)]

/-- Future fair filling preserves arbitrary tests of the actual complete
truncated reply, including at the terminal index. -/
theorem firstOrderTruncatedReply_mean_transport (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) (k : ℕ) (x : Point (FirstOrderDimension d T))
    (F : RichReply (FirstOrderDimension d T) → ℝ) :
    pmfMean (firstOrderChainCoefficientLaw Θ R hR) (fun z => F (scaledFirstOrderTruncatedReply Θ A β z k x))=
      pmfMean (firstOrderPrefixCoefficientLaw Θ R hR (k+1))
        (fun z => F (scaledFirstOrderTruncatedReply Θ A β z k x)) := by
  by_cases hk : k≤T
  · apply pmfMean_comp_eq_of_measure_map_eq _ _ _ _ F
    exact (firstOrderPrefixCoefficientLaw_extended_response Θ (Θ 0) A β R hR hk x).symm
  · rw [firstOrderPrefixCoefficientLaw_full_of_le Θ R hR (k+1) (by omega)]

theorem firstOrderComparisonStep_mean_transport (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (n : ℕ) (s : ℕ × S) (F : (ℕ × S) → ℝ) :
    pmfMean (firstOrderChainCoefficientLaw Θ R hR) (fun z => F (firstOrderComparisonStep P Θ A β n s z))=
      pmfMean (firstOrderPrefixCoefficientLaw Θ R hR (firstOrderLimitedProgress Θ β (P.query n s.2) (s.1+1)+1))
        (fun z => F (firstOrderComparisonStep P Θ A β n s z)) := by
  exact firstOrderTruncatedReply_mean_transport Θ A β R hR
    (firstOrderLimitedProgress Θ β (P.query n s.2) (s.1+1)) (P.query n s.2)
    (fun y => F (max s.1 (firstOrderLimitedProgress Θ β (P.query n s.2) (s.1+1)),P.update n s.2 y))

end
end SecondOrder

