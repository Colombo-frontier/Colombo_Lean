import SecondOrder.FiniteObservableTransport

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvaturePrefixCoefficientLaw_full_of_le (Θ : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (k : ℕ) (hk : T+1≤k) :
    curvaturePrefixCoefficientLaw Θ R hR k=curvatureCoefficientLaw Θ R hR := by
  unfold curvaturePrefixCoefficientLaw curvatureCoefficientLaw
  congr 1
  funext i
  simp only [curvaturePrefixArray, if_pos (show i.val<k by omega)]

/-- Future fair filling preserves arbitrary tests of the actual complete
truncated reply, including at the terminal index. -/
theorem curvatureTruncatedReply_mean_transport (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (k : ℕ) (x : Point (CurvatureDimension m T))
    (F : RichReply (CurvatureDimension m T) → ℝ) :
    pmfMean (curvatureCoefficientLaw Θ R hR) (fun z => F (scaledCurvatureTruncatedReply Θ A β z k x))=
      pmfMean (curvaturePrefixCoefficientLaw Θ R hR (k+1))
        (fun z => F (scaledCurvatureTruncatedReply Θ A β z k x)) := by
  by_cases hk : k≤T
  · apply pmfMean_comp_eq_of_measure_map_eq _ _ _ _ F
    exact (curvaturePrefixCoefficientLaw_extended_response Θ (Θ 0) A β R hR hk x).symm
  · rw [curvaturePrefixCoefficientLaw_full_of_le Θ R hR (k+1) (by omega)]

theorem curvatureComparisonStep_mean_transport (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (n : ℕ) (s : ℕ × S) (F : (ℕ × S) → ℝ) :
    pmfMean (curvatureCoefficientLaw Θ R hR) (fun z => F (curvatureComparisonStep P Θ A β n s z))=
      pmfMean (curvaturePrefixCoefficientLaw Θ R hR (curvatureLimitedProgress Θ β (P.query n s.2) (s.1+1)+1))
        (fun z => F (curvatureComparisonStep P Θ A β n s z)) := by
  exact curvatureTruncatedReply_mean_transport Θ A β R hR
    (curvatureLimitedProgress Θ β (P.query n s.2) (s.1+1)) (P.query n s.2)
    (fun y => F (max s.1 (curvatureLimitedProgress Θ β (P.query n s.2) (s.1+1)),P.update n s.2 y))

end
end SecondOrder
