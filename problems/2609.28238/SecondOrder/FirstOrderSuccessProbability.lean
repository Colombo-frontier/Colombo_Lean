import SecondOrder.FirstOrderComparisonLawTransport

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderOriginalOutput (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) : Point (FirstOrderDimension d T) :=
  P.query n (queryPolicyRun P (fun x a => richReply (scaledFirstOrderSample Θ A β) a x)
    (finiteHistoryTape a₀ n h) n)

theorem firstOrderComparison_completion_mean_transport (P : FirstOrderPolicy d T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    pmfMean (firstOrderOriginalJointLaw d T R hR n)
      (fun w => if firstOrderComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1 then (1:ℝ) else 0)=
    pmfMean (firstOrderComparisonJointLaw P A β R hR a₀ n)
      (fun w => if firstOrderComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1 then (1:ℝ) else 0) :=
  firstOrderComparison_joint_mean_transport P A β R hR a₀ n
    (fun Θ s => if max s.2.1 (firstOrderLimitedProgress Θ β (P.query n s.2.2) (s.2.1+1))=T+1 then 1 else 0)

/-- Success under the true full-array oracle is bounded by completion under
the fair-filled comparison law plus the explicit far-jump error. -/
theorem firstOrderOriginal_success_probability (P : FirstOrderPolicy d T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (success : (Fin (T+1) → (Fin d → Bool)) → Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x)=T+1) :
    pmfEventProbability (firstOrderOriginalJointLaw d T R hR n)
      (fun w => decide (success w.1 (firstOrderOriginalOutput P w.1 A β a₀ n w.2)))≤
    pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (firstOrderComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1))+
      (n+1:ℕ)*((T+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))) := by
  rw [pmfEventProbability_mean, pmfEventProbability_mean]
  simp only [decide_eq_true_eq]
  have hpoint (w : (Fin (T+1) → (Fin d → Bool)) × FiniteHistory Unit (FirstOrderCoefficients d T R) n) :
      (if success w.1 (firstOrderOriginalOutput P w.1 A β a₀ n w.2) then (1:ℝ) else 0)≤
      (if firstOrderComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1 then (1:ℝ) else 0)+
      (if firstOrderHistoryFar P w.1 A β a₀ n w.2 then (1:ℝ) else 0) := by
    by_cases hs : success w.1 (firstOrderOriginalOutput P w.1 A β a₀ n w.2)
    · have ht := firstOrderComparison_success_transfer P w.1 A β (finiteHistoryTape a₀ n w.2) n
        (success w.1) (hcomplete w.1) hs
      rw [if_pos hs]
      rcases ht with ht | ht
      · rw [if_pos ((firstOrderHistoryFar_noFarJump P w.1 A β a₀ n w.2).mpr ht)]
        split_ifs <;> norm_num
      · rw [if_pos ht]
        split_ifs <;> norm_num
    · rw [if_neg hs]
      split_ifs <;> norm_num
  apply (pmfMean_mono _ hpoint).trans
  rw [pmfMean_add, firstOrderComparison_completion_mean_transport]
  have hh := firstOrderOriginal_far_probability P A β R hR a₀ n
  rw [pmfEventProbability_mean] at hh
  simp only [decide_eq_true_eq] at hh
  exact add_le_add_left hh _

end
end SecondOrder

