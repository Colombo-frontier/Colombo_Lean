import SecondOrder.ComparisonLawTransport

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

def curvatureOriginalOutput (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (a₀ : CurvatureCoefficients m T R) (n : ℕ)
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) : Point (CurvatureDimension m T) :=
  P.query n (queryPolicyRun P (fun x a => richReply (scaledCurvatureSample Θ A β) a x)
    (finiteHistoryTape a₀ n h) n)

theorem curvatureComparison_completion_mean_transport (P : CurvaturePolicy m T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    pmfMean (curvatureOriginalJointLaw m T R hR n)
      (fun w => if curvatureComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1 then (1:ℝ) else 0)=
    pmfMean (curvatureComparisonJointLaw P A β R hR a₀ n)
      (fun w => if curvatureComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1 then (1:ℝ) else 0) :=
  curvatureComparison_joint_mean_transport P A β R hR a₀ n
    (fun Θ s => if max s.2.1 (curvatureLimitedProgress Θ β (P.query n s.2.2) (s.2.1+1))=T+1 then 1 else 0)

/-- Success under the true full-array oracle is bounded by completion under
the fair-filled comparison law plus the explicit far-jump error. -/
theorem curvatureOriginal_success_probability (P : CurvaturePolicy m T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : CurvatureCoefficients m T R) (n : ℕ)
    (success : (Fin (T+1) → BalancedVector m) → Point (CurvatureDimension m T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → curvatureProgress Θ (curvatureDilation m T β x)=T+1) :
    pmfEventProbability (curvatureOriginalJointLaw m T R hR n)
      (fun w => decide (success w.1 (curvatureOriginalOutput P w.1 A β a₀ n w.2)))≤
    pmfEventProbability (curvatureComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (curvatureComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1))+
      (n+1:ℕ)*((T+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))) := by
  rw [pmfEventProbability_mean, pmfEventProbability_mean]
  simp only [decide_eq_true_eq]
  have hpoint (w : (Fin (T+1) → BalancedVector m) × FiniteHistory Unit (CurvatureCoefficients m T R) n) :
      (if success w.1 (curvatureOriginalOutput P w.1 A β a₀ n w.2) then (1:ℝ) else 0)≤
      (if curvatureComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ n w.2) n=T+1 then (1:ℝ) else 0)+
      (if curvatureHistoryFar P w.1 A β a₀ n w.2 then (1:ℝ) else 0) := by
    by_cases hs : success w.1 (curvatureOriginalOutput P w.1 A β a₀ n w.2)
    · have ht := curvatureComparison_success_transfer P w.1 A β (finiteHistoryTape a₀ n w.2) n
        (success w.1) (hcomplete w.1) hs
      rw [if_pos hs]
      rcases ht with ht | ht
      · rw [if_pos ((curvatureHistoryFar_noFarJump P w.1 A β a₀ n w.2).mpr ht)]
        split_ifs <;> norm_num
      · rw [if_pos ht]
        split_ifs <;> norm_num
    · rw [if_neg hs]
      split_ifs <;> norm_num
  apply (pmfMean_mono _ hpoint).trans
  rw [pmfMean_add, curvatureComparison_completion_mean_transport]
  have hh := curvatureOriginal_far_probability P A β R hR a₀ n
  rw [pmfEventProbability_mean] at hh
  simp only [decide_eq_true_eq] at hh
  exact add_le_add_left hh _

theorem curvatureOriginal_sosp_probability (P : CurvaturePolicy m T S)
    (hm : 0<m) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ) (R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    pmfEventProbability (curvatureOriginalJointLaw m T R hR n)
      (fun w => decide (IsSOSP (scaledCurvaturePopulation w.1 (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
        (curvatureInputScale L γ)) ε γ
        (curvatureOriginalOutput P w.1 (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ) a₀ n w.2)))≤
    pmfEventProbability (curvatureComparisonJointLaw P (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
      (curvatureInputScale L γ) R hR a₀ n)
      (fun w => decide (curvatureComparisonOutputProgress P w.1 (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
        (curvatureInputScale L γ) (finiteHistoryTape a₀ n w.2) n=T+1))+
      (n+1:ℕ)*((T+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))) :=
  curvatureOriginal_success_probability P _ _ R hR a₀ n _
    (fun Θ _ hx => curvatureHardFamily_sosp_progress Θ hm hL hγ hx)

end
end SecondOrder
