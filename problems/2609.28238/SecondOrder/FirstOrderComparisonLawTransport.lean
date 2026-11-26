import SecondOrder.FirstOrderComparisonObservedState

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- The original oracle draws a fresh full biased coefficient array on every
call. This is its actual finite sample-history distribution. -/
def firstOrderOriginalSamplingLaw (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R) (n : ℕ) :=
  finiteAdaptiveLaw (PMF.pure ()) (fun _ _ => firstOrderChainCoefficientLaw Θ R hR) n

theorem firstOrderObservedPrefix_sampling (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    finiteStateSamplingLaw (firstOrderObservedInitial P Θ β) (firstOrderObservedStep P Θ A β)
      (firstOrderObservedPrefix P Θ β R hR) n=firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n := by
  have hk : finiteStateTransition (firstOrderObservedInitial P Θ β) (firstOrderObservedStep P Θ A β)
      (firstOrderObservedPrefix P Θ β R hR)=firstOrderComparisonTransition P Θ A β R hR a₀ := by
    funext k h
    unfold finiteStateTransition
    rw [firstOrderObservedRun_eq P Θ A β a₀ k h]
    rfl
  unfold finiteStateSamplingLaw firstOrderComparisonSamplingLaw
  rw [hk]

/-- Full biased and fair-filled sampling give exactly the same law of the
comparison state jointly with its entire far-jump event. No pathwise coupling
between different latent coefficient laws is assumed. -/
theorem firstOrderComparison_mean_transport (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (F : (Prop × (ℕ × S)) → ℝ) :
    pmfMean (firstOrderOriginalSamplingLaw Θ R hR n)
      (fun h => F (firstOrderHistoryFar P Θ A β a₀ n h,firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n))=
    pmfMean (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)
      (fun h => F (firstOrderHistoryFar P Θ A β a₀ n h,firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n)) := by
  have hh := finiteStateSamplingLaw_transport (firstOrderObservedInitial P Θ β) (firstOrderObservedStep P Θ A β)
    (fun _ _ => firstOrderChainCoefficientLaw Θ R hR) (firstOrderObservedPrefix P Θ β R hR)
    (firstOrderObservedStep_mean_transport P Θ A β R hR) n F
  rw [firstOrderObservedPrefix_sampling P Θ A β R hR a₀ n] at hh
  simp_rw [firstOrderObservedRun_eq P Θ A β a₀ n] at hh
  exact hh

def firstOrderOriginalJointLaw (d T : ℕ) (R : ℝ) (hR : 2≤R) (n : ℕ) :=
  finiteConditionalPMF (firstOrderHiddenPrior d T) (fun Θ => firstOrderOriginalSamplingLaw Θ R hR n)

theorem firstOrderComparison_joint_mean_transport (P : FirstOrderPolicy d T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (F : (Fin (T+1) → (Fin d → Bool)) → (Prop × (ℕ × S)) → ℝ) :
    pmfMean (firstOrderOriginalJointLaw d T R hR n)
      (fun w => F w.1 (firstOrderHistoryFar P w.1 A β a₀ n w.2,
        firstOrderComparisonRun P w.1 A β (finiteHistoryTape a₀ n w.2) n))=
    pmfMean (firstOrderComparisonJointLaw P A β R hR a₀ n)
      (fun w => F w.1 (firstOrderHistoryFar P w.1 A β a₀ n w.2,
        firstOrderComparisonRun P w.1 A β (finiteHistoryTape a₀ n w.2) n)) := by
  rw [firstOrderOriginalJointLaw, firstOrderComparisonJointLaw,
    finiteConditionalPMF_mean, finiteConditionalPMF_mean]
  apply pmfMean_congr
  intro Θ
  exact firstOrderComparison_mean_transport P Θ A β R hR a₀ n (F Θ)

/-- The previously proved comparison far-jump bound now holds under the
actual original full-array sampling law. -/
theorem firstOrderOriginal_far_probability (P : FirstOrderPolicy d T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    pmfEventProbability (firstOrderOriginalJointLaw d T R hR n)
      (fun w => decide (firstOrderHistoryFar P w.1 A β a₀ n w.2))≤
      (n+1:ℕ)*((T+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq]
  rw [firstOrderComparison_joint_mean_transport P A β R hR a₀ n (fun _ s => if s.1 then 1 else 0)]
  have hh := firstOrderComparison_history_far_probability P A β R hR a₀ n
  simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hh

end
end SecondOrder

