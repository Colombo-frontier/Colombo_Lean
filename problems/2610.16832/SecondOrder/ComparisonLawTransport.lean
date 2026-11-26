import SecondOrder.ComparisonObservedState

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- The original oracle draws a fresh full biased coefficient array on every
call. This is its actual finite sample-history distribution. -/
def curvatureOriginalSamplingLaw (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R) (n : ℕ) :=
  finiteAdaptiveLaw (PMF.pure ()) (fun _ _ => curvatureCoefficientLaw Θ R hR) n

theorem curvatureObservedPrefix_sampling (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    finiteStateSamplingLaw (curvatureObservedInitial P Θ β) (curvatureObservedStep P Θ A β)
      (curvatureObservedPrefix P Θ β R hR) n=curvatureComparisonSamplingLaw P Θ A β R hR a₀ n := by
  have hk : finiteStateTransition (curvatureObservedInitial P Θ β) (curvatureObservedStep P Θ A β)
      (curvatureObservedPrefix P Θ β R hR)=curvatureComparisonTransition P Θ A β R hR a₀ := by
    funext k h
    unfold finiteStateTransition
    rw [curvatureObservedRun_eq P Θ A β a₀ k h]
    rfl
  unfold finiteStateSamplingLaw curvatureComparisonSamplingLaw
  rw [hk]

/-- Full biased and fair-filled sampling give exactly the same law of the
comparison state jointly with its entire far-jump event. No pathwise coupling
between different latent coefficient laws is assumed. -/
theorem curvatureComparison_mean_transport (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (F : (Prop × (ℕ × S)) → ℝ) :
    pmfMean (curvatureOriginalSamplingLaw Θ R hR n)
      (fun h => F (curvatureHistoryFar P Θ A β a₀ n h,curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n))=
    pmfMean (curvatureComparisonSamplingLaw P Θ A β R hR a₀ n)
      (fun h => F (curvatureHistoryFar P Θ A β a₀ n h,curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n)) := by
  have hh := finiteStateSamplingLaw_transport (curvatureObservedInitial P Θ β) (curvatureObservedStep P Θ A β)
    (fun _ _ => curvatureCoefficientLaw Θ R hR) (curvatureObservedPrefix P Θ β R hR)
    (curvatureObservedStep_mean_transport P Θ A β R hR) n F
  rw [curvatureObservedPrefix_sampling P Θ A β R hR a₀ n] at hh
  simp_rw [curvatureObservedRun_eq P Θ A β a₀ n] at hh
  exact hh

def curvatureOriginalJointLaw (m T : ℕ) (R : ℝ) (hR : 2≤R) (n : ℕ) :=
  finiteConditionalPMF (curvatureHiddenPrior m T) (fun Θ => curvatureOriginalSamplingLaw Θ R hR n)

theorem curvatureComparison_joint_mean_transport (P : CurvaturePolicy m T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : CurvatureCoefficients m T R) (n : ℕ)
    (F : (Fin (T+1) → BalancedVector m) → (Prop × (ℕ × S)) → ℝ) :
    pmfMean (curvatureOriginalJointLaw m T R hR n)
      (fun w => F w.1 (curvatureHistoryFar P w.1 A β a₀ n w.2,
        curvatureComparisonRun P w.1 A β (finiteHistoryTape a₀ n w.2) n))=
    pmfMean (curvatureComparisonJointLaw P A β R hR a₀ n)
      (fun w => F w.1 (curvatureHistoryFar P w.1 A β a₀ n w.2,
        curvatureComparisonRun P w.1 A β (finiteHistoryTape a₀ n w.2) n)) := by
  rw [curvatureOriginalJointLaw, curvatureComparisonJointLaw,
    finiteConditionalPMF_mean, finiteConditionalPMF_mean]
  apply pmfMean_congr
  intro Θ
  exact curvatureComparison_mean_transport P Θ A β R hR a₀ n (F Θ)

/-- The previously proved comparison far-jump bound now holds under the
actual original full-array sampling law. -/
theorem curvatureOriginal_far_probability (P : CurvaturePolicy m T S)
    (A β R : ℝ) (hR : 2≤R) (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    pmfEventProbability (curvatureOriginalJointLaw m T R hR n)
      (fun w => decide (curvatureHistoryFar P w.1 A β a₀ n w.2))≤
      (n+1:ℕ)*((T+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq]
  rw [curvatureComparison_joint_mean_transport P A β R hR a₀ n (fun _ s => if s.1 then 1 else 0)]
  have hh := curvatureComparison_history_far_probability P A β R hR a₀ n
  simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hh

end
end SecondOrder
