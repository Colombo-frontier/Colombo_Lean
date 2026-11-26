import SecondOrder.CurvatureStoppedProbability

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvatureContinuationStep_update (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (θ : BalancedVector m) (R : ℝ) :
    (curvatureContinuationStep P (Function.update Θ i θ) A β start i.val cap dummy (R := R))=
      curvatureContinuationStep P Θ A β start i.val cap dummy := by
  funext n s z
  apply curvatureContinuationStep_prefix
  intro j hj
  have hne : j≠i := by intro he; subst j; omega
  exact Function.update_of_ne hne _ _

theorem curvatureContinuationIndex_update (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) (θ : BalancedVector m) (R : ℝ) :
    (curvatureContinuationIndex P (Function.update Θ i θ) A β start i.val cap dummy s₀ (R := R))=
      curvatureContinuationIndex P Θ A β start i.val cap dummy s₀ := by
  funext n h
  unfold curvatureContinuationIndex
  rw [curvatureContinuationStep_update]
  apply curvatureLimitedProgress_prefix
  intro j hj
  have hne : j≠i := by intro he; subst j; omega
  exact Function.update_of_ne hne _ _

theorem curvatureContinuationQuery_update (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) (θ : BalancedVector m) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    curvatureContinuationQuery P (Function.update Θ i θ) A β start i cap dummy s₀ a₀ n=
      curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n := by
  funext t h
  unfold curvatureContinuationQuery
  rw [curvatureContinuationStep_update]

/-- The hidden-target capped experiment is exactly the mixture of the
concrete capped continuation laws for each possible target vector. -/
theorem curvatureContinuationTrueLaw_mean (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (s₀ : S) (n : ℕ)
    (F : BalancedVector m → FiniteHistory Unit (CurvatureCoefficients m T R) n → ℝ) :
    pmfMean (curvatureContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => F (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h))=
      pmfMean (PMF.uniformOfFintype (BalancedVector m)) (fun θ =>
        pmfMean (finiteAdaptiveLaw (PMF.pure ())
          (curvatureContinuationKernel P (Function.update Θ i θ) A β R hR start i.val cap dummy s₀) n) (F θ)) := by
  have hk : cappedTransition
      (curvatureStageSelected (curvatureLiftedIndex (curvatureContinuationIndex P Θ A β start i.val cap dummy s₀)) i.val) cap
      (curvatureStageTrue (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR
        (curvatureLiftedIndex (curvatureContinuationIndex P Θ A β start i.val cap dummy s₀)))
      (curvatureStageDummy (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR)=
      parameterizedTransition (fun θ =>
        curvatureContinuationKernel P (Function.update Θ i θ) A β R hR start i.val cap dummy s₀) := by
    change cappedTransition
      (fun n h => curvatureStageSelected (curvatureContinuationIndex P Θ A β start i.val cap dummy s₀) i.val
        n (finiteHistoryMapInitial Prod.snd n h)) cap
      (parameterizedTransition (fun θ n h => curvaturePrefixCoefficientLaw (Function.update Θ i θ) R hR
        (curvatureContinuationIndex P Θ A β start i.val cap dummy s₀ n h+1)))
      (parameterizedTransition (fun θ _ _ => curvaturePrefixCoefficientLaw (Function.update Θ i θ) R hR 0))=_
    rw [cappedTransition_parameter]
    apply congrArg parameterizedTransition
    funext θ
    unfold curvatureContinuationKernel
    rw [curvatureContinuationIndex_update]
  unfold curvatureContinuationTrueLaw curvatureCappedTrueLaw
  rw [hk]
  exact finiteAdaptiveLaw_parameter_mean _ _ _ n F

end
end SecondOrder
