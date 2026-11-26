import SecondOrder.FirstOrderStoppedProbability

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderContinuationStep_update (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (θ : (Fin d → Bool)) (R : ℝ) :
    (firstOrderContinuationStep P (Function.update Θ i θ) A β start i.val cap dummy (R := R))=
      firstOrderContinuationStep P Θ A β start i.val cap dummy := by
  funext n s z
  apply firstOrderContinuationStep_prefix
  intro j hj
  have hne : j≠i := by intro he; subst j; omega
  exact Function.update_of_ne hne _ _

theorem firstOrderContinuationIndex_update (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) (θ : (Fin d → Bool)) (R : ℝ) :
    (firstOrderContinuationIndex P (Function.update Θ i θ) A β start i.val cap dummy s₀ (R := R))=
      firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀ := by
  funext n h
  unfold firstOrderContinuationIndex
  rw [firstOrderContinuationStep_update]
  apply firstOrderLimitedProgress_prefix
  intro j hj
  have hne : j≠i := by intro he; subst j; omega
  exact Function.update_of_ne hne _ _

theorem firstOrderContinuationQuery_update (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) (θ : (Fin d → Bool)) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    firstOrderContinuationQuery P (Function.update Θ i θ) A β start i cap dummy s₀ a₀ n=
      firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n := by
  funext t h
  unfold firstOrderContinuationQuery
  rw [firstOrderContinuationStep_update]

/-- The hidden-target capped experiment is exactly the mixture of the
concrete capped continuation laws for each possible target vector. -/
theorem firstOrderContinuationTrueLaw_mean (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (n : ℕ)
    (F : (Fin d → Bool) → FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℝ) :
    pmfMean (firstOrderContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => F (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h))=
      pmfMean (PMF.uniformOfFintype ((Fin d → Bool))) (fun θ =>
        pmfMean (finiteAdaptiveLaw (PMF.pure ())
          (firstOrderContinuationKernel P (Function.update Θ i θ) A β R hR start i.val cap dummy s₀) n) (F θ)) := by
  have hk : cappedTransition
      (firstOrderStageSelected (firstOrderLiftedIndex (firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀)) i.val) cap
      (firstOrderStageTrue (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR
        (firstOrderLiftedIndex (firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀)))
      (firstOrderStageDummy (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR)=
      parameterizedTransition (fun θ =>
        firstOrderContinuationKernel P (Function.update Θ i θ) A β R hR start i.val cap dummy s₀) := by
    change cappedTransition
      (fun n h => firstOrderStageSelected (firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀) i.val
        n (finiteHistoryMapInitial Prod.snd n h)) cap
      (parameterizedTransition (fun θ n h => firstOrderPrefixCoefficientLaw (Function.update Θ i θ) R hR
        (firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀ n h+1)))
      (parameterizedTransition (fun θ _ _ => firstOrderPrefixCoefficientLaw (Function.update Θ i θ) R hR 0))=_
    rw [cappedTransition_parameter]
    apply congrArg parameterizedTransition
    funext θ
    unfold firstOrderContinuationKernel
    rw [firstOrderContinuationIndex_update]
  unfold firstOrderContinuationTrueLaw firstOrderCappedTrueLaw
  rw [hk]
  exact finiteAdaptiveLaw_parameter_mean _ _ _ n F

end
end SecondOrder
