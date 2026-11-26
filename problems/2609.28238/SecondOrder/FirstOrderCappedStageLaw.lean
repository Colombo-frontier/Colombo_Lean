import SecondOrder.FirstOrderCappedHiddenIndependence

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderStagePrior (d : ℕ) : PMF ((Fin d → Bool) × Unit) :=
  finiteProdPMF (PMF.uniformOfFintype ((Fin d → Bool))) (PMF.pure ())

theorem firstOrderStagePrior_ne_zero (d : ℕ) : ∀ s, firstOrderStagePrior d s≠0 := by
  apply finiteProdPMF_ne_zero
  · intro θ; simp [PMF.uniformOfFintype_apply]
  · intro s; cases s; simp

def firstOrderCappedTrueLaw (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ) (cap n : ℕ) :=
  finiteAdaptiveLaw (firstOrderStagePrior d)
    (cappedTransition (firstOrderStageSelected (firstOrderLiftedIndex index) i.val) cap
      (firstOrderStageTrue (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR (firstOrderLiftedIndex index))
      (firstOrderStageDummy (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR)) n

def firstOrderCappedReferenceLaw (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ) (cap n : ℕ) :=
  finiteAdaptiveLaw (firstOrderStagePrior d)
    (cappedTransition (firstOrderStageSelected (firstOrderLiftedIndex index) i.val) cap
      (firstOrderStageReference (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR (firstOrderLiftedIndex index) i.val)
      (firstOrderStageDummy (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR)) n

theorem firstOrderCappedTrueLaw_ne_zero (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ) (cap n : ℕ) :
    ∀ h, firstOrderCappedTrueLaw Θ R hR i index cap n h≠0 :=
  finiteAdaptiveLaw_ne_zero _ _ (firstOrderStagePrior_ne_zero d)
    (cappedTransition_ne_zero _ cap _ _ (firstOrderStageTrue_ne_zero _ R hR _)
      (firstOrderStageDummy_ne_zero _ R hR)) n

theorem firstOrderCappedReferenceLaw_ne_zero (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ) (cap n : ℕ) :
    ∀ h, firstOrderCappedReferenceLaw Θ R hR i index cap n h≠0 :=
  finiteAdaptiveLaw_ne_zero _ _ (firstOrderStagePrior_ne_zero d)
    (cappedTransition_ne_zero _ cap _ _ (firstOrderStageReference_ne_zero _ R hR _ _)
      (firstOrderStageDummy_ne_zero _ R hR)) n

theorem firstOrderCappedStage_kl (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ) (cap n : ℕ) :
    pmfKL (firstOrderCappedTrueLaw Θ R hR i index cap n) (firstOrderCappedReferenceLaw Θ R hR i index cap n)≤
      firstOrderArrayInformation d R*cap :=
  firstOrderCappedExperiment_pmfKL _ _ R hR _ (by omega) cap n (firstOrderStagePrior_ne_zero d)

theorem firstOrderCappedStage_reference_activation (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap n : ℕ)
    (query : Fin (n+1) → FiniteHistory Unit (FirstOrderCoefficients d T R) n → Point d) :
    pmfEventProbability (firstOrderCappedReferenceLaw Θ R hR i index cap n)
      (fun h => decide (∃ t, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (query t (finiteHistoryMapInitial Prod.snd n h))))≤
      (n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128)) := by
  unfold firstOrderCappedReferenceLaw
  rw [firstOrderCappedReference_hidden Θ R hR i index hindex cap]
  exact firstOrderReferenceActivation_probability (PMF.pure ()) _ n query

theorem firstOrderCappedStage_activation_probability (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap n : ℕ)
    (query : Fin (n+1) → FiniteHistory Unit (FirstOrderCoefficients d T R) n → Point d)
    {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))))) :
    pmfEventProbability (firstOrderCappedTrueLaw Θ R hR i index cap n)
      (fun h => decide (∃ t, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (query t (finiteHistoryMapInitial Prod.snd n h))))≤
      (firstOrderArrayInformation d R*cap+Real.log 2)/B :=
  pmfEventProbability_information_bound _ _
    (firstOrderCappedTrueLaw_ne_zero Θ R hR i index cap n)
    (firstOrderCappedReferenceLaw_ne_zero Θ R hR i index cap n) _
    (mul_nonneg (firstOrderArrayInformation_nonneg d R) (Nat.cast_nonneg _))
    (firstOrderCappedStage_kl Θ R hR i index cap n) hB (by positivity) hrare
    (firstOrderCappedStage_reference_activation Θ R hR i index hindex cap n query) hlog

theorem firstOrderCappedStage_activation_one_thirty_second (Θ : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (i : Fin (T+1))
    (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap n : ℕ)
    (query : Fin (n+1) → FiniteHistory Unit (FirstOrderCoefficients d T R) n → Point d)
    {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128)))))
    (hbudget : 32*(firstOrderArrayInformation d R*cap+Real.log 2)≤B) :
    pmfEventProbability (firstOrderCappedTrueLaw Θ R hR i index cap n)
      (fun h => decide (∃ t, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (query t (finiteHistoryMapInitial Prod.snd n h))))≤1/32 := by
  apply (firstOrderCappedStage_activation_probability Θ R hR i index hindex cap n query hB hrare hlog).trans
  apply (div_le_iff₀ hB).mpr
  linarith only [hbudget]

end
end SecondOrder
