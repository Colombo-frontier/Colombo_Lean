import SecondOrder.CappedHiddenIndependence

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

def curvatureStagePrior (m : ℕ) : PMF (BalancedVector m × Unit) :=
  finiteProdPMF (PMF.uniformOfFintype (BalancedVector m)) (PMF.pure ())

theorem curvatureStagePrior_ne_zero (m : ℕ) : ∀ s, curvatureStagePrior m s≠0 := by
  apply finiteProdPMF_ne_zero
  · intro θ; simp [PMF.uniformOfFintype_apply]
  · intro s; cases s; simp

def curvatureCappedTrueLaw (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ) (cap n : ℕ) :=
  finiteAdaptiveLaw (curvatureStagePrior m)
    (cappedTransition (curvatureStageSelected (curvatureLiftedIndex index) i.val) cap
      (curvatureStageTrue (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR (curvatureLiftedIndex index))
      (curvatureStageDummy (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR)) n

def curvatureCappedReferenceLaw (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ) (cap n : ℕ) :=
  finiteAdaptiveLaw (curvatureStagePrior m)
    (cappedTransition (curvatureStageSelected (curvatureLiftedIndex index) i.val) cap
      (curvatureStageReference (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR (curvatureLiftedIndex index) i.val)
      (curvatureStageDummy (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR)) n

theorem curvatureCappedTrueLaw_ne_zero (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ) (cap n : ℕ) :
    ∀ h, curvatureCappedTrueLaw Θ R hR i index cap n h≠0 :=
  finiteAdaptiveLaw_ne_zero _ _ (curvatureStagePrior_ne_zero m)
    (cappedTransition_ne_zero _ cap _ _ (curvatureStageTrue_ne_zero _ R hR _)
      (curvatureStageDummy_ne_zero _ R hR)) n

theorem curvatureCappedReferenceLaw_ne_zero (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ) (cap n : ℕ) :
    ∀ h, curvatureCappedReferenceLaw Θ R hR i index cap n h≠0 :=
  finiteAdaptiveLaw_ne_zero _ _ (curvatureStagePrior_ne_zero m)
    (cappedTransition_ne_zero _ cap _ _ (curvatureStageReference_ne_zero _ R hR _ _)
      (curvatureStageDummy_ne_zero _ R hR)) n

theorem curvatureCappedStage_kl (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ) (cap n : ℕ) :
    pmfKL (curvatureCappedTrueLaw Θ R hR i index cap n) (curvatureCappedReferenceLaw Θ R hR i index cap n)≤
      curvatureArrayInformation m R*cap :=
  curvatureCappedExperiment_pmfKL _ _ R hR _ (by omega) cap n (curvatureStagePrior_ne_zero m)

theorem curvatureCappedStage_reference_activation (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap n : ℕ)
    (query : Fin (n+1) → FiniteHistory Unit (CurvatureCoefficients m T R) n → Point (2*m)) :
    pmfEventProbability (curvatureCappedReferenceLaw Θ R hR i index cap n)
      (fun h => decide (∃ t, 0<periodicCompletion (finiteHistoryInitial n h).1
        (query t (finiteHistoryMapInitial Prod.snd n h))))≤
      (n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512)) := by
  unfold curvatureCappedReferenceLaw
  rw [curvatureCappedReference_hidden Θ R hR i index hindex cap]
  exact curvatureReferenceActivation_probability (PMF.pure ()) _ n query

theorem curvatureCappedStage_activation_probability (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap n : ℕ)
    (query : Fin (n+1) → FiniteHistory Unit (CurvatureCoefficients m T R) n → Point (2*m))
    {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))))) :
    pmfEventProbability (curvatureCappedTrueLaw Θ R hR i index cap n)
      (fun h => decide (∃ t, 0<periodicCompletion (finiteHistoryInitial n h).1
        (query t (finiteHistoryMapInitial Prod.snd n h))))≤
      (curvatureArrayInformation m R*cap+Real.log 2)/B :=
  pmfEventProbability_information_bound _ _
    (curvatureCappedTrueLaw_ne_zero Θ R hR i index cap n)
    (curvatureCappedReferenceLaw_ne_zero Θ R hR i index cap n) _
    (mul_nonneg (curvatureArrayInformation_nonneg m R) (Nat.cast_nonneg _))
    (curvatureCappedStage_kl Θ R hR i index cap n) hB (by positivity) hrare
    (curvatureCappedStage_reference_activation Θ R hR i index hindex cap n query) hlog

theorem curvatureCappedStage_activation_one_thirty_second (Θ : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (i : Fin (T+1))
    (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap n : ℕ)
    (query : Fin (n+1) → FiniteHistory Unit (CurvatureCoefficients m T R) n → Point (2*m))
    {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512)))))
    (hbudget : 32*(curvatureArrayInformation m R*cap+Real.log 2)≤B) :
    pmfEventProbability (curvatureCappedTrueLaw Θ R hR i index cap n)
      (fun h => decide (∃ t, 0<periodicCompletion (finiteHistoryInitial n h).1
        (query t (finiteHistoryMapInitial Prod.snd n h))))≤1/32 := by
  apply (curvatureCappedStage_activation_probability Θ R hR i index hindex cap n query hB hrare hlog).trans
  apply (div_le_iff₀ hB).mpr
  linarith only [hbudget]

end
end SecondOrder
