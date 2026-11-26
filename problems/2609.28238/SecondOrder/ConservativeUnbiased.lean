import SecondOrder.ConservativeFeatures

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {T m : ℕ} {E : Fin (T+1) → Type*} {Θ : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

namespace ConservativeFeatureData

theorem payload_mean (D : ConservativeFeatureData T m E Θ) (θ : Fin (T+1) → Θ)
    (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (x : PiLp 2 E) :
    pmfMean (D.arrayLaw θ R hR) (fun z =>
      conservativePayload (fun i => D.population i (θ i)) (fun i => D.sample i (z i)) j x)=0 := by
  by_cases hj : j<T+1
  · simp only [conservativePayload,dif_pos hj,pmfMean_mul,pmfMean_sub,pmfMean_const]
    have hc := finitePiPMF_coordinate_mean (fun i => D.blockLaw i (θ i) R hR) (⟨j,hj⟩ : Fin (T+1))
      (fun zi => D.sample ⟨j,hj⟩ zi (x ⟨j,hj⟩))
    have hm : pmfMean (D.blockLaw ⟨j,hj⟩ (θ ⟨j,hj⟩) R hR)
        (fun zi => D.sample ⟨j,hj⟩ zi (x ⟨j,hj⟩))=D.population ⟨j,hj⟩ (θ ⟨j,hj⟩) (x ⟨j,hj⟩) := by
      simpa only [PMF.integral_eq_sum,pmfMean] using D.sample_mean ⟨j,hj⟩ (θ ⟨j,hj⟩) R hR (x ⟨j,hj⟩)
    rw [hm] at hc
    have hc' : pmfMean (D.arrayLaw θ R hR) (fun z => D.sample ⟨j,hj⟩ (z ⟨j,hj⟩) (x ⟨j,hj⟩))=
        D.population ⟨j,hj⟩ (θ ⟨j,hj⟩) (x ⟨j,hj⟩) := by
      unfold pmfMean at hc ⊢
      refine Eq.trans ?_ hc
      apply Finset.sum_congr (by ext z; simp)
      intro z _
      rfl
    rw [hc',sub_self,mul_zero]
  · simp only [conservativePayload,dif_neg hj,pmfMean_const]

/-- The manuscript's full finite-feature chain is unbiased in value,
gradient and Hessian under its actual fixed independent coefficient law. -/
theorem loss_unbiased (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    let F := conservativePopulation reg (fun i => D.population i (θ i)) (fun i => gate i (θ i))
    (∫ z, D.loss reg gate θ z x ∂(D.arrayLaw θ R hR).toMeasure)=F x ∧
      (∫ z, gradient (D.loss reg gate θ z) x ∂(D.arrayLaw θ R hR).toMeasure)=gradient F x ∧
      (∫ z, fderiv ℝ (gradient (D.loss reg gate θ z)) x ∂(D.arrayLaw θ R hR).toMeasure)=
        fderiv ℝ (gradient F) x := by
  exact dependentConservativeLoss_unbiased (D.arrayLaw θ R hR)
    (conservativePopulation reg (fun i => D.population i (θ i)) (fun i => gate i (θ i)))
    (fun i => gate i (θ i))
    (fun z => conservativePayload (fun i => D.population i (θ i)) (fun i => D.sample i (z i)))
    (conservativePopulation_contDiff reg _ _ hreg (fun i => D.population_contDiff h0 hφ i (θ i))
      (fun i => hgate i (θ i)))
    (fun i => hgate i (θ i))
    (fun z j _ => conservativePayload_contDiff _ _ (fun i => D.population_contDiff h0 hφ i (θ i))
      (fun i => D.sample_contDiff h0 hφ i (z i)) j)
    (fun y j _ => D.payload_mean θ R hR j y) x

end ConservativeFeatureData
end
end SecondOrder
