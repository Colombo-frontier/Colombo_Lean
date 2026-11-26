import SecondOrder.FirstOrderEntrySum

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- The per-stage fast probability under the actual joint comparison law,
averaging every hidden vector and every adaptive coefficient history. -/
theorem firstOrderStageFast_probability (P : FirstOrderPolicy d T S)
    (hd : 0<d) (A β R : ℝ) (hR : 2≤R) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ N)
      (fun w => decide (firstOrderStageFast P w.1 A β (finiteHistoryTape a₀ N w.2) i cap N))≤1/32 := by
  rw [pmfEventProbability_mean, firstOrderComparisonJointLaw, finiteConditionalPMF_mean]
  simp only [decide_eq_true_eq]
  let G := fun Θ => pmfMean (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ N)
    (fun h => if firstOrderStageFast P Θ A β (finiteHistoryTape a₀ N h) i cap N then (1:ℝ) else 0)
  unfold firstOrderHiddenPrior
  change pmfMean (finitePiPMF (fun _ : Fin (T+1) => PMF.uniformOfFintype ((Fin d → Bool)))) G≤_
  have he := finitePiPMF_resample_mean_any_fintype inferInstance
    (fun _ : Fin (T+1) => PMF.uniformOfFintype ((Fin d → Bool))) i G
  rw [←he]
  apply pmfMean_le_const
  intro Θ
  have hh := firstOrderStageFast_coordinate_probability P Θ hd A β R hR i cap dummy a₀ N hhorizon hlarge hcap
  rw [pmfEventProbability_mean, firstOrderCoordinateSamplingLaw, finiteConditionalPMF_mean] at hh
  simpa only [G, decide_eq_true_eq] using hh

end
end SecondOrder
