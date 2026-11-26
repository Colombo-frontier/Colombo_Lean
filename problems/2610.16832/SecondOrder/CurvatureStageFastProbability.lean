import SecondOrder.CurvatureEntrySum

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- The per-stage fast probability under the actual joint comparison law,
averaging every hidden vector and every adaptive coefficient history. -/
theorem curvatureStageFast_probability (P : CurvaturePolicy m T S)
    (hm : 0<m) (A β R : ℝ) (hR : 2≤R) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfEventProbability (curvatureComparisonJointLaw P A β R hR a₀ N)
      (fun w => decide (curvatureStageFast P w.1 A β (finiteHistoryTape a₀ N w.2) i cap N))≤1/32 := by
  rw [pmfEventProbability_mean, curvatureComparisonJointLaw, finiteConditionalPMF_mean]
  simp only [decide_eq_true_eq]
  let G := fun Θ => pmfMean (curvatureComparisonSamplingLaw P Θ A β R hR a₀ N)
    (fun h => if curvatureStageFast P Θ A β (finiteHistoryTape a₀ N h) i cap N then (1:ℝ) else 0)
  unfold curvatureHiddenPrior
  change pmfMean (finitePiPMF (fun _ : Fin (T+1) => PMF.uniformOfFintype (BalancedVector m))) G≤_
  have he := finitePiPMF_resample_mean_any_fintype inferInstance
    (fun _ : Fin (T+1) => PMF.uniformOfFintype (BalancedVector m)) i G
  rw [←he]
  apply pmfMean_le_const
  intro Θ
  have hh := curvatureStageFast_coordinate_probability P Θ hm A β R hR i cap dummy a₀ N hhorizon hlarge hcap
  rw [pmfEventProbability_mean, curvatureCoordinateSamplingLaw, finiteConditionalPMF_mean] at hh
  simpa only [G, decide_eq_true_eq] using hh

end
end SecondOrder
