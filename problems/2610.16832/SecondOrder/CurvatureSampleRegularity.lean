import SecondOrder.BoundedSelector
import SecondOrder.CurvatureNoiseBounds
import SecondOrder.PeriodicJets

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

theorem periodicBlockNoise_boundedC3 (θ : BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : UpperPair (2*m) → SignedCoefficient R) :
    BoundedC3 (periodicBlockNoise θ z) := by
  have hA : 0 ≤ R+1 := by linarith
  have hs : 0 ≤ (R+1)/Real.sqrt ((2*m:ℕ):ℝ) := by positivity
  have hd : 0 ≤ (R+1)/((2*m:ℕ):ℝ) := by positivity
  refine ⟨periodicBlockNoise_contDiff θ z 3,
    2*(R+1)+2*((R+1)/Real.sqrt ((2*m:ℕ):ℝ))+2*((R+1)/((2*m:ℕ):ℝ)), by positivity, ?_⟩
  intro x k hk
  have hh := periodicBlockNoise_bounds θ hm R hR z x
  interval_cases k
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    linarith [hh.1]
  · rw [norm_first_iteratedFDeriv, ← norm_gradient_eq_fderiv]
    linarith [hh.2.1]
  · rw [← norm_fderiv_gradient]
    change ‖hessian (periodicBlockNoise θ z) x‖ ≤ _
    linarith [hh.2.2.1]
  · have h3 := hh.2.2.2
    rw [mul_div_assoc] at h3
    linarith

theorem periodicCompletion_boundedC3 (θ : BalancedVector m) (hm : 0 < m) :
    BoundedC3 (periodicCompletion θ) :=
  boundedC3_of_dimensionJet (periodicCompletion_contDiff θ) curvatureJetConstant_ge_one
    (by exact_mod_cast (show 1 ≤ 2*m by omega)) (periodicCompletion_dimensionJet θ hm)

theorem periodicBlockPotential_boundedC3 (θ : BalancedVector m) (hm : 0 < m) :
    BoundedC3 (periodicBlockPotential θ) :=
  boundedC3_of_dimensionJet (periodicBlockPotential_contDiff θ 3) curvatureJetConstant_ge_one
    (by exact_mod_cast (show 1 ≤ 2*m by omega)) (periodicBlockPotential_dimensionJet θ hm)

theorem curvatureNoisePayload_boundedC3 (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : CurvatureCoefficients m T R) (j : ℕ) :
    BoundedC3 (curvatureNoisePayload Θ z j) := by
  by_cases hj : j<T+1
  · have he : curvatureNoisePayload Θ z j = fun x : CurvatureSpace m T =>
        curvaturePayloadScale j*periodicBlockNoise (Θ ⟨j,hj⟩) (z ⟨j,hj⟩) (x ⟨j,hj⟩) := by
      funext x
      simp only [curvatureNoisePayload, dif_pos hj]
    rw [he]
    exact ((periodicBlockNoise_boundedC3 (Θ ⟨j,hj⟩) hm R hR (z ⟨j,hj⟩)).comp_contraction
      (blockProj (⟨j,hj⟩ : Fin (T+1))) (blockProj_norm_le_one _)).const_mul _
  · have he : curvatureNoisePayload Θ z j = fun _ => (0:ℝ) := by
      funext x
      simp only [curvatureNoisePayload, dif_neg hj]
    rw [he]
    exact boundedC3_const 0

theorem curvatureChain_boundedC3 (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m) :
    BoundedC3 (curvatureChain Θ) := by
  apply BoundedC3.add
  · exact (periodicBlockPotential_boundedC3 (Θ 0) hm).comp_contraction (blockProj (0 : Fin (T+1))) (blockProj_norm_le_one _)
  · apply boundedC3_finset_sum
    intro i _
    exact (((periodicCompletion_boundedC3 (Θ i.castSucc) hm).comp_contraction
      (blockProj i.castSucc) (blockProj_norm_le_one _)).mul
      ((periodicBlockPotential_boundedC3 (Θ i.succ) hm).comp_contraction
      (blockProj i.succ) (blockProj_norm_le_one _))).const_mul 2

/-- Global C²,¹ regularity is proved for every coefficient realization. The
regularity constant may depend on chain length; the noise bounds above do not. -/
theorem curvatureRandomLoss_C21 (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : CurvatureCoefficients m T R) :
    ContDiff ℝ 2 (curvatureRandomLoss Θ z) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      ‖fderiv ℝ (gradient (curvatureRandomLoss Θ z)) y-
        fderiv ℝ (gradient (curvatureRandomLoss Θ z)) x‖ ≤ C*‖y-x‖ := by
  have hn : BoundedC3 (curvatureChainNoise Θ z) := boundedC3_reverseBlockSelector _ _
    (fun i => periodicCompletion_boundedC3 (Θ i) hm)
    (fun j _ => curvatureNoisePayload_boundedC3 Θ hm R hR z j)
  have hf : BoundedC3 (curvatureRandomLoss Θ z) := (curvatureChain_boundedC3 Θ hm).add hn
  exact ⟨hf.1.of_le (show (2:WithTop ℕ∞) ≤ 3 by decide), hf.hessian_lipschitz⟩

end
end SecondOrder
