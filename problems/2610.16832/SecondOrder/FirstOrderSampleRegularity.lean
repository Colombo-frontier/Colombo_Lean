import SecondOrder.BoundedSelector
import SecondOrder.FirstOrderNoiseBounds

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

theorem firstOrderBlockNoise_boundedC3 (θ : Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : Fin d → SignedCoefficient R) : BoundedC3 (firstOrderBlockNoise θ z) := by
  have hA : 0≤R+1 := by linarith
  have hs : 0≤24*(R+1)*Real.sqrt d := by positivity
  refine ⟨firstOrderBlockNoise_contDiff θ z 3,16*(R+1)+24*(R+1)*Real.sqrt d,by positivity,?_⟩
  intro x k hk
  have hh := firstOrderBlockNoise_bounds θ hd R hR z x
  interval_cases k
  · rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    linarith [hh.1]
  · rw [norm_first_iteratedFDeriv,←norm_gradient_eq_fderiv]
    linarith [hh.2.1]
  · rw [←norm_fderiv_gradient]
    change ‖hessian (firstOrderBlockNoise θ z) x‖≤_
    linarith [hh.2.2.1]
  · linarith [hh.2.2.2]

theorem firstOrderBlockCompletion_boundedC3 (θ : Fin d → Bool) (hd : 0<d) :
    BoundedC3 (firstOrderBlockCompletion θ) := by
  have hC : 0≤firstOrderJetConstant := le_trans (by norm_num) firstOrderJetConstant_ge_one
  have hs : 0≤firstOrderJetConstant*Real.sqrt d := by positivity
  refine ⟨firstOrderBlockCompletion_contDiff θ,firstOrderJetConstant+firstOrderJetConstant*Real.sqrt d,by positivity,?_⟩
  intro x k hk
  have hh := firstOrderBlockCompletion_jet θ hd x
  interval_cases k
  · rw [norm_iteratedFDeriv_zero]
    linarith [hh.1]
  · linarith [hh.2.1]
  · linarith [hh.2.2.1]
  · linarith [hh.2.2.2]

theorem firstOrderNoisePayload_boundedC3 (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : FirstOrderCoefficients d T R) (j : ℕ) :
    BoundedC3 (firstOrderNoisePayload Θ z j) := by
  by_cases hj : j<T+1
  · have he : firstOrderNoisePayload Θ z j=fun x : FirstOrderSpace d T =>
        firstOrderPayloadScale j*firstOrderBlockNoise (Θ ⟨j,hj⟩) (z ⟨j,hj⟩) (x ⟨j,hj⟩) := by
      funext x
      simp only [firstOrderNoisePayload,dif_pos hj]
    rw [he]
    exact ((firstOrderBlockNoise_boundedC3 (Θ ⟨j,hj⟩) hd R hR (z ⟨j,hj⟩)).comp_contraction
      (blockProj (⟨j,hj⟩ : Fin (T+1))) (blockProj_norm_le_one _)).const_mul _
  · have he : firstOrderNoisePayload Θ z j=fun _ => (0:ℝ) := by
      funext x
      simp only [firstOrderNoisePayload,dif_neg hj]
    rw [he]
    exact boundedC3_const 0

theorem firstOrderChainNoise_boundedC3 (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : FirstOrderCoefficients d T R) : BoundedC3 (firstOrderChainNoise Θ z) :=
  boundedC3_reverseBlockSelector _ _ (fun i => firstOrderBlockCompletion_boundedC3 (Θ i) hd)
    (fun j _ => firstOrderNoisePayload_boundedC3 Θ hd R hR z j)

/-- The unbounded public regularizer is handled by its Hessian Lipschitz bound;
only the selector noise is required to have bounded value and derivatives. -/
theorem firstOrderRandomLoss_C21 (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : FirstOrderCoefficients d T R) :
    ContDiff ℝ 2 (firstOrderRandomLoss Θ z) ∧ ∃ C : ℝ, 0≤C ∧ ∀ x y,
      ‖fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) y-
        fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) x‖≤C*‖y-x‖ := by
  obtain ⟨C,hC,hn⟩ := (firstOrderChainNoise_boundedC3 Θ hd R hR z).hessian_lipschitz
  have hgeom := firstOrderGeometryConstant_pos
  have hF := (firstOrderChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have hN := (firstOrderChainNoise_contDiff Θ z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  refine ⟨(firstOrderRandomLoss_contDiff Θ z).of_le (show (2:WithTop ℕ∞)≤3 by decide),
    firstOrderGeometryConstant*Real.sqrt d+C,by positivity,?_⟩
  intro x y
  have he (w : FirstOrderSpace d T) : fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) w=
      fderiv ℝ (gradient (firstOrderChain Θ)) w+fderiv ℝ (gradient (firstOrderChainNoise Θ z)) w :=
    hessian_add_scalar hF hN w
  have he' : fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) y-fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) x=
      (fderiv ℝ (gradient (firstOrderChain Θ)) y-fderiv ℝ (gradient (firstOrderChain Θ)) x)+
      (fderiv ℝ (gradient (firstOrderChainNoise Θ z)) y-fderiv ℝ (gradient (firstOrderChainNoise Θ z)) x) := by
    rw [he,he]
    abel
  rw [he',add_mul]
  exact (norm_add_le _ _).trans (add_le_add (firstOrderChain_hessian_lipschitz Θ hd x y) (hn x y))

end
end SecondOrder
