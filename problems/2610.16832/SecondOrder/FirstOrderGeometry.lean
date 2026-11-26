import SecondOrder.FirstOrderLocal

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderGeometryConstant : ℝ := 49*firstOrderJetConstant^2

theorem firstOrderGeometryConstant_pos : 0<firstOrderGeometryConstant := by
  norm_num [firstOrderGeometryConstant,firstOrderJetConstant,completionDerivativeBound]

theorem firstOrderChain_second_bound (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) : ‖iteratedFDeriv ℝ 2 (firstOrderChain Θ) x‖≤firstOrderGeometryConstant := by
  let head : FirstOrderSpace d T → ℝ := fun y => firstOrderBlockPotential (Θ 0) (y 0)
  let parts := localObjective (fun _ : Fin (T+1) => Point d) regularizedChainSupport (firstOrderLocalTerm Θ)
  have hh3 : ContDiff ℝ 3 head := (firstOrderBlockPotential_contDiff (Θ 0) 3).comp
    (blockProj (E := Point d) (0:Fin (T+1))).contDiff
  have hl3 : ContDiff ℝ 3 parts := localObjective_contDiff _ _ _ (firstOrderLocalTerm_contDiff Θ)
  have hh := ((firstOrderBlockPotential_jet (Θ 0) hd (x 0)).comp_linear
    (firstOrderBlockPotential_contDiff (Θ 0) 3)
    (blockProj (E := Point d) (0:Fin (T+1))) (blockProj_norm_le_one _) x).2.2.1
  have hl := regularizedChainObjective_second_bound (fun _ : Fin (T+1) => Point d) (firstOrderLocalTerm Θ)
    (fun i => (firstOrderLocalTerm_contDiff Θ i).of_le (show (2:WithTop ℕ∞)≤3 by decide))
    (show 0≤8*firstOrderJetConstant^2 by positivity) (fun i y => (firstOrderLocalTerm_bounds Θ hd i y).1) x
  rw [firstOrderChain_eq_local]
  change ‖iteratedFDeriv ℝ 2 (fun y => head y+parts y) x‖≤_
  rw [iteratedFDeriv_add_apply' (hh3.of_le (show (2:WithTop ℕ∞)≤3 by decide)).contDiffAt
    (hl3.of_le (show (2:WithTop ℕ∞)≤3 by decide)).contDiffAt]
  apply (norm_add_le _ _).trans ((add_le_add hh hl).trans _)
  unfold firstOrderGeometryConstant
  nlinarith [firstOrderJetConstant_ge_one]

theorem firstOrderChain_third_bound (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) :
    ‖iteratedFDeriv ℝ 3 (firstOrderChain Θ) x‖≤firstOrderGeometryConstant*Real.sqrt d := by
  let head : FirstOrderSpace d T → ℝ := fun y => firstOrderBlockPotential (Θ 0) (y 0)
  let parts := localObjective (fun _ : Fin (T+1) => Point d) regularizedChainSupport (firstOrderLocalTerm Θ)
  have hh3 : ContDiff ℝ 3 head := (firstOrderBlockPotential_contDiff (Θ 0) 3).comp
    (blockProj (E := Point d) (0:Fin (T+1))).contDiff
  have hl3 : ContDiff ℝ 3 parts := localObjective_contDiff _ _ _ (firstOrderLocalTerm_contDiff Θ)
  have hh := ((firstOrderBlockPotential_jet (Θ 0) hd (x 0)).comp_linear
    (firstOrderBlockPotential_contDiff (Θ 0) 3)
    (blockProj (E := Point d) (0:Fin (T+1))) (blockProj_norm_le_one _) x).2.2.2
  have hl := regularizedChainObjective_third_bound (fun _ : Fin (T+1) => Point d) (firstOrderLocalTerm Θ)
    (firstOrderLocalTerm_contDiff Θ)
    (show 0≤16*firstOrderJetConstant^2*Real.sqrt d by positivity)
    (fun i y => (firstOrderLocalTerm_bounds Θ hd i y).2) x
  rw [firstOrderChain_eq_local]
  change ‖iteratedFDeriv ℝ 3 (fun y => head y+parts y) x‖≤_
  rw [iteratedFDeriv_add_apply' hh3.contDiffAt hl3.contDiffAt]
  apply (norm_add_le _ _).trans ((add_le_add hh hl).trans _)
  have hc : firstOrderJetConstant≤firstOrderJetConstant^2 := by nlinarith [firstOrderJetConstant_ge_one]
  have hs := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (d:ℝ))
  unfold firstOrderGeometryConstant
  nlinarith only [hs]

theorem firstOrderChain_gradient_lipschitz (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x y : FirstOrderSpace d T) :
    ‖gradient (firstOrderChain Θ) y-gradient (firstOrderChain Θ) x‖≤firstOrderGeometryConstant*‖y-x‖ :=
  gradient_lipschitz_of_second_bound ((firstOrderChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide))
    (firstOrderChain_second_bound Θ hd) x y

theorem firstOrderChain_hessian_lipschitz (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x y : FirstOrderSpace d T) :
    ‖fderiv ℝ (gradient (firstOrderChain Θ)) y-fderiv ℝ (gradient (firstOrderChain Θ)) x‖≤
      (firstOrderGeometryConstant*Real.sqrt d)*‖y-x‖ :=
  fderiv_gradient_lipschitz_of_third_bound (firstOrderChain_contDiff Θ) (firstOrderChain_third_bound Θ hd) x y

/-- All deterministic conclusions of the first-order chain geometry lemma,
with T+1 blocks, actual Euclidean derivatives, and constants independent of T and D. -/
theorem firstOrderChain_geometry (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) :
    ContDiff ℝ 3 (firstOrderChain Θ) ∧ firstOrderChain Θ 0 = -6 ∧
    -20*(T+1:ℕ)≤firstOrderChain Θ x ∧ firstOrderChain Θ 0-firstOrderChain Θ x≤20*(T+1:ℕ) ∧
    ‖fderiv ℝ (gradient (firstOrderChain Θ)) x‖≤firstOrderGeometryConstant ∧
    ‖iteratedFDeriv ℝ 3 (firstOrderChain Θ) x‖≤firstOrderGeometryConstant*Real.sqrt d ∧
    ((∃ j, firstOrderBlockEncoding (Θ j) (x j)≤1/2) → firstOrderGradientConstant≤‖gradient (firstOrderChain Θ) x‖) := by
  refine ⟨firstOrderChain_contDiff Θ,firstOrderChain_zero Θ,firstOrderChain_lower Θ x,
    firstOrderChain_initial_gap Θ x,?_,firstOrderChain_third_bound Θ hd x,firstOrderChain_gradient_lower Θ hd x⟩
  rw [norm_fderiv_gradient]
  exact firstOrderChain_second_bound Θ hd x

end
end SecondOrder

