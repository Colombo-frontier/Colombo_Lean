import SecondOrder.BernoulliMixtureOperatorBounds
import SecondOrder.BlockDirections

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem secondBilinear_comp_linear {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    (L : E →L[ℝ] F) (x u v : E) :
    secondBilinear (f ∘ L) x u v = secondBilinear f (L x) (L u) (L v) := by
  have hh := congrArg (fun A => A ![u,v]) (L.iteratedFDeriv_comp_right hf x (le_refl 2))
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply] at hh
  exact hh

theorem blockGate_fderiv (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x u : HomogeneousBlocks ι E) (i : ι) :
    fderiv ℝ (fun y : HomogeneousBlocks ι E => p i (y i)) x u = fderiv ℝ (p i) (x i) (u i) := by
  change fderiv ℝ (p i ∘ blockProj i) x u = _
  rw [fderiv_comp x ((hp i).differentiable (by norm_num) _) (blockProj i).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, blockProj_apply]

theorem blockGate_secondBilinear (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x u v : HomogeneousBlocks ι E) (i : ι) :
    secondBilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u v =
      secondBilinear (p i) (x i) (u i) (v i) :=
  secondBilinear_comp_linear (hp i) (blockProj i) x u v

/-- Disjoint blocks turn individual Fisher bounds into one energy bound without
introducing the number of blocks. -/
theorem blockGate_fisher_energy (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x : HomogeneousBlocks ι E) (hp0 : ∀ i, 0 < p i (x i)) (hp1 : ∀ i, p i (x i) < 1)
    (ell : ℝ) (hF : ∀ i, ‖fderiv ℝ (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (u : HomogeneousBlocks ι E) :
    bernoulliFisherEnergy (fun i => p i (x i))
      (fun i => fderiv ℝ (fun y : HomogeneousBlocks ι E => p i (y i)) x u) ≤ ell^2*‖u‖^2 := by
  unfold bernoulliFisherEnergy
  simp only [blockGate_fderiv p hp]
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply (div_le_iff₀ (mul_pos (hp0 i) (sub_pos.mpr (hp1 i)))).2
  have hd := (fderiv ℝ (p i) (x i)).le_opNorm (u i)
  have hd2 : (fderiv ℝ (p i) (x i) (u i))^2 ≤ ‖fderiv ℝ (p i) (x i)‖^2*‖u i‖^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hd
    simpa only [← pow_two, Real.norm_eq_abs, sq_abs, mul_pow] using hh
  have hh := mul_le_mul_of_nonneg_right (hF i) (sq_nonneg ‖u i‖)
  nlinarith

theorem blockGate_second_energy (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x : HomogeneousBlocks ι E) (h : ℝ) (hh : 0 ≤ h)
    (hH : ∀ i, ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ≤ h)
    (u v : HomogeneousBlocks ι E) :
    (∑ i, |secondBilinear (fun y : HomogeneousBlocks ι E => p i (y i)) x u v|) ≤ h*‖u‖*‖v‖ := by
  have hcs : (∑ i, ‖u i‖*‖v i‖) ≤ ‖u‖*‖v‖ := by
    have hs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖)
    simpa only [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)] using hs
  calc
    _ ≤ ∑ i, h*‖u i‖*‖v i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [blockGate_secondBilinear p hp]
      exact (secondBilinear_abs_le (x i) (u i) (v i)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hH i) (norm_nonneg _)) (norm_nonneg _))
    _ = h * ∑ i, ‖u i‖*‖v i‖ := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs hh

end
end SecondOrder
