import SecondOrder.BlockGateEnergies

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- Coordinate projection on a finite L2 product of possibly different spaces. -/
def dependentBlockProj (i : ι) : PiLp 2 E →L[ℝ] E i :=
  PiLp.proj (𝕜 := ℝ) 2 E i

@[simp] theorem dependentBlockProj_apply (i : ι) (x : PiLp 2 E) :
    dependentBlockProj i x = x i := rfl

theorem dependentBlockGate_fderiv (p : (i : ι) → E i → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x u : PiLp 2 E) (i : ι) :
    fderiv ℝ (fun y : PiLp 2 E => p i (y i)) x u = fderiv ℝ (p i) (x i) (u i) := by
  change fderiv ℝ (p i ∘ dependentBlockProj i) x u = _
  rw [fderiv_comp x ((hp i).differentiable (by norm_num) _) (dependentBlockProj i).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, dependentBlockProj_apply]

theorem dependentBlockGate_secondBilinear (p : (i : ι) → E i → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x u v : PiLp 2 E) (i : ι) :
    secondBilinear (fun y : PiLp 2 E => p i (y i)) x u v =
      secondBilinear (p i) (x i) (u i) (v i) :=
  secondBilinear_comp_linear (hp i) (dependentBlockProj i) x u v

/-- Disjoint blocks turn individual Fisher bounds into one energy bound without
introducing the number of blocks. -/
theorem dependentBlockGate_fisher_energy (p : (i : ι) → E i → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x : PiLp 2 E) (hp0 : ∀ i, 0 < p i (x i)) (hp1 : ∀ i, p i (x i) < 1)
    (ell : ℝ) (hF : ∀ i, ‖fderiv ℝ (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (u : PiLp 2 E) :
    bernoulliFisherEnergy (fun i => p i (x i))
      (fun i => fderiv ℝ (fun y : PiLp 2 E => p i (y i)) x u) ≤ ell^2*‖u‖^2 := by
  unfold bernoulliFisherEnergy
  simp only [dependentBlockGate_fderiv p hp]
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

theorem dependentBlockGate_second_energy (p : (i : ι) → E i → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x : PiLp 2 E) (h : ℝ) (hh : 0 ≤ h)
    (hH : ∀ i, ‖fderiv ℝ (fderiv ℝ (p i)) (x i)‖ ≤ h)
    (u v : PiLp 2 E) :
    (∑ i, |secondBilinear (fun y : PiLp 2 E => p i (y i)) x u v|) ≤ h*‖u‖*‖v‖ := by
  have hcs : (∑ i, ‖u i‖*‖v i‖) ≤ ‖u‖*‖v‖ := by
    have hs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖)
    simpa only [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)] using hs
  calc
    _ ≤ ∑ i, h*‖u i‖*‖v i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [dependentBlockGate_secondBilinear p hp]
      exact (secondBilinear_abs_le (x i) (u i) (v i)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hH i) (norm_nonneg _)) (norm_nonneg _))
    _ = h * ∑ i, ‖u i‖*‖v i‖ := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs hh

end
end SecondOrder
