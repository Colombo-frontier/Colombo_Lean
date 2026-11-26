import SecondOrder.SignedPhase

open scoped BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

variable {d : ℕ}

def phasePotential (θ : Fin d → Bool) (x : Point d) : ℝ :=
  -(phaseCosMean θ x^2+phaseSinMean θ x^2)/2

def phaseGradient (θ : Fin d → Bool) (x : Point d) : Point d :=
  (d:ℝ)⁻¹ • (phaseCosMean θ x • signedSin θ x-phaseSinMean θ x • signedCos θ x)

def phaseHessian (θ : Fin d → Bool) (x : Point d) : Point d →L[ℝ] Point d :=
  -((d:ℝ)⁻¹)^2 •
    ((InnerProductSpace.toDual ℝ (Point d) (signedCos θ x)).smulRight (signedCos θ x)+
     (InnerProductSpace.toDual ℝ (Point d) (signedSin θ x)).smulRight (signedSin θ x))+
  (d:ℝ)⁻¹ • diagonalMap (phaseCosMean θ x • signedCos θ x+phaseSinMean θ x • signedSin θ x)

theorem phasePotential_contDiff (θ : Fin d → Bool) (k : WithTop ℕ∞) :
    ContDiff ℝ k (phasePotential θ) :=
  (((phaseCosMean_contDiff θ k).pow 2).add ((phaseSinMean_contDiff θ k).pow 2)).neg.div_const 2

theorem phaseGradient_contDiff (θ : Fin d → Bool) (k : WithTop ℕ∞) :
    ContDiff ℝ k (phaseGradient θ) :=
  (((phaseCosMean_contDiff θ k).smul (signedSin_contDiff θ k)).sub
    ((phaseSinMean_contDiff θ k).smul (signedCos_contDiff θ k))).const_smul _

theorem phasePotential_hasGradientAt (θ : Fin d → Bool) (x : Point d) :
    HasGradientAt (phasePotential θ) (phaseGradient θ x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (((phaseCosMean_hasFDerivAt θ x).mul (phaseCosMean_hasFDerivAt θ x)).add
    ((phaseSinMean_hasFDerivAt θ x).mul (phaseSinMean_hasFDerivAt θ x))).neg.const_mul (1/2:ℝ) using 1
  · funext y; simp [phasePotential, pow_two, div_eq_mul_inv, mul_comm]
  ext v
  simp only [phaseGradient, InnerProductSpace.toDual_apply, inner_smul_left,
    inner_sub_left, map_sub, map_smul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, smul_eq_mul, RCLike.conj_to_real]
  norm_num
  ring

theorem gradient_phasePotential (θ : Fin d → Bool) : gradient (phasePotential θ) = phaseGradient θ :=
  funext (fun x => (phasePotential_hasGradientAt θ x).gradient)

theorem phaseGradient_hasFDerivAt (θ : Fin d → Bool) (x : Point d) :
    HasFDerivAt (phaseGradient θ) (phaseHessian θ x) x := by
  have h := (((phaseCosMean_hasFDerivAt θ x).smul (signedSin_hasFDerivAt θ x)).sub
    ((phaseSinMean_hasFDerivAt θ x).smul (signedCos_hasFDerivAt θ x))).const_smul (d:ℝ)⁻¹
  convert h using 1
  ext v i
  simp only [phaseHessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply, PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply,
    PiLp.neg_apply, diagonalMap_apply, smul_eq_mul]
  ring

/-- Identification with the true Hessian, not an assumed matrix field. -/
theorem hessian_phasePotential (θ : Fin d → Bool) (x : Point d) :
    hessian (phasePotential θ) x = phaseHessian θ x := by
  rw [hessian, gradient_phasePotential]
  exact (phaseGradient_hasFDerivAt θ x).fderiv

theorem phaseHessian_quadratic (θ : Fin d → Bool) (x v : Point d) :
    ⟪phaseHessian θ x v,v⟫_ℝ =
      -((d:ℝ)⁻¹)^2*(⟪signedCos θ x,v⟫_ℝ^2+⟪signedSin θ x,v⟫_ℝ^2)+
      (d:ℝ)⁻¹*∑ i, (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i)*(v i)^2 := by
  simp only [phaseHessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply,
    inner_add_left, inner_smul_left, diagonalMap_inner, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, RCLike.conj_to_real]
  ring

theorem phasePotential_eq_periodicPotential {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    phasePotential θ.1 x = periodicPotential x θ := by
  rw [periodicPotential, ← phaseMean_eq_periodicMean θ x, planarVector_norm_sq]
  rfl

/-- The source potential, now viewed on the Euclidean normed space of query points. -/
def periodicBlockPotential {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) : ℝ :=
  periodicPotential x θ

theorem periodicBlockPotential_eq {m : ℕ} (θ : BalancedVector m) :
    periodicBlockPotential θ = phasePotential θ.1 :=
  funext (fun x => (phasePotential_eq_periodicPotential θ x).symm)

theorem periodicBlockPotential_contDiff {m : ℕ} (θ : BalancedVector m) (k : WithTop ℕ∞) :
    ContDiff ℝ k (periodicBlockPotential θ) := by
  rw [periodicBlockPotential_eq]
  exact phasePotential_contDiff _ k

theorem periodicBlockPotential_gradient {m : ℕ} (θ : BalancedVector m) :
    gradient (periodicBlockPotential θ) = phaseGradient θ.1 := by
  rw [periodicBlockPotential_eq, gradient_phasePotential]

theorem periodicBlockPotential_hessian {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    hessian (periodicBlockPotential θ) x = phaseHessian θ.1 x := by
  rw [periodicBlockPotential_eq, hessian_phasePotential]

end
end SecondOrder
