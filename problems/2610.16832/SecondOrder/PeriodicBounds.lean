import SecondOrder.PeriodicCalculus
import SecondOrder.RankTwoDirection

open scoped BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

variable {d : ℕ}

def phaseMeanNorm (θ : Fin d → Bool) (x : Point d) : ℝ :=
  ‖planarVector (phaseCosMean θ x) (phaseSinMean θ x)‖

theorem phaseMeanNorm_sq (θ : Fin d → Bool) (x : Point d) :
    phaseMeanNorm θ x^2 = phaseCosMean θ x^2+phaseSinMean θ x^2 :=
  planarVector_norm_sq _ _

theorem phaseMeanNorm_nonneg (θ : Fin d → Bool) (x : Point d) : 0 ≤ phaseMeanNorm θ x := norm_nonneg _

theorem phaseDiagonal_coefficient_bound (θ : Fin d → Bool) (x : Point d) (i : Fin d) :
    |phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i| ≤ phaseMeanNorm θ x := by
  have hcs := signedPhase_coordinate_sq θ x i
  have hm := phaseMeanNorm_sq θ x
  have he :
      (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i)^2+
      (phaseCosMean θ x*signedSin θ x i-phaseSinMean θ x*signedCos θ x i)^2 =
      (phaseCosMean θ x^2+phaseSinMean θ x^2)*
      ((signedCos θ x i)^2+(signedSin θ x i)^2) := by ring
  rw [hcs, mul_one, ← hm] at he
  nlinarith [sq_abs (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i),
    sq_nonneg (phaseCosMean θ x*signedSin θ x i-phaseSinMean θ x*signedCos θ x i),
    abs_nonneg (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i), phaseMeanNorm_nonneg θ x]

theorem phaseGradient_coordinate_sq_bound (θ : Fin d → Bool) (x : Point d) (i : Fin d) :
    (phaseCosMean θ x*signedSin θ x i-phaseSinMean θ x*signedCos θ x i)^2 ≤ phaseMeanNorm θ x^2 := by
  have hcs := signedPhase_coordinate_sq θ x i
  have hm := phaseMeanNorm_sq θ x
  have he :
      (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i)^2+
      (phaseCosMean θ x*signedSin θ x i-phaseSinMean θ x*signedCos θ x i)^2 =
      (phaseCosMean θ x^2+phaseSinMean θ x^2)*
      ((signedCos θ x i)^2+(signedSin θ x i)^2) := by ring
  rw [hcs, mul_one, ← hm] at he
  nlinarith [sq_nonneg (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i)]

theorem phaseGradient_norm_sq_bound (θ : Fin d → Bool) (x : Point d) :
    ‖phaseGradient θ x‖^2 ≤ (d:ℝ)⁻¹*phaseMeanNorm θ x^2 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => phaseGradient_coordinate_sq_bound θ x i)
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (d:ℝ)⁻¹)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hm
  have he : ((d:ℝ)⁻¹)^2*(d:ℝ) = (d:ℝ)⁻¹ := by
    by_cases hd : (d:ℝ) = 0
    · simp [hd]
    · field_simp; ring
  simpa only [phaseGradient, euclidean_norm_sq, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul, mul_pow, ← Finset.mul_sum, ← mul_assoc, he] using hm

theorem phaseHessian_norm_bound (θ : Fin d → Bool) (x : Point d) :
    ‖phaseHessian θ x‖ ≤ (d:ℝ)⁻¹*(1+phaseMeanNorm θ x) := by
  have hd : 0 ≤ (d:ℝ)⁻¹ := by positivity
  have hdiag := diagonalMap_norm_le
    (phaseCosMean θ x • signedCos θ x+phaseSinMean θ x • signedSin θ x)
    (phaseMeanNorm_nonneg θ x) (fun i => phaseDiagonal_coefficient_bound θ x i)
  have hscale := norm_smul ((d:ℝ)⁻¹)
    (diagonalMap (phaseCosMean θ x • signedCos θ x+phaseSinMean θ x • signedSin θ x))
  have hsum : ‖(InnerProductSpace.toDual ℝ (Point d) (signedCos θ x)).smulRight (signedCos θ x)+
      (InnerProductSpace.toDual ℝ (Point d) (signedSin θ x)).smulRight (signedSin θ x)‖ ≤ (d:ℝ) := by
    have hn := norm_add_le
      ((InnerProductSpace.toDual ℝ (Point d) (signedCos θ x)).smulRight (signedCos θ x))
      ((InnerProductSpace.toDual ℝ (Point d) (signedSin θ x)).smulRight (signedSin θ x))
    simpa only [ContinuousLinearMap.norm_smulRight_apply, LinearIsometryEquiv.norm_map,
      ← sq, signedPhase_norm_sq] using hn
  have he : ((d:ℝ)⁻¹)^2*(d:ℝ) = (d:ℝ)⁻¹ := by
    by_cases hz : (d:ℝ) = 0
    · simp [hz]
    · field_simp; ring
  calc
    _ ≤ ‖-((d:ℝ)⁻¹)^2 •
      ((InnerProductSpace.toDual ℝ (Point d) (signedCos θ x)).smulRight (signedCos θ x)+
       (InnerProductSpace.toDual ℝ (Point d) (signedSin θ x)).smulRight (signedSin θ x))‖+
      ‖(d:ℝ)⁻¹ • diagonalMap (phaseCosMean θ x • signedCos θ x+phaseSinMean θ x • signedSin θ x)‖ := norm_add_le _ _
    _ ≤ ((d:ℝ)⁻¹)^2*(d:ℝ)+(d:ℝ)⁻¹*phaseMeanNorm θ x := by
      simp only [hscale, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg (d:ℝ)⁻¹), abs_of_nonneg hd]
      exact add_le_add (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)) (mul_le_mul_of_nonneg_left hdiag hd)
    _ = _ := by rw [he]; ring

theorem phaseHessian_negative (θ : Fin d → Bool) (x : Point d) (hd : 0 < d)
    (hm : phaseMeanNorm θ x ≤ 1/4) :
    ∃ v : Point d, ‖v‖ = 1 ∧ ⟪hessian (phasePotential θ) x v,v⟫_ℝ ≤ -1/(4*(d:ℝ)) := by
  have hD : (0:ℝ) < d := by exact_mod_cast hd
  rw [hessian_phasePotential]
  apply two_vector_negative_direction (signedCos θ x) (signedSin θ x) (phaseHessian θ x)
    hD (signedPhase_norm_sq θ x)
  intro v
  rw [phaseHessian_quadratic]
  apply add_le_add_left
  have hs : (∑ i, (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i)*(v i)^2) ≤
      (1/4)*‖v‖^2 := by
    rw [euclidean_norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((phaseDiagonal_coefficient_bound θ x i).trans hm)) (sq_nonneg _)
  have ht := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hD.le)
  convert ht using 1 <;> ring

theorem periodicBlockPotential_gradient_sq_bound {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    ‖gradient (periodicBlockPotential θ) x‖^2 ≤ ((2*m:ℕ):ℝ)⁻¹ := by
  rw [periodicBlockPotential_gradient]
  have hm : phaseMeanNorm θ.1 x ≤ 1 := by
    rw [phaseMeanNorm, phaseMean_eq_periodicMean]
    exact periodicMean_norm_le_one x θ
  have hsq : phaseMeanNorm θ.1 x^2 ≤ 1 := by nlinarith [phaseMeanNorm_nonneg θ.1 x]
  exact (phaseGradient_norm_sq_bound θ.1 x).trans (by
    simpa using mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ ((2*m:ℕ):ℝ)⁻¹))

theorem periodicBlockPotential_hessian_bound {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    ‖hessian (periodicBlockPotential θ) x‖ ≤ 2/((2*m:ℕ):ℝ) := by
  rw [periodicBlockPotential_hessian]
  have hm : phaseMeanNorm θ.1 x ≤ 1 := by
    rw [phaseMeanNorm, phaseMean_eq_periodicMean]
    exact periodicMean_norm_le_one x θ
  apply (phaseHessian_norm_bound θ.1 x).trans
  have h := mul_le_mul_of_nonneg_left (show 1+phaseMeanNorm θ.1 x ≤ 2 by linarith)
    (by positivity : (0:ℝ) ≤ ((2*m:ℕ):ℝ)⁻¹)
  convert h using 1 <;> ring

/-- The original periodic block has a unit direction of curvature at most -1/(4D). -/
theorem periodicBlockPotential_negative {m : ℕ} (θ : BalancedVector m) (x : Point (2*m))
    (hm : 0 < m) (hsmall : ‖periodicMean x θ‖ ≤ 1/4) :
    ∃ v : Point (2*m), ‖v‖ = 1 ∧
      ⟪hessian (periodicBlockPotential θ) x v,v⟫_ℝ ≤ -1/(4*((2*m:ℕ):ℝ)) := by
  rw [periodicBlockPotential_eq]
  apply phaseHessian_negative θ.1 x (by omega)
  simpa only [phaseMeanNorm, phaseMean_eq_periodicMean] using hsmall

end
end SecondOrder
