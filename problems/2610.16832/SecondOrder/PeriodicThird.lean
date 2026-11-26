import SecondOrder.PhaseLipschitz
import SecondOrder.RankOnePerturbation
import SecondOrder.LocalHessian

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

private theorem product_change_bound {a b c d R : ℝ}
    (ha : |a| ≤ 1) (hd : |d| ≤ 1) (hab : |a-b| ≤ R) (hcd : |c-d| ≤ R) :
    |a*c-b*d| ≤ 2*R := by
  have he : a*c-b*d = a*(c-d)+(a-b)*d := by ring
  rw [he]
  calc
    _ ≤ |a*(c-d)|+|(a-b)*d| := abs_add _ _
    _ = |a| *|c-d|+|a-b| *|d| := by rw [abs_mul, abs_mul]
    _ ≤ 1*R+R*1 := add_le_add
      (mul_le_mul ha hcd (abs_nonneg _) (by norm_num))
      (mul_le_mul hab hd (abs_nonneg _) (by linarith [abs_nonneg (a-b)]))
    _ = _ := by ring

variable {d : ℕ}

def phaseDiagonal (θ : Fin d → Bool) (x : Point d) : Point d :=
  phaseCosMean θ x • signedCos θ x+phaseSinMean θ x • signedSin θ x

theorem phaseDiagonal_lipschitz (θ : Fin d → Bool) (hd : 0 < d)
    (hm : ∀ x, phaseMeanNorm θ x ≤ 1) (x y : Point d) :
    ‖diagonalMap (phaseDiagonal θ y)-diagonalMap (phaseDiagonal θ x)‖ ≤ 4*‖y-x‖ := by
  rw [diagonalMap_sub]
  apply diagonalMap_norm_le _ (by positivity)
  intro i
  have hc : |signedCos θ y i-signedCos θ x i| ≤ ‖y-x‖ := by
    have h := (PiLp.norm_apply_le (signedCos θ y-signedCos θ x) i).trans (signedCos_lipschitz θ x y)
    simpa only [Real.norm_eq_abs, PiLp.sub_apply] using h
  have hs : |signedSin θ y i-signedSin θ x i| ≤ ‖y-x‖ := by
    have h := (PiLp.norm_apply_le (signedSin θ y-signedSin θ x) i).trans (signedSin_lipschitz θ x y)
    simpa only [Real.norm_eq_abs, PiLp.sub_apply] using h
  have hpc := product_change_bound (phaseMean_coordinates_le θ y (hm y)).1
    (signedPhase_coordinate_abs_le θ x i).1 (phaseCosMean_lipschitz θ hd x y) hc
  have hps := product_change_bound (phaseMean_coordinates_le θ y (hm y)).2
    (signedPhase_coordinate_abs_le θ x i).2 (phaseSinMean_lipschitz θ hd x y) hs
  change |(phaseCosMean θ y*signedCos θ y i+phaseSinMean θ y*signedSin θ y i)-
    (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i)| ≤ _
  have he : (phaseCosMean θ y*signedCos θ y i+phaseSinMean θ y*signedSin θ y i)-
    (phaseCosMean θ x*signedCos θ x i+phaseSinMean θ x*signedSin θ x i) =
    (phaseCosMean θ y*signedCos θ y i-phaseCosMean θ x*signedCos θ x i)+
    (phaseSinMean θ y*signedSin θ y i-phaseSinMean θ x*signedSin θ x i) := by ring
  rw [he]
  exact (abs_add _ _).trans (by linarith)

theorem phaseRankTwo_lipschitz (θ : Fin d → Bool) (hd : 0 < d) (x y : Point d) :
    ‖(rankOneMap (signedCos θ y)-rankOneMap (signedCos θ x))+
      (rankOneMap (signedSin θ y)-rankOneMap (signedSin θ x))‖ ≤ 4*(d:ℝ)*‖y-x‖ := by
  have hc : ‖rankOneMap (signedCos θ y)-rankOneMap (signedCos θ x)‖ ≤ (2*(d:ℝ))*‖y-x‖ :=
    (rankOneMap_sub_norm _ _).trans (mul_le_mul
      (by linarith [(signedPhase_norm_le_dim θ y hd).1, (signedPhase_norm_le_dim θ x hd).1])
      (signedCos_lipschitz θ x y) (norm_nonneg _) (by positivity))
  have hs : ‖rankOneMap (signedSin θ y)-rankOneMap (signedSin θ x)‖ ≤ (2*(d:ℝ))*‖y-x‖ :=
    (rankOneMap_sub_norm _ _).trans (mul_le_mul
      (by linarith [(signedPhase_norm_le_dim θ y hd).2, (signedPhase_norm_le_dim θ x hd).2])
      (signedSin_lipschitz θ x y) (norm_nonneg _) (by positivity))
  exact (norm_add_le _ _).trans (by linarith)

theorem phaseHessian_lipschitz (θ : Fin d → Bool) (hd : 0 < d)
    (hm : ∀ x, phaseMeanNorm θ x ≤ 1) (x y : Point d) :
    ‖phaseHessian θ y-phaseHessian θ x‖ ≤ (8/(d:ℝ))*‖y-x‖ := by
  let A := (rankOneMap (signedCos θ y)-rankOneMap (signedCos θ x))+
    (rankOneMap (signedSin θ y)-rankOneMap (signedSin θ x))
  let B := diagonalMap (phaseDiagonal θ y)-diagonalMap (phaseDiagonal θ x)
  have he : phaseHessian θ y-phaseHessian θ x = -((d:ℝ)⁻¹)^2 • A+(d:ℝ)⁻¹ • B := by
    simp only [phaseHessian, rankOneMap, phaseDiagonal, A, B, smul_add, smul_sub]
    module
  rw [he]
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  calc
    _ ≤ ‖-((d:ℝ)⁻¹)^2 • A‖+‖(d:ℝ)⁻¹ • B‖ := norm_add_le _ _
    _ = ((d:ℝ)⁻¹)^2*‖A‖+(d:ℝ)⁻¹*‖B‖ := by
      rw [norm_smul (-((d:ℝ)⁻¹)^2) A, norm_smul ((d:ℝ)⁻¹) B]
      simp only [Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg (d:ℝ)⁻¹),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ)⁻¹)]
    _ ≤ ((d:ℝ)⁻¹)^2*(4*(d:ℝ)*‖y-x‖)+(d:ℝ)⁻¹*(4*‖y-x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (phaseRankTwo_lipschitz θ hd x y) (sq_nonneg _))
        (mul_le_mul_of_nonneg_left (phaseDiagonal_lipschitz θ hd hm x y) (by positivity))
    _ = _ := by field_simp; ring

theorem periodicBlockPotential_hessian_lipschitz {m : ℕ} (θ : BalancedVector m) (hm : 0 < m)
    (x y : Point (2*m)) :
    ‖hessian (periodicBlockPotential θ) y-hessian (periodicBlockPotential θ) x‖ ≤
      (8/((2*m:ℕ):ℝ))*‖y-x‖ := by
  simp only [periodicBlockPotential_hessian]
  apply phaseHessian_lipschitz θ.1 (by omega)
  intro z
  rw [phaseMeanNorm, phaseMean_eq_periodicMean]
  exact periodicMean_norm_le_one z θ

theorem norm_third_eq_norm_fderiv_hessian (f : Point d → ℝ) (x : Point d) :
    ‖iteratedFDeriv ℝ 3 f x‖ = ‖fderiv ℝ (hessian f) x‖ := by
  unfold hessian
  rw [← norm_first_iteratedFDeriv, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_gradient]

theorem periodicBlockPotential_third_bound {m : ℕ} (θ : BalancedVector m) (hm : 0 < m)
    (x : Point (2*m)) : ‖iteratedFDeriv ℝ 3 (periodicBlockPotential θ) x‖ ≤ 8/((2*m:ℕ):ℝ) := by
  rw [norm_third_eq_norm_fderiv_hessian]
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  exact Filter.Eventually.of_forall (fun y => periodicBlockPotential_hessian_lipschitz θ hm x y)

end
end SecondOrder
