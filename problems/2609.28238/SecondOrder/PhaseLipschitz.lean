import SecondOrder.PeriodicBounds
import Mathlib.Analysis.Calculus.MeanValue

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

variable {d : ℕ}

theorem signedPhase_coordinate_abs_le (θ : Fin d → Bool) (x : Point d) (i : Fin d) :
    |signedCos θ x i| ≤ 1 ∧ |signedSin θ x i| ≤ 1 := by
  have h := signedPhase_coordinate_sq θ x i
  constructor <;> nlinarith [sq_nonneg (signedCos θ x i), sq_nonneg (signedSin θ x i),
    sq_abs (signedCos θ x i), sq_abs (signedSin θ x i), abs_nonneg (signedCos θ x i), abs_nonneg (signedSin θ x i)]

theorem signedPhase_norm_le_dim (θ : Fin d → Bool) (x : Point d) (hd : 0 < d) :
    ‖signedCos θ x‖ ≤ (d:ℝ) ∧ ‖signedSin θ x‖ ≤ (d:ℝ) := by
  have hD : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hh : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hs := signedPhase_norm_sq θ x
  constructor <;> nlinarith [sq_nonneg ‖signedCos θ x‖, sq_nonneg ‖signedSin θ x‖,
    norm_nonneg (signedCos θ x), norm_nonneg (signedSin θ x)]

theorem signedCos_lipschitz (θ : Fin d → Bool) (x y : Point d) :
    ‖signedCos θ y-signedCos θ x‖ ≤ ‖y-x‖ := by
  have hb (z : Point d) : ‖diagonalMap (-signedSin θ z)‖ ≤ 1 :=
    diagonalMap_norm_le _ (by norm_num) (fun i => by
      simpa only [PiLp.neg_apply, abs_neg] using (signedPhase_coordinate_abs_le θ z i).2)
  simpa only [one_mul] using Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z (_ : z ∈ Set.univ) => (signedCos_hasFDerivAt θ z).hasFDerivWithinAt)
    (fun z _ => hb z) (convex_univ : Convex ℝ (Set.univ : Set (Point d))) (Set.mem_univ x) (Set.mem_univ y)

theorem signedSin_lipschitz (θ : Fin d → Bool) (x y : Point d) :
    ‖signedSin θ y-signedSin θ x‖ ≤ ‖y-x‖ := by
  have hb (z : Point d) : ‖diagonalMap (signedCos θ z)‖ ≤ 1 :=
    diagonalMap_norm_le _ (by norm_num) (fun i => (signedPhase_coordinate_abs_le θ z i).1)
  simpa only [one_mul] using Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z (_ : z ∈ Set.univ) => (signedSin_hasFDerivAt θ z).hasFDerivWithinAt)
    (fun z _ => hb z) (convex_univ : Convex ℝ (Set.univ : Set (Point d))) (Set.mem_univ x) (Set.mem_univ y)

theorem phaseCosMean_derivative_bound (θ : Fin d → Bool) (x : Point d) (hd : 0 < d) :
    ‖fderiv ℝ (phaseCosMean θ) x‖ ≤ 1 := by
  rw [(phaseCosMean_hasFDerivAt θ x).fderiv,
    norm_smul (-(d:ℝ)⁻¹) (InnerProductSpace.toDual ℝ (Point d) (signedSin θ x)),
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ)⁻¹)]
  have h := mul_le_mul_of_nonneg_left (signedPhase_norm_le_dim θ x hd).2
    (by positivity : (0:ℝ) ≤ (d:ℝ)⁻¹)
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  simpa only [inv_mul_cancel₀ hD] using h

theorem phaseSinMean_derivative_bound (θ : Fin d → Bool) (x : Point d) (hd : 0 < d) :
    ‖fderiv ℝ (phaseSinMean θ) x‖ ≤ 1 := by
  rw [(phaseSinMean_hasFDerivAt θ x).fderiv,
    norm_smul ((d:ℝ)⁻¹) (InnerProductSpace.toDual ℝ (Point d) (signedCos θ x)),
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ)⁻¹)]
  have h := mul_le_mul_of_nonneg_left (signedPhase_norm_le_dim θ x hd).1
    (by positivity : (0:ℝ) ≤ (d:ℝ)⁻¹)
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  simpa only [inv_mul_cancel₀ hD] using h

theorem phaseCosMean_lipschitz (θ : Fin d → Bool) (hd : 0 < d) (x y : Point d) :
    |phaseCosMean θ y-phaseCosMean θ x| ≤ ‖y-x‖ := by
  simpa only [one_mul, Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => (phaseCosMean_hasFDerivAt θ z).differentiableAt)
    (fun z _ => phaseCosMean_derivative_bound θ z hd)
    (convex_univ : Convex ℝ (Set.univ : Set (Point d))) (Set.mem_univ x) (Set.mem_univ y)

theorem phaseSinMean_lipschitz (θ : Fin d → Bool) (hd : 0 < d) (x y : Point d) :
    |phaseSinMean θ y-phaseSinMean θ x| ≤ ‖y-x‖ := by
  simpa only [one_mul, Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => (phaseSinMean_hasFDerivAt θ z).differentiableAt)
    (fun z _ => phaseSinMean_derivative_bound θ z hd)
    (convex_univ : Convex ℝ (Set.univ : Set (Point d))) (Set.mem_univ x) (Set.mem_univ y)

theorem phaseMean_coordinates_le (θ : Fin d → Bool) (x : Point d) (hm : phaseMeanNorm θ x ≤ 1) :
    |phaseCosMean θ x| ≤ 1 ∧ |phaseSinMean θ x| ≤ 1 := by
  have hh : phaseMeanNorm θ x^2 ≤ 1 := by nlinarith [phaseMeanNorm_nonneg θ x]
  rw [phaseMeanNorm_sq] at hh
  constructor <;> nlinarith [sq_nonneg (phaseCosMean θ x), sq_nonneg (phaseSinMean θ x),
    sq_abs (phaseCosMean θ x), sq_abs (phaseSinMean θ x), abs_nonneg (phaseCosMean θ x), abs_nonneg (phaseSinMean θ x)]

end
end SecondOrder
