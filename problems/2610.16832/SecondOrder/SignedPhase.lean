import SecondOrder.EuclideanCoordinates
import SecondOrder.PeriodicBlock
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open scoped BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section
set_option maxHeartbeats 1200000

variable {d : ℕ}

def signedCos (θ : Fin d → Bool) (x : Point d) : Point d :=
  euclideanVector (fun i => signValue (θ i)*Real.cos (x i))
def signedSin (θ : Fin d → Bool) (x : Point d) : Point d :=
  euclideanVector (fun i => signValue (θ i)*Real.sin (x i))

@[simp] theorem signedCos_apply (θ : Fin d → Bool) (x : Point d) (i : Fin d) :
    signedCos θ x i = signValue (θ i)*Real.cos (x i) := rfl
@[simp] theorem signedSin_apply (θ : Fin d → Bool) (x : Point d) (i : Fin d) :
    signedSin θ x i = signValue (θ i)*Real.sin (x i) := rfl

theorem signedPhase_coordinate_sq (θ : Fin d → Bool) (x : Point d) (i : Fin d) :
    (signedCos θ x i)^2+(signedSin θ x i)^2 = 1 := by
  simp only [signedCos_apply, signedSin_apply, mul_pow, signValue_sq, one_mul]
  exact Real.cos_sq_add_sin_sq _

theorem signedPhase_norm_sq (θ : Fin d → Bool) (x : Point d) :
    ‖signedCos θ x‖^2+‖signedSin θ x‖^2 = d := by
  rw [euclidean_norm_sq, euclidean_norm_sq, ← Finset.sum_add_distrib]
  simp only [signedPhase_coordinate_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem signedCos_contDiff (θ : Fin d → Bool) (k : WithTop ℕ∞) : ContDiff ℝ k (signedCos θ) := by
  apply contDiff_coordinates
  intro i
  exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).contDiff.cos

theorem signedSin_contDiff (θ : Fin d → Bool) (k : WithTop ℕ∞) : ContDiff ℝ k (signedSin θ) := by
  apply contDiff_coordinates
  intro i
  exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).contDiff.sin

theorem signedCos_hasFDerivAt (θ : Fin d → Bool) (x : Point d) :
    HasFDerivAt (signedCos θ) (diagonalMap (-signedSin θ x)) x := by
  apply hasFDerivAt_coordinates
  intro i
  convert (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).hasFDerivAt).cos.const_mul (signValue (θ i))) using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply, diagonalMap_apply, PiLp.neg_apply, signedSin_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem signedSin_hasFDerivAt (θ : Fin d → Bool) (x : Point d) :
    HasFDerivAt (signedSin θ) (diagonalMap (signedCos θ x)) x := by
  apply hasFDerivAt_coordinates
  intro i
  convert (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).hasFDerivAt).sin.const_mul (signValue (θ i))) using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply, diagonalMap_apply, signedCos_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

def phaseCosMean (θ : Fin d → Bool) (x : Point d) : ℝ := (d:ℝ)⁻¹ * ∑ i, signedCos θ x i
def phaseSinMean (θ : Fin d → Bool) (x : Point d) : ℝ := (d:ℝ)⁻¹ * ∑ i, signedSin θ x i

theorem phaseCosMean_contDiff (θ : Fin d → Bool) (k : WithTop ℕ∞) : ContDiff ℝ k (phaseCosMean θ) :=
  contDiff_const.mul (ContDiff.sum (fun i _ => contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).contDiff.cos))

theorem phaseSinMean_contDiff (θ : Fin d → Bool) (k : WithTop ℕ∞) : ContDiff ℝ k (phaseSinMean θ) :=
  contDiff_const.mul (ContDiff.sum (fun i _ => contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).contDiff.sin))

theorem phaseCosMean_hasFDerivAt (θ : Fin d → Bool) (x : Point d) :
    HasFDerivAt (phaseCosMean θ)
      (-(d:ℝ)⁻¹ • InnerProductSpace.toDual ℝ (Point d) (signedSin θ x)) x := by
  have h := (HasFDerivAt.sum (x := x) (u := Finset.univ) (fun i _ =>
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).hasFDerivAt.cos).const_mul (signValue (θ i)))).const_mul (d:ℝ)⁻¹
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply, euclidean_inner, signedSin_apply, PiLp.proj_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem phaseSinMean_hasFDerivAt (θ : Fin d → Bool) (x : Point d) :
    HasFDerivAt (phaseSinMean θ)
      ((d:ℝ)⁻¹ • InnerProductSpace.toDual ℝ (Point d) (signedCos θ x)) x := by
  have h := (HasFDerivAt.sum (x := x) (u := Finset.univ) (fun i _ =>
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).hasFDerivAt.sin).const_mul (signValue (θ i)))).const_mul (d:ℝ)⁻¹
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply, euclidean_inner, signedCos_apply, PiLp.proj_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem phaseMean_eq_periodicMean {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    planarVector (phaseCosMean θ.1 x) (phaseSinMean θ.1 x) = periodicMean x θ := by
  congr 1 <;> simp [phaseCosMean, phaseSinMean, periodicMean, balancedVectorSum,
    signedCos_apply, signedSin_apply, div_eq_mul_inv, mul_comm]

end
end SecondOrder
