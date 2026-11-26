import Matvec.RandomStart
import LowRank.GaussianInverseGramRotation
import Mathlib.Tactic

namespace Matvec
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
noncomputable section

def smallBallDensity : ℝ := gaussianPDFReal 0 1 1

theorem smallBallDensity_pos : 0 < smallBallDensity :=
  gaussianPDFReal_pos 0 1 1 (by norm_num)

theorem gaussian_density_lower_unit {x : ℝ} (hx : x ∈ Icc 0 1) :
    smallBallDensity ≤ gaussianPDFReal 0 1 x := by
  unfold smallBallDensity gaussianPDFReal
  norm_num only [NNReal.coe_one, sub_zero, one_pow, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [hx.1, hx.2]

theorem gaussian_small_interval_lower {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    smallBallDensity * u / 2 ≤ (gaussianReal 0 1).real (Icc (u / 2) u) := by
  have hconst : IntegrableOn (fun _ : ℝ => smallBallDensity) (Icc (u / 2) u) :=
    integrableOn_const.mpr (Or.inr (isCompact_Icc.measure_lt_top))
  have h := setIntegral_mono_on hconst (integrable_gaussianPDFReal 0 1).integrableOn
    measurableSet_Icc (fun x hx => gaussian_density_lower_unit
      (show x ∈ Icc 0 1 from ⟨by linarith [hx.1], hx.2.trans hu1⟩))
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith : u / 2 ≤ u)] at h
  have hnonneg : 0 ≤ ∫ x in Icc (u / 2) u, gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num),
    ENNReal.toReal_ofReal hnonneg]
  nlinarith

theorem square_inverse_diagonal_law (n : ℕ) (i : Fin (n + 1)) :
    (LowRank.iidMatrixLaw (n + 1) (n + 1) 1).map
      (fun X => LowRank.inverseGram X i i) =
      (LowRank.squaredGaussianLaw 1 1).map (fun t : ℝ => t⁻¹) := by
  have hu : (Pi.single i 1 : Fin (n + 1) → ℝ) ⬝ᵥ Pi.single i 1 = 1 := by simp
  have h := LowRank.iidMatrixLaw_inverseGram_unit_quadratic (d := n + 1) (s := n)
    (v := 1) (by omega) (by norm_num) (Pi.single i 1) hu
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

theorem square_inverse_diagonal_lower (n : ℕ) (i : Fin (n + 1))
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    smallBallDensity * u / 2 ≤
      (LowRank.iidMatrixLaw (n + 1) (n + 1) 1).real
        {X | (u ^ 2)⁻¹ ≤ LowRank.inverseGram X i i} := by
  letI : IsProbabilityMeasure (LowRank.iidVectorLaw 1 1) := LowRank.iidVectorLaw_probability _ _
  have hm : Measurable (fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      LowRank.inverseGram X i i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (LowRank.measurable_inverseGram (n + 1) (n + 1)))
  have h := congrArg (fun μ : Measure ℝ => μ (Ici ((u ^ 2)⁻¹)))
    (square_inverse_diagonal_law n i)
  dsimp only at h
  rw [Measure.map_apply hm measurableSet_Ici,
    Measure.map_apply measurable_inv measurableSet_Ici,
    LowRank.squaredGaussianLaw, Measure.map_apply (LowRank.measurable_dot_self 1)
      (measurableSet_Ici.preimage measurable_inv)] at h
  have heq : (LowRank.iidMatrixLaw (n + 1) (n + 1) 1).real
      {X | (u ^ 2)⁻¹ ≤ LowRank.inverseGram X i i} =
      (LowRank.iidVectorLaw 1 1).real {z | (u ^ 2)⁻¹ ≤ (z ⬝ᵥ z)⁻¹} := by
    exact congrArg ENNReal.toReal h
  rw [heq]
  have hinterval := congrArg ENNReal.toReal (RandomStart.gaussian_one_coordinate (Icc (u / 2) u))
  calc
    _ ≤ (gaussianReal 0 1).real (Icc (u / 2) u) := gaussian_small_interval_lower hu hu1
    _ = (LowRank.iidVectorLaw 1 1).real {z | z 0 ∈ Icc (u / 2) u} := hinterval.symm
    _ ≤ _ := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro z hz
      have hz0 : 0 < z 0 := by linarith [hz.1]
      have hsq : (z 0) ^ 2 ≤ u ^ 2 := by nlinarith [hz.2]
      simpa [dotProduct, pow_two] using inv_anti₀ (sq_pos_of_pos hz0) hsq

end
end Matvec
