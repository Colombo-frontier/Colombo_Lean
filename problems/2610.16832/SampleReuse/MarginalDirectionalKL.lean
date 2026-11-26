import SampleReuse.MarginalGradientInformation

open SecondOrder InformationTheory MeasureTheory
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section

/-- Directed testing compares the positive and negative hypotheses, rather
than their average against a fair reference. -/
theorem coefficient_positive_negative_kl {R : ℝ} (hR : 2 ≤ R) :
    klDiv (coefficientPMF R 1 hR (by norm_num)).toMeasure
      (coefficientPMF R (-1) hR (by norm_num)).toMeasure ≤ ENNReal.ofReal (8/R^2) := by
  rw [klDiv_pmf _ _ (coefficientPMF_ne_zero R (-1) hR (by norm_num))]
  apply ENNReal.ofReal_le_ofReal
  rw [coefficientPMF,coefficientPMF,pmfKL_transport]
  have hu : pmfKL (biasedSignPMF R 1 hR (by norm_num)) (biasedSignPMF R (-1) hR (by norm_num)) ≤
      ∑ b : Bool, biasedSignMass R 1 b*(biasedSignMass R 1 b/biasedSignMass R (-1) b-1) := by
    unfold pmfKL
    apply Finset.sum_le_sum
    intro b _
    rw [biasedSignPMF_toReal,biasedSignPMF_toReal]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (biasedSignMass_pos hR (by norm_num) b)
        (biasedSignMass_pos hR (by norm_num) b)))
      (biasedSignMass_pos hR (by norm_num) b).le
  have h0 : R ≠ 0 := by linarith
  have h1 : R-1 ≠ 0 := by linarith
  have h2 : R+1 ≠ 0 := by linarith
  have hp : 0 < R^2-1 := by nlinarith
  have he : (∑ b : Bool, biasedSignMass R 1 b*(biasedSignMass R 1 b/biasedSignMass R (-1) b-1)) =
      4/(R^2-1) := by
    rw [Fintype.sum_bool]
    norm_num [biasedSignMass,signValue]
    field_simp [h0,h1,h2,hp.ne',show -1+R ≠ 0 by linarith,show 1+R ≠ 0 by linarith]
    ring_nf
    field_simp [show -1+R ≠ 0 by linarith]
    ring
  rw [he] at hu
  apply hu.trans
  apply (div_le_div_iff₀ hp (sq_pos_of_pos (by linarith : 0<R))).mpr
  nlinarith

end
end SampleReuse
