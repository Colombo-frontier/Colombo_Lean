import LowRank.InverseGramWishartBound

/-! Moment-based probability bounds for inverse Gram eigenvalues and the
lower positive Wishart spectral event. Constants remain explicit Gamma ratios. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem inverseGramEigenvalue_tail_le {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (i : Fin (s + 1)) {a R : ℝ} (ha : 0 ≤ a)
    (hd : 0 < ((d - s : ℕ) : ℝ) / 2 - a) (hR : 0 < R) :
    (iidMatrixLaw d (s + 1) v) {X | R < inverseGramEigenvalue X i} ≤
      ((ENNReal.ofReal (gaussianMomentFormula (s + 1) a) *
        ENNReal.ofReal ((v : ℝ) ^ (-a) * gaussianMomentFormula (d - s) (-a))) /
          ENNReal.ofReal (gaussianMomentFormula 1 a)) / ENNReal.ofReal (R ^ a) := by
  have hm : Measurable (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ =>
      ENNReal.ofReal ((inverseGramEigenvalue X i) ^ a)) :=
    ((measurable_inverseGramEigenvalue d (s + 1) i).pow_const a).ennreal_ofReal
  have hmarkov := meas_ge_le_lintegral_div (μ := iidMatrixLaw d (s + 1) v) hm.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR a))) ENNReal.ofReal_ne_top
  calc
    _ ≤ (iidMatrixLaw d (s + 1) v) {X | ENNReal.ofReal (R ^ a) ≤
        ENNReal.ofReal ((inverseGramEigenvalue X i) ^ a)} := by
      apply measure_mono
      intro X hX
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hR.le hX.le ha)
    _ ≤ (∫⁻ X, ENNReal.ofReal ((inverseGramEigenvalue X i) ^ a)
        ∂iidMatrixLaw d (s + 1) v) / ENNReal.ofReal (R ^ a) := hmarkov
    _ ≤ _ := by
      simp only [div_eq_mul_inv]
      exact mul_le_mul_right' (inverseGramEigenvalue_moment_le hs hv i ha hd) _

theorem wishart_lower_bad_le_gamma_bound {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) {a R : ℝ} (ha : 0 ≤ a)
    (hd : 0 < ((d - s : ℕ) : ℝ) / 2 - a) (hR : 0 < R) :
    (iidMatrixLaw d (s + 1) v)
        {X | ¬LoewnerLE (R⁻¹ • (1 - leftKernelProjector X)) (wishart X)} ≤
      ((ENNReal.ofReal (gaussianMomentFormula (s + 1) a) *
        ENNReal.ofReal ((v : ℝ) ^ (-a) * gaussianMomentFormula (d - s) (-a))) /
          ENNReal.ofReal (gaussianMomentFormula 1 a)) / ENNReal.ofReal (R ^ a) :=
  (wishart_lower_bad_le_inverseGram_tail _ hR).trans
    (inverseGramEigenvalue_tail_le hs hv (Fin.last s) ha hd hR)

end
end LowRank
