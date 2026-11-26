import LowRank.InverseGramSpectralMoments
import LowRank.GramSpectrum

/-! Deterministic conversion from an inverse Gram upper bound to a
Wishart lower bound on the complement of the explicit kernel projector. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem inverseGram_le_top {d s : ℕ} (X : Matrix (Fin d) (Fin (s + 1)) ℝ) :
    LoewnerLE (inverseGram X) ((inverseGramEigenvalue X (Fin.last s)) • 1) := by
  let sp := orderedMatrixSpectrum (inverseGram_posSemidef X).isHermitian
  exact (sp.loewner_interval (a := 0) (b := inverseGramEigenvalue X (Fin.last s))
    (fun i => ⟨sp.value_nonneg (inverseGram_posSemidef X) i,
      sp.increasing (Fin.le_last i)⟩)).2

theorem wishart_lower_of_inverseGram_le {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ)
    {R : ℝ} (hR : 0 < R) (hX : LoewnerLE (inverseGram X) (R • 1)) :
    LoewnerLE (R⁻¹ • (1 - leftKernelProjector X)) (wishart X) := by
  have h := loewner_congruence hX Xᵀ
  simp only [Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one] at h
  have hc := psd_smul h (inv_nonneg.mpr hR.le)
  change (R⁻¹ • (R • (X * Xᵀ) - X * inverseGram X * Xᵀ)).PosSemidef at hc
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hR.ne', one_smul] at hc
  simpa only [LoewnerLE, wishart, leftKernelProjector, sub_sub_cancel, inverseGram] using hc

theorem wishart_lower_of_inverseGram_top_le {d s : ℕ}
    (X : Matrix (Fin d) (Fin (s + 1)) ℝ) {R : ℝ} (hR : 0 < R)
    (hX : inverseGramEigenvalue X (Fin.last s) ≤ R) :
    LoewnerLE (R⁻¹ • (1 - leftKernelProjector X)) (wishart X) := by
  apply wishart_lower_of_inverseGram_le X hR
  let sp := orderedMatrixSpectrum (inverseGram_posSemidef X).isHermitian
  exact (sp.loewner_interval (a := 0) (b := R)
    (fun i => ⟨sp.value_nonneg (inverseGram_posSemidef X) i,
      (sp.increasing (Fin.le_last i)).trans hX⟩)).2

theorem wishart_lower_bad_le_inverseGram_tail {d s : ℕ}
    (μ : Measure (Matrix (Fin d) (Fin (s + 1)) ℝ)) {R : ℝ} (hR : 0 < R) :
    μ {X | ¬LoewnerLE (R⁻¹ • (1 - leftKernelProjector X)) (wishart X)} ≤
      μ {X | R < inverseGramEigenvalue X (Fin.last s)} := by
  apply measure_mono
  intro X hX
  exact lt_of_not_ge (fun h => hX (wishart_lower_of_inverseGram_top_le X hR h))

end
end LowRank
