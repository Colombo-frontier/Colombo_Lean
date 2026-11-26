import LowRank.GaussianSpectralMoments
import LowRank.InverseGramRealMoments
import LowRank.MeasurableEigenvector

/-! Measurable inverse Gram eigenvalues and their moment bounds. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem inverseGram_posSemidef {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ) :
    (inverseGram X).PosSemidef := by
  exact (show (Xᵀ * X).PosSemidef by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X).inv

def inverseGramEigenvalue {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ) (i : Fin s) : ℝ :=
  (orderedMatrixSpectrum (inverseGram_posSemidef X).isHermitian).value i

theorem inverseGramEigenvalue_nonneg {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ) (i : Fin s) :
    0 ≤ inverseGramEigenvalue X i :=
  (orderedMatrixSpectrum (inverseGram_posSemidef X).isHermitian).value_nonneg
    (inverseGram_posSemidef X) i

theorem measurable_inverseGramEigenvalue (d s : ℕ) (i : Fin s) :
    Measurable (fun X : Matrix (Fin d) (Fin s) ℝ => inverseGramEigenvalue X i) := by
  let f : Matrix (Fin d) (Fin s) ℝ → RealSymmetricMatrix s :=
    fun X => ⟨inverseGram X, (inverseGram_posSemidef X).isHermitian⟩
  have hf : Measurable f := (measurable_inverseGram d s).subtype_mk
  have hg : Measurable (fun A : RealSymmetricMatrix s => (orderedMatrixSpectrum A.2).value i) :=
    (continuous_ordered_eigenvalue (fun A : RealSymmetricMatrix s => A.1)
      (fun A => A.2) continuous_subtype_val i).measurable
  change Measurable ((fun A : RealSymmetricMatrix s => (orderedMatrixSpectrum A.2).value i) ∘ f)
  exact hg.comp hf

theorem inverseGramEigenvalue_moment_mul_le {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (i : Fin (s + 1)) {a : ℝ} (ha : 0 ≤ a)
    (hd : 0 < ((d - s : ℕ) : ℝ) / 2 - a) :
    (∫⁻ X, ENNReal.ofReal ((inverseGramEigenvalue X i) ^ a) ∂iidMatrixLaw d (s + 1) v) *
        ENNReal.ofReal (gaussianMomentFormula 1 a) ≤
      ENNReal.ofReal (gaussianMomentFormula (s + 1) a) *
        ENNReal.ofReal ((v : ℝ) ^ (-a) * gaussianMomentFormula (d - s) (-a)) := by
  have hmeas : Measurable (fun X : Matrix (Fin d) (Fin (s + 1)) ℝ =>
      ENNReal.ofReal ((inverseGramEigenvalue X i) ^ a)) :=
    ((measurable_inverseGramEigenvalue d (s + 1) i).pow_const a).ennreal_ofReal
  rw [← lintegral_mul_const _ hmeas]
  have hm : Measurable (fun p : Matrix (Fin d) (Fin (s + 1)) ℝ × (Fin (s + 1) → ℝ) =>
      ENNReal.ofReal ((p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) ^ a)) :=
    ((measurable_inverseGram_quadratic_pair d (s + 1)).pow_const a).ennreal_ofReal
  have hw : 0 < ((s + 1 : ℕ) : ℝ) / 2 + a := by positivity
  have hjoint := iidMatrixLaw_inverseGram_gaussian_real_moment hs hv 1 hd hw
  rw [lintegral_prod _ hm.aemeasurable] at hjoint
  simp only [NNReal.coe_one, Real.one_rpow, one_mul] at hjoint
  calc
    _ ≤ ∫⁻ X, ∫⁻ w : Fin (s + 1) → ℝ,
        ENNReal.ofReal ((w ⬝ᵥ (inverseGram X *ᵥ w)) ^ a) ∂iidVectorLaw (s + 1) 1
          ∂iidMatrixLaw d (s + 1) v := by
      apply lintegral_mono
      intro X
      exact iidVectorLaw_quadratic_spectral_moment (inverseGram_posSemidef X)
        (orderedMatrixSpectrum (inverseGram_posSemidef X).isHermitian) i ha
    _ = _ := hjoint

theorem inverseGramEigenvalue_moment_le {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (i : Fin (s + 1)) {a : ℝ} (ha : 0 ≤ a)
    (hd : 0 < ((d - s : ℕ) : ℝ) / 2 - a) :
    (∫⁻ X, ENNReal.ofReal ((inverseGramEigenvalue X i) ^ a) ∂iidMatrixLaw d (s + 1) v) ≤
      (ENNReal.ofReal (gaussianMomentFormula (s + 1) a) *
        ENNReal.ofReal ((v : ℝ) ^ (-a) * gaussianMomentFormula (d - s) (-a))) /
          ENNReal.ofReal (gaussianMomentFormula 1 a) := by
  have hpos : 0 < gaussianMomentFormula 1 a := by
    unfold gaussianMomentFormula
    apply div_pos
    · exact mul_pos (Real.rpow_pos_of_pos (by norm_num) a)
        (Real.Gamma_pos_of_pos (by norm_num; linarith))
    · exact Real.Gamma_pos_of_pos (by norm_num)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)))
    (Or.inl ENNReal.ofReal_ne_top)).2
  exact inverseGramEigenvalue_moment_mul_le hs hv i ha hd

end
end LowRank
