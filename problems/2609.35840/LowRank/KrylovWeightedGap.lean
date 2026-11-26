import LowRank.KrylovGapApproximation
import LowRank.PositiveSpectralLeftColumns
import LowRank.GaussianRightInverse

/-! Singular-value-weighted error in the actual Krylov subspace. The right
inverse is taken of standard Gaussian left coordinates, so no inverse
singular values remain in the residual bound. -/

namespace LowRank
open Matrix Polynomial MeasureTheory
open scoped Matrix
noncomputable section

theorem krylov_scaled_filtered_residual_bound {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : ℝ[X]) (hf : f.natDegree < n)
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m)) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i : Fin m, |f.eval (sp.value (i.castAdd k))| ≤ η)
    (hh : ∀ j : Fin k, 1 ≤ f.eval (sp.value (j.natAdd m))) :
    frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
      (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) ≤
        η ^ 2 * frobeniusSq ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id * R) := by
  apply filtered_scaled_residual_bound sp.basis sp.orthogonal (columnRangeProjector_isProjector _)
    (fun i => f.eval (sp.value i)) (sp.basisᵀ * (Aᵀ * U))
    ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) R
    (fun j => Real.sqrt (sp.value (j.natAdd m)))
    (fun j => ne_of_gt (Real.sqrt_pos.mpr (hp j)))
    (spectral_startingBlock_factor A sp (Fin.natAdd m) hp U) hR _ hη hl hh
  have heq : aeval (Aᵀ * A) f * (Aᵀ * U) =
      sp.basis * (diagonal (fun i => f.eval (sp.value i)) * (sp.basisᵀ * (Aᵀ * U))) := by
    rw [sp.aeval_reconstruct f]
    simp only [Matrix.mul_assoc]
  rw [← heq]
  exact krylovProjector_fixes_aeval A U f hf

theorem krylov_scaled_gap_residual_bound {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
      (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) ≤
        η ^ 2 * frobeniusSq ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id * R) := by
  have hfilter := chebyshevGapFilter_spec ht hγ hγ1 hη
  have hp (j : Fin k) : 0 < sp.value (j.natAdd m) :=
    lt_of_lt_of_le (mul_pos ht (by linarith)) (hh j)
  apply krylov_scaled_filtered_residual_bound A U sp
    (chebyshevGapFilter t γ (chebyshevFilterDegree γ η)) (hfilter.1.trans_lt hn) hp R hR hη.le
  · intro i
    exact hfilter.2.1 _ (sp.value_nonneg (rightGram_posSemidef A) _) (hl i)
  · intro j
    exact hfilter.2.2 _ (hh j)

theorem krylov_gaussian_weighted_gap_ae {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : k ≤ s)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    ∀ᵐ U ∂iidMatrixLaw a s 1,
      frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
        (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) ≤
          η ^ 2 * frobeniusSq ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id *
            gramRightInverse ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U)) := by
  have hp (j : Fin k) : 0 < sp.value (j.natAdd m) :=
    lt_of_lt_of_le (mul_pos ht (by linarith)) (hh j)
  have hV := positiveSpectralLeftColumns_orthogonal A sp (Fin.natAdd m) (Fin.natAddEmb m).injective hp
  filter_upwards [iidMatrixLaw_compressed_rightInverse_ae _ hV hs (by norm_num : (1 : NNReal) ≠ 0)] with U hU
  exact krylov_scaled_gap_residual_bound A U sp _ hU ht hγ hγ1 hη hn hl hh

end
end LowRank
