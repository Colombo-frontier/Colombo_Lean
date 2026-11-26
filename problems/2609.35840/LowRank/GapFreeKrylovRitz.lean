import LowRank.SpectralDeficitEnergy
import LowRank.GaussianStartingBlockConstant

/-! A gap-independent probability bound for an actual compressed Gram
eigenvalue. The input may have repeated or zero eigenvalues. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_ritz_without_gap_of_factor_bound {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m))
    {C : ℝ} (hC : 0 ≤ C)
    (hfactor : frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R) ≤
      C * (s : ℝ) * frobeniusSq (spectralDeficitMatrix A sp (Fin.castAdd k) t))
    (hbudget : η ^ 2 * (C * (s : ℝ) * (m : ℝ)) ≤ γ / 2) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ := by
  have hh0 (j : Fin k) : t ≤ sp.value (j.natAdd m) := by
    have h := hh j
    nlinarith [mul_pos ht hγ]
  have hp (j : Fin k) : 0 < sp.value (j.natAdd m) := ht.trans_le (hh0 j)
  let c := fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))
  have hc (j : Fin k) : c j ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp j))
  have hinv : diagonal c * diagonal (fun j => (c j)⁻¹) = 1 := diagonal_mul_reciprocal c hc
  have hscaled : (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id *
      (R * diagonal (fun j => (c j)⁻¹)) = 1 := by
    rw [spectral_startingBlock_factor A sp (Fin.natAdd m) hp U]
    change (diagonal c * ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U)) *
      (R * diagonal (fun j => (c j)⁻¹)) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U),
      hR, Matrix.one_mul, hinv]
  apply krylov_ritz_lower_without_gap hk A U sp (R * diagonal (fun j => (c j)⁻¹))
    hscaled ht hγ hγ1 hη hn hh
  have htail := spectralDeficit_scaled_startingBlock_le A sp U R ht hh0
  have henergy := spectralDeficitMatrix_frobeniusSq_le A sp (Fin.castAdd k)
    (Fin.castAdd_injective m k) ht.le
  have hf := hfactor.trans (mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ C * (s : ℝ)))
  calc
    _ ≤ η ^ 2 * (t⁻¹ * frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R)) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg η)
    _ ≤ η ^ 2 * (t⁻¹ * (C * (s : ℝ) * ((m : ℝ) * t ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr ht.le)) (sq_nonneg η)
    _ = t * (η ^ 2 * (C * (s : ℝ) * (m : ℝ))) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget ht.le

theorem krylov_ritz_without_gap_of_factor {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m))
    (hfactor : frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R) ≤
      1600 * (s : ℝ) * frobeniusSq (spectralDeficitMatrix A sp (Fin.castAdd k) t))
    (hbudget : η ^ 2 * (1600 * (s : ℝ) * (m : ℝ)) ≤ γ / 2) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ :=
  krylov_ritz_without_gap_of_factor_bound hk A U sp R hR ht hγ hγ1 hη hn hh
    (by norm_num : (0 : ℝ) ≤ 1600) hfactor hbudget

theorem krylov_gaussian_ritz_without_gap_bad_le {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {t γ η : ℝ}
    (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m))
    (hbudget : η ^ 2 * (1600 * (s : ℝ) * (m : ℝ)) ≤ γ / 2) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ < t} ≤
          1 / 20 := by
  let V := positiveSpectralLeftColumns A sp (Fin.natAdd m)
  let M := spectralDeficitMatrix A sp (Fin.castAdd k) t
  have hp (j : Fin k) : 0 < sp.value (j.natAdd m) :=
    lt_of_lt_of_le (mul_pos ht (by linarith)) (hh j)
  have hV : Vᵀ * V = 1 :=
    positiveSpectralLeftColumns_orthogonal A sp (Fin.natAdd m) (Fin.natAddEmb m).injective hp
  have hsub : ∀ᵐ U ∂iidMatrixLaw a s 1,
      ((canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ < t) →
          1600 * (s : ℝ) * frobeniusSq M < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U)) := by
    filter_upwards [iidMatrixLaw_compressed_rightInverse_ae V hV (by omega : k ≤ s)
      (by norm_num : (1 : NNReal) ≠ 0)] with U hU
    intro hbad
    by_contra! hfactor
    exact (not_lt_of_ge (krylov_ritz_without_gap_of_factor hk A U sp _ hU ht hγ hγ1 hη hn hh
      hfactor hbudget)) hbad
  exact (measure_mono_ae hsub).trans (iidMatrixLaw_startingBlock_factor_bad_le M V hV hs)

def gapFreeRitzTolerance (γ : ℝ) (s m : ℕ) : ℝ :=
  Real.sqrt (γ / (3200 * (s : ℝ) * ((m : ℝ) + 1)))

theorem gapFreeRitzTolerance_pos {γ : ℝ} {s m : ℕ} (hγ : 0 < γ) (hs : 0 < s) :
    0 < gapFreeRitzTolerance γ s m := by
  unfold gapFreeRitzTolerance
  positivity

theorem gapFreeRitzTolerance_budget {γ : ℝ} {s m : ℕ} (hγ : 0 ≤ γ) (hs : 0 < s) :
    gapFreeRitzTolerance γ s m ^ 2 * (1600 * (s : ℝ) * (m : ℝ)) ≤ γ / 2 := by
  have hd : 0 < 3200 * (s : ℝ) * ((m : ℝ) + 1) := by positivity
  have he : gapFreeRitzTolerance γ s m ^ 2 * (1600 * (s : ℝ) * ((m : ℝ) + 1)) = γ / 2 := by
    unfold gapFreeRitzTolerance
    rw [Real.sq_sqrt (div_nonneg hγ hd.le)]
    field_simp
    ring
  rw [← he]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem krylov_gaussian_relative_ritz_without_gap_bad_le {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (gapFreeRitzTolerance γ s m) < n) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ <
          sp.value ⟨m, by omega⟩ / (1 + γ / 2)} ≤ 1 / 20 := by
  have hval := sp.value_nonneg (rightGram_posSemidef A) ⟨m, by omega⟩
  by_cases hz : sp.value ⟨m, by omega⟩ = 0
  · have he : {U : Matrix (Fin a) (Fin s) ℝ |
        (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ <
            sp.value ⟨m, by omega⟩ / (1 + γ / 2)} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro U hU
      rw [hz, zero_div] at hU
      exact (not_lt_of_ge ((canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value_nonneg
          (rightGram_posSemidef _) _)) hU
    rw [he, measure_empty]
    exact zero_le _
  · have hp : 0 < sp.value ⟨m, by omega⟩ := lt_of_le_of_ne hval (Ne.symm hz)
    have hd : 0 < 1 + γ / 2 := by linarith
    apply krylov_gaussian_ritz_without_gap_bad_le hk A sp hs (div_pos hp hd) hγ hγ1
      (gapFreeRitzTolerance_pos hγ (by omega : 0 < s)) hn
    · intro j
      rw [div_mul_cancel₀ _ (ne_of_gt hd)]
      exact sp.increasing (by change m ≤ m + j.val; omega)
    · exact gapFreeRitzTolerance_budget hγ.le (by omega : 0 < s)

end
end LowRank
