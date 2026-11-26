import LowRank.GapFreeKrylovRitz
import LowRank.GaussianStartingBlockConfidence

/-! A tunable failure probability for each Ritz value. A common tolerance
uses the ambient column dimension, so every target shares one Krylov run. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_gaussian_ritz_confidence_le {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {t γ η q : ℝ}
    (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ η < n)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m))
    (hbudget : η ^ 2 * (q ^ 2 * (s : ℝ) * (m : ℝ)) ≤ γ / 2) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ < t} ≤
          ENNReal.ofReal (2 / q) := by
  let V := positiveSpectralLeftColumns A sp (Fin.natAdd m)
  let M := spectralDeficitMatrix A sp (Fin.castAdd k) t
  have hp (j : Fin k) : 0 < sp.value (j.natAdd m) :=
    lt_of_lt_of_le (mul_pos ht (by linarith)) (hh j)
  have hV : Vᵀ * V = 1 :=
    positiveSpectralLeftColumns_orthogonal A sp (Fin.natAdd m) (Fin.natAddEmb m).injective hp
  have hsub : ∀ᵐ U ∂iidMatrixLaw a s 1,
      ((canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ < t) →
          q ^ 2 * (s : ℝ) * frobeniusSq M < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U)) := by
    filter_upwards [iidMatrixLaw_compressed_rightInverse_ae V hV (by omega : k ≤ s)
      (by norm_num : (1 : NNReal) ≠ 0)] with U hU
    intro hbad
    by_contra! hfactor
    exact (not_lt_of_ge (krylov_ritz_without_gap_of_factor_bound hk A U sp _ hU
      ht hγ hγ1 hη hn hh (sq_nonneg q) hfactor hbudget)) hbad
  exact (measure_mono_ae hsub).trans (iidMatrixLaw_startingBlock_confidence_le M V hV hs hq)

def confidentRitzTolerance (γ q : ℝ) (s d : ℕ) : ℝ :=
  Real.sqrt (γ / (2 * q ^ 2 * (s : ℝ) * ((d : ℝ) + 1)))

theorem confidentRitzTolerance_pos {γ q : ℝ} {s d : ℕ}
    (hγ : 0 < γ) (hq : 0 < q) (hs : 0 < s) :
    0 < confidentRitzTolerance γ q s d := by
  unfold confidentRitzTolerance
  positivity

theorem confidentRitzTolerance_budget {γ q : ℝ} {s m d : ℕ}
    (hγ : 0 ≤ γ) (hq : 0 < q) (hs : 0 < s) (hm : m ≤ d) :
    confidentRitzTolerance γ q s d ^ 2 * (q ^ 2 * (s : ℝ) * (m : ℝ)) ≤ γ / 2 := by
  have hd : 0 < 2 * q ^ 2 * (s : ℝ) * ((d : ℝ) + 1) := by positivity
  have he : confidentRitzTolerance γ q s d ^ 2 * (q ^ 2 * (s : ℝ) * ((d : ℝ) + 1)) = γ / 2 := by
    unfold confidentRitzTolerance
    rw [Real.sq_sqrt (div_nonneg hγ hd.le)]
    field_simp
    ring
  rw [← he]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ q ^ 2 * (s : ℝ))
  have hmd : (m : ℝ) ≤ d := by exact_mod_cast hm
  linarith

theorem krylov_gaussian_relative_ritz_confidence_le {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {γ q : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ q s (m + k)) < n) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ <
          sp.value ⟨m, by omega⟩ / (1 + γ / 2)} ≤ ENNReal.ofReal (2 / q) := by
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
    apply krylov_gaussian_ritz_confidence_le hk A sp hs (div_pos hp hd) hγ hγ1
      (confidentRitzTolerance_pos hγ hq (by omega : 0 < s)) hq hn
    · intro j
      rw [div_mul_cancel₀ _ (ne_of_gt hd)]
      exact sp.increasing (by change m ≤ m + j.val; omega)
    · exact confidentRitzTolerance_budget hγ.le hq (by omega : 0 < s) (by omega : m ≤ m + k)

theorem krylov_gaussian_ritz_index_confidence_le {a b s n : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (i : Fin b)
    (hs : 2 * (b - i.val) + 2 ≤ s) {γ q : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ q s b) < n) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum b (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value i <
          sp.value i / (1 + γ / 2)} ≤ ENNReal.ofReal (2 / q) := by
  rcases i with ⟨m, hm⟩
  obtain ⟨k, hb⟩ := Nat.exists_eq_add_of_le hm.le
  subst b
  exact krylov_gaussian_relative_ritz_confidence_le (by omega : 0 < k) A sp
    (by simpa only [Nat.add_sub_cancel_left] using hs) hγ hγ1 hq hn

end
end LowRank
