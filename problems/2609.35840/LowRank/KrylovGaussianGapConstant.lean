import LowRank.KrylovGaussianGapTail
import LowRank.GaussianStartingBlockConstant

/-! A concrete 95 percent weighted-subspace guarantee for the actual
oversampled Gaussian Krylov algorithm on a separated spectrum. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_gaussian_weighted_gap_bad_le {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : 2 * k + 2 ≤ s)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    (iidMatrixLaw a s 1) {U |
      η ^ 2 * (1600 * (s : ℝ) * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k))) <
        frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
          (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m)))))} ≤ 1 / 20 := by
  let V := positiveSpectralLeftColumns A sp (Fin.natAdd m)
  let M := (A * sp.basis.submatrix id (Fin.castAdd k))ᵀ
  have hp (j : Fin k) : 0 < sp.value (j.natAdd m) :=
    lt_of_lt_of_le (mul_pos ht (by linarith)) (hh j)
  have hV : Vᵀ * V = 1 :=
    positiveSpectralLeftColumns_orthogonal A sp (Fin.natAdd m) (Fin.natAddEmb m).injective hp
  have he := krylov_gaussian_weighted_gap_ae A sp (by omega : k ≤ s) ht hγ hγ1 hη hn hl hh
  have hsub : ∀ᵐ U ∂iidMatrixLaw a s 1,
      (η ^ 2 * (1600 * (s : ℝ) * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k))) <
        frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
          (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m)))))) →
        1600 * (s : ℝ) * frobeniusSq M < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U)) := by
    filter_upwards [he] with U hU
    intro hbad
    rw [spectral_startingBlock_rows] at hU
    simpa only [M, frobeniusSq_transpose] using
      (mul_lt_mul_left (sq_pos_of_pos hη)).mp (hbad.trans_le hU)
  exact (measure_mono_ae hsub).trans (iidMatrixLaw_startingBlock_factor_bad_le M V hV hs)

def weightedKrylovTolerance (ε : ℝ) (s : ℕ) : ℝ := Real.sqrt (ε / (1600 * (s : ℝ)))

theorem weightedKrylovTolerance_pos {ε : ℝ} {s : ℕ} (hε : 0 < ε) (hs : 0 < s) :
    0 < weightedKrylovTolerance ε s := by
  unfold weightedKrylovTolerance
  positivity

theorem weightedKrylovTolerance_sq {ε : ℝ} {s : ℕ} (hε : 0 ≤ ε) (hs : 0 < s) :
    weightedKrylovTolerance ε s ^ 2 * (1600 * (s : ℝ)) = ε := by
  unfold weightedKrylovTolerance
  rw [Real.sq_sqrt (by positivity)]
  exact div_mul_cancel₀ _ (by positivity)

theorem krylov_gaussian_weighted_relative_gap_bad_le {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hn : chebyshevFilterDegree γ (weightedKrylovTolerance ε s) < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    (iidMatrixLaw a s 1) {U |
      ε * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k)) <
        frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
          (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m)))))} ≤ 1 / 20 := by
  have hs0 : 0 < s := by omega
  have h := krylov_gaussian_weighted_gap_bad_le A sp hs ht hγ hγ1
    (weightedKrylovTolerance_pos hε hs0) hn hl hh
  simpa only [← mul_assoc, weightedKrylovTolerance_sq hε.le hs0] using h

theorem krylov_policy_weighted_relative_gap_bad_le {a m k s : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    let n := chebyshevFilterDegree γ (weightedKrylovTolerance ε s) + 1
    (iidMatrixLaw a s 1) {U |
      let data := runBoundedRectangular a (m + k) (krylovQueryBudget s 0 n)
        (krylovBlockPolicy a (m + k) s n) A U
      ε * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k)) <
        frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks data)) *
          (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m)))))} ≤ 1 / 20 := by
  dsimp only
  simp_rw [krylovBlockPolicy_run]
  exact krylov_gaussian_weighted_relative_gap_bad_le A sp hs ht hγ hγ1 hε (Nat.lt_succ_self _) hl hh

end
end LowRank
