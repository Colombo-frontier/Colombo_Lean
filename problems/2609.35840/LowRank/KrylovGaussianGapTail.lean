import LowRank.KrylovWeightedGap
import LowRank.GaussianStartingBlockBound

/-! A quantitative probability bound for the weighted error of the actual
Gaussian Krylov subspace. Its right side contains deterministic tail energy
and dimensions only; no random right-inverse condition remains. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem frobeniusSq_transpose {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    frobeniusSq Aᵀ = frobeniusSq A := by
  rw [frobeniusSq_eq_trace, Matrix.transpose_transpose, ← frobeniusSq_eq_trace_right]

theorem spectral_startingBlock_rows {a b k s : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (V : Matrix (Fin b) (Fin b) ℝ) (f : Fin k → Fin b) (U : Matrix (Fin a) (Fin s) ℝ) :
    (Vᵀ * (Aᵀ * U)).submatrix f id = (A * V.submatrix id f)ᵀ * U := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc]
  ext i j
  rfl

theorem krylov_gaussian_weighted_gap_tail {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : k + 2 ≤ s)
    {t γ η R S : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hR : 0 < R) (hS : 0 < S) (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    (iidMatrixLaw a s 1) {U |
      η ^ 2 * (R * S) <
        frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
          (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m)))))} ≤
      ENNReal.ofReal ((s : ℝ) * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k))) / ENNReal.ofReal R +
        ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) / ENNReal.ofReal S := by
  let V := positiveSpectralLeftColumns A sp (Fin.natAdd m)
  let M := (A * sp.basis.submatrix id (Fin.castAdd k))ᵀ
  have hp (j : Fin k) : 0 < sp.value (j.natAdd m) :=
    lt_of_lt_of_le (mul_pos ht (by linarith)) (hh j)
  have hV : Vᵀ * V = 1 :=
    positiveSpectralLeftColumns_orthogonal A sp (Fin.natAdd m) (Fin.natAddEmb m).injective hp
  have he := krylov_gaussian_weighted_gap_ae A sp (by omega : k ≤ s) ht hγ hγ1 hη hn hl hh
  have hsub : ∀ᵐ U ∂iidMatrixLaw a s 1,
      (η ^ 2 * (R * S) <
        frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
          (sp.basis.submatrix id (Fin.natAdd m) * diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m)))))) →
        R * S < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U)) := by
    filter_upwards [he] with U hU
    intro hbad
    rw [spectral_startingBlock_rows] at hU
    exact (mul_lt_mul_left (sq_pos_of_pos hη)).mp (hbad.trans_le hU)
  have hbound := iidMatrixLaw_startingBlock_factor_tail M V hV hs hR hS
  simp only [M, frobeniusSq_transpose] at hbound
  exact (measure_mono_ae hsub).trans hbound

end
end LowRank
