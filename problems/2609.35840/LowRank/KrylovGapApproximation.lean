import LowRank.KrylovMatrixPolynomial
import LowRank.FilteredGraphApproximation

/-! A deterministic gap-dependent error bound for the actual queried
Krylov subspace. The remaining starting-block factor is explicit; its
Gaussian probability estimate is not assumed to have been proved here. -/

namespace LowRank
open Matrix Polynomial
open scoped Matrix
noncomputable section

theorem krylov_filtered_residual_bound {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : ℝ[X]) (hf : f.natDegree < n)
    (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id * R = 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i : Fin m, |f.eval (sp.value (i.castAdd k))| ≤ η)
    (hh : ∀ j : Fin k, 1 ≤ f.eval (sp.value (j.natAdd m))) :
    frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
      sp.basis.submatrix id (Fin.natAdd m)) ≤
        η ^ 2 * frobeniusSq ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id * R) := by
  apply filtered_subspace_residual_bound sp.basis sp.orthogonal
    (columnRangeProjector_isProjector _) (fun i => f.eval (sp.value i))
    (sp.basisᵀ * (Aᵀ * U)) R hR _ hη hl hh
  have heq : aeval (Aᵀ * A) f * (Aᵀ * U) =
      sp.basis * (diagonal (fun i => f.eval (sp.value i)) * (sp.basisᵀ * (Aᵀ * U))) := by
    rw [sp.aeval_reconstruct f]
    simp only [Matrix.mul_assoc]
  rw [← heq]
  exact krylovProjector_fixes_aeval A U f hf

theorem krylov_gap_residual_bound {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id * R = 1)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
      sp.basis.submatrix id (Fin.natAdd m)) ≤
        η ^ 2 * frobeniusSq ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id * R) := by
  have hfilter := chebyshevGapFilter_spec ht hγ hγ1 hη
  apply krylov_filtered_residual_bound A U sp
    (chebyshevGapFilter t γ (chebyshevFilterDegree γ η)) (hfilter.1.trans_lt hn) R hR hη.le
  · intro i
    exact hfilter.2.1 _ (sp.value_nonneg (rightGram_posSemidef A) _) (hl i)
  · intro j
    exact hfilter.2.2 _ (hh j)

theorem krylov_policy_gap_residual_bound {a m k s : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id * R = 1)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    let n := chebyshevFilterDegree γ η + 1
    let data := runBoundedRectangular a (m + k) (krylovQueryBudget s 0 n)
      (krylovBlockPolicy a (m + k) s n) A U
    frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks data)) *
      sp.basis.submatrix id (Fin.natAdd m)) ≤
        η ^ 2 * frobeniusSq ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id * R) := by
  dsimp only
  rw [krylovBlockPolicy_run]
  exact krylov_gap_residual_bound A U sp R hR ht hγ hγ1 hη (Nat.lt_succ_self _) hl hh

theorem krylov_gap_query_count {a b s : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) :
    let n := chebyshevFilterDegree γ η + 1
    (((krylovBlockPolicy a b s n).toProgram a b (krylovQueryBudget s 0 n) U).calls
      (rectangularOracle A) : ℝ) ≤
        2 * (s : ℝ) * (2 * Real.log (2 / η) / Real.sqrt γ + 2) := by
  dsimp only
  rw [krylovBlockPolicy_calls]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * (s : ℝ))
  have h := chebyshevFilterDegree_le hγ hη hη1
  linarith

end
end LowRank
