import LowRank.WeightedGraphRayleigh
import LowRank.KrylovMatrixPolynomial

/-! Filtered graph candidates give actual Ritz-value lower bounds. Only
rows below the target value must be suppressed; no separation assumption
is placed on the remaining tail eigenvalues. -/

namespace LowRank
open Matrix Polynomial
open scoped Matrix BigOperators
noncomputable section

theorem weightedFrobeniusSq_diagonal_sandwich_le {m k : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (B : Matrix (Fin m) (Fin k) ℝ)
    (left : Fin m → ℝ) (right : Fin k → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i, 0 < w i → |left i| ≤ η) (hr : ∀ j, |right j| ≤ 1) :
    weightedFrobeniusSq w (diagonal left * B * diagonal right) ≤
      η ^ 2 * weightedFrobeniusSq w B := by
  simp only [weightedFrobeniusSq, Matrix.mul_diagonal, Matrix.diagonal_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hi : w i = 0
  · simp only [hi, zero_mul, mul_zero, le_refl]
  · have hwi : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
    have habs : |left i * B i j * right j| ≤ η * |B i j| := by
      rw [abs_mul, abs_mul]
      calc
        _ ≤ (η * |B i j|) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hl i hwi) (abs_nonneg _)) (hr j)
            (abs_nonneg _) (mul_nonneg hη (abs_nonneg _))
        _ = _ := mul_one _
    have hs := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg (left i * B i j * right j)) habs 2) (hw i)
    simpa only [sq_abs, mul_pow, mul_left_comm] using hs

theorem filteredTailBlock_deficit_bound {m k s : ℕ}
    (lam w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (R : Matrix (Fin s) (Fin k) ℝ) {t η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i : Fin m, lam (i.castAdd k) < t → |w (i.castAdd k)| ≤ η)
    (hh : ∀ j : Fin k, 1 ≤ w (j.natAdd m)) :
    weightedFrobeniusSq (fun i : Fin m => max 0 (t - lam (i.castAdd k)))
      (filteredTailBlock w B R) ≤
        η ^ 2 * weightedFrobeniusSq (fun i : Fin m => max 0 (t - lam (i.castAdd k)))
          (B.submatrix (Fin.castAdd k) id * R) := by
  apply weightedFrobeniusSq_diagonal_sandwich_le _ (fun _ => le_max_left _ _) _ _ _ hη
  · intro i hi
    apply hl i
    rcases lt_max_iff.mp hi with h | h
    · exact (lt_irrefl _ h).elim
    · linarith
  · intro j
    rw [abs_inv, abs_of_nonneg (by linarith [hh j] : 0 ≤ w (j.natAdd m))]
    exact inv_le_one_of_one_le₀ (hh j)

theorem filtered_ritz_lower_of_deficit {a m k s : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    {P : Matrix (Fin (m + k)) (Fin (m + k)) ℝ}
    (w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (R : Matrix (Fin s) (Fin k) ℝ) (hR : B.submatrix (Fin.natAdd m) id * R = 1)
    (hw : ∀ j : Fin k, w (j.natAdd m) ≠ 0)
    (hfix : P * (sp.basis * (diagonal w * B)) = sp.basis * (diagonal w * B))
    {t α : ℝ} (hh : ∀ j : Fin k, α ≤ sp.value (j.natAdd m))
    (hbudget : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      (filteredTailBlock w B R) ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A * P))).value ⟨m, by omega⟩ := by
  let Y := normalizedFilteredBlock w B R
  have hY : Y.submatrix (Fin.natAdd m) id = 1 := normalizedFilteredBlock_head w B R hR hw
  apply compressed_gram_eigenvalue_lower_of_candidate hk A (sp.basis * Y)
    (graphBlock_mulVec_injective sp.basis sp.orthogonal Y hY)
  · have h := congrArg (fun M => M * R * diagonal (fun j => (w (j.natAdd m))⁻¹)) hfix
    simpa only [Y, normalizedFilteredBlock, Matrix.mul_assoc] using h
  · intro x
    have hb : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
        (Y.submatrix (Fin.castAdd k) id) ≤ α - t := by
      simpa only [Y, normalizedFilteredBlock_tail] using hbudget
    have h := graphBlock_rayleigh_lower sp Y hY hh hb x
    have he := quadratic_coordinates A (1 : Matrix (Fin a) (Fin a) ℝ) ((sp.basis * Y) *ᵥ x)
    simp only [Matrix.one_mulVec, Matrix.mul_one] at he
    rw [he]
    exact h

theorem krylov_ritz_lower_of_filtered_deficit {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : ℝ[X]) (hf : f.natDegree < n)
    (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id * R = 1)
    (hw : ∀ j : Fin k, f.eval (sp.value (j.natAdd m)) ≠ 0)
    {t α : ℝ} (hh : ∀ j : Fin k, α ≤ sp.value (j.natAdd m))
    (hbudget : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      (filteredTailBlock (fun i => f.eval (sp.value i)) (sp.basisᵀ * (Aᵀ * U)) R) ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ := by
  apply filtered_ritz_lower_of_deficit hk A sp (fun i => f.eval (sp.value i))
    (sp.basisᵀ * (Aᵀ * U)) R hR hw _ hh hbudget
  have heq : aeval (Aᵀ * A) f * (Aᵀ * U) =
      sp.basis * (diagonal (fun i => f.eval (sp.value i)) * (sp.basisᵀ * (Aᵀ * U))) := by
    rw [sp.aeval_reconstruct f]
    simp only [Matrix.mul_assoc]
  rw [← heq]
  exact krylovProjector_fixes_aeval A U f hf

theorem krylov_ritz_lower_without_gap {a m k s n : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (R : Matrix (Fin s) (Fin k) ℝ)
    (hR : (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id * R = 1)
    {t γ η : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m))
    (hbudget : η ^ 2 * weightedFrobeniusSq
      (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
        ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id * R) ≤ t * (γ / 2)) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value ⟨m, by omega⟩ := by
  have hs := chebyshevGapFilter_spec ht hγ hγ1 hη
  let f := chebyshevGapFilter t γ (chebyshevFilterDegree γ η)
  have hfhead : ∀ j : Fin k, 1 ≤ f.eval (sp.value (j.natAdd m)) := fun j => hs.2.2 _ (hh j)
  apply krylov_ritz_lower_of_filtered_deficit hk A U sp f (hs.1.trans_lt hn) R hR
    (fun j => ne_of_gt (by linarith [hfhead j])) hh
  have h := filteredTailBlock_deficit_bound sp.value (fun i => f.eval (sp.value i))
    (sp.basisᵀ * (Aᵀ * U)) R hη.le
    (fun i hi => hs.2.1 _ (sp.value_nonneg (rightGram_posSemidef A) _) hi.le) hfhead
  have he : t * (1 + γ / 2) - t = t * (γ / 2) := by ring
  rw [he]
  exact h.trans hbudget

end
end LowRank
