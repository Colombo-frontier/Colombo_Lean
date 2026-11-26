import LowRank.RefinedPairedKrylovAlgorithm
import LowRank.TailPowerBudget

/-! Each constituent Krylov space can certify the same combined output.
Capture monotonicity is used before converting to residual power. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem refinedPairedKrylovPolicy_power_of_capture {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : PairedKrylovSeed b s t) {Q : Matrix (Fin a) (Fin a) ℝ}
    (hQ : IsOrthogonalProjector Q) (hPQ : pairedKrylovProjector Aᵀ n r U * Q = Q)
    {p δ : ℝ} (hp : 1 ≤ p)
    (hc : schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) - δ ≤
      schattenPower p ((Aᵀ * Q) * optimalColumnSelector b a k hka (Aᵀ * Q))) :
    let Z := runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (refinedPairedKrylovPolicy a b k s t n r hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k + δ := by
  dsimp only
  rw [refinedPairedKrylovPolicy_run]
  exact refinedRitzColumns_residual_le_optimum_add_deficit hka hkb A
    (pairedKrylovProjector_isProjector Aᵀ n r U) hp
    (hc.trans (compressedRitz_power_mono_subspace hka Aᵀ hQ hPQ (by linarith : 0 < p)))

theorem refinedPairedKrylovPolicy_power_of_left_tail_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : PairedKrylovSeed b s t) {p γ L : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hU : U.1 ∈ krylovTailRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n hka γ L) :
    let Z := runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (refinedPairedKrylovPolicy a b k s t n r hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k +
      (k : ℝ) * (γ / 2) * L ^ (p / 2) := by
  apply refinedPairedKrylovPolicy_power_of_capture hka hkb A U (columnRangeProjector_isProjector _)
    (pairedKrylovProjector_absorbs_left Aᵀ n r U) hp
  exact optimalColumnSelector_tail_power_deficit hka Aᵀ _ (by linarith : 0 < p) hp2 hγ hL hhead hU

theorem refinedPairedKrylovPolicy_power_of_right_tail_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : PairedKrylovSeed b s t) {p γ L : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hU : U.2 ∈ krylovTailRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k t r hka γ L) :
    let Z := runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (refinedPairedKrylovPolicy a b k s t n r hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k +
      (k : ℝ) * (γ / 2) * L ^ (p / 2) := by
  apply refinedPairedKrylovPolicy_power_of_capture hka hkb A U (columnRangeProjector_isProjector _)
    (pairedKrylovProjector_absorbs_right Aᵀ n r U) hp
  exact optimalColumnSelector_tail_power_deficit hka Aᵀ _ (by linarith : 0 < p) hp2 hγ hL hhead hU

end
end LowRank
