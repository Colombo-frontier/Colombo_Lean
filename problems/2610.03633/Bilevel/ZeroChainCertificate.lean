import Bilevel.ZeroChainThird

/-! The original chain facts, including the gap to the actual infimum. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainCertificate
open ZeroChain ZeroChainRegularity ZeroChainThird

theorem value_bddBelow (n : ℕ) : BddBelow (Set.range (value n)) := by
  refine ⟨-(phiBound + (n : ℝ)*(2*Real.exp 1*phiBound)), ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (abs_le.mp (value_abs_bound n z)).1

theorem gap_to_infimum (n : ℕ) :
    value n 0 - sInf (Set.range (value n)) ≤
      (1+2*Real.exp 1)*phiBound*(n+1 : ℕ) := by
  have hl : value n 0-(1+2*Real.exp 1)*phiBound*(n+1 : ℕ) ≤ sInf (Set.range (value n)) := by
    apply le_csInf (Set.range_nonempty (value n))
    rintro _ ⟨z, rfl⟩
    linarith [initial_gap_bound n z]
  linarith

theorem gradient_infinity_norm_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (z : Space n),
    ‖fun j : Fin (n+1) => gradient (value n) z j‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := coordinate_gradient_uniform_bound
  refine ⟨B, hB, fun n z => ?_⟩
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro j
  simpa only [Real.norm_eq_abs] using hb n z j

/-- A common numerical constant, independent of dimension, controls the gap,
gradient infinity norm, gradient Lipschitz constant and Hessian Lipschitz
constant of the exact chain. The endgame holds with the original threshold. -/
theorem universal_chain_certificate : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    ContDiff ℝ 3 (value n) ∧
    value n 0-sInf (Set.range (value n)) ≤ C*(n+1 : ℕ) ∧
    (∀ z : Space n, ‖fun j : Fin (n+1) => gradient (value n) z j‖ ≤ C) ∧
    (∀ x y : Space n, ‖gradient (value n) x-gradient (value n) y‖ ≤ C*‖x-y‖) ∧
    (∀ x y : Space n, ‖fderiv ℝ (gradient (value n)) x-fderiv ℝ (gradient (value n)) y‖ ≤ C*‖x-y‖) ∧
    (∀ z : Space n, |z (Fin.last n)| < 1 → 1 ≤ ‖gradient (value n) z‖) := by
  obtain ⟨B, hB, hb⟩ := gradient_infinity_norm_bound
  obtain ⟨L, hL⟩ := gradient_lipschitz_uniform
  obtain ⟨M, hM⟩ := hessian_lipschitz_uniform
  let A := (1+2*Real.exp 1)*phiBound
  have hA : 0 ≤ A := mul_nonneg (by positivity) phiBound_nonneg
  let C := 1+A+B+(L:ℝ)+(M:ℝ)
  have hC : 0 < C := by dsimp [C]; nlinarith [L.coe_nonneg, M.coe_nonneg]
  have hAC : A ≤ C := by dsimp [C]; linarith [L.coe_nonneg, M.coe_nonneg]
  have hBC : B ≤ C := by dsimp [C]; linarith [L.coe_nonneg, M.coe_nonneg]
  have hLC : (L:ℝ) ≤ C := by dsimp [C]; linarith [M.coe_nonneg]
  have hMC : (M:ℝ) ≤ C := by dsimp [C]; linarith [L.coe_nonneg]
  refine ⟨C, hC, fun n => ⟨value_contDiff n 3, ?_, ?_, ?_, ?_, endgame n⟩⟩
  · exact (gap_to_infimum n).trans (mul_le_mul_of_nonneg_right hAC (Nat.cast_nonneg _))
  · exact fun z => (hb n z).trans hBC
  · intro x y
    exact ((hL n).norm_sub_le x y).trans (mul_le_mul_of_nonneg_right hLC (norm_nonneg _))
  · intro x y
    exact ((hM n).norm_sub_le x y).trans (mul_le_mul_of_nonneg_right hMC (norm_nonneg _))

end Bilevel.ZeroChainCertificate
