import FreshGradientMinimax.TestingLower

/-! The complete D.1 witness statement, the nontrivial-regime specialization,
and the integer minimax lower bound. No hard-family premise is assumed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem theorem_D1 (p : Parameters) (hκ : 1120 * p.μ ≤ p.L) :
    ∃ F H : NCObjective 1 1 p.L p.μ,
      F.DualLocalized 0 ∧ H.DualLocalized 0 ∧
      F.PrimalGapAtMost (151424 * p.ε ^ 2 / (p.κ * p.L)) ∧
      H.PrimalGapAtMost (151424 * p.ε ^ 2 / (p.κ * p.L)) ∧
      ∀ (A : RandomizedAlgorithm 1 1) (N : ℕ),
        2 / 3 ≤ (A.outputLaw (FreshOracle.gaussianDual F p.σ).kernel N).real (F.successSet p.ε) →
        2 / 3 ≤ (A.outputLaw (FreshOracle.gaussianDual H p.σ).kernel N).real (H.successSet p.ε) →
        1 ≤ N ∧ (2 / (9 * 903168) : ℝ) * p.testing ≤ N := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hg (s : ℝ) (hs : |s| ≤ 1) :
      (testingHardObjective p hκ s hs).PrimalGapAtMost (151424 * p.ε ^ 2 / (p.κ * p.L)) := by
    intro x
    have h := testingObjective_gap_rate p.μ_pos (testingRadius_pos p.μ_pos hκ p.ε_pos)
      hκ p.ε_pos.le hs x
    convert h using 1
    unfold Parameters.κ
    field_simp [ne_of_gt p.μ_pos, ne_of_gt hL]
    ring
  refine ⟨testingHardObjective p hκ 1 (by norm_num),
    testingHardObjective p hκ (-1) (by norm_num),
    testingObjective_localized p.μ_pos _ hκ (by norm_num) (le_refl 0),
    testingObjective_localized p.μ_pos _ hκ (by norm_num) (le_refl 0),
    hg 1 (by norm_num), hg (-1) (by norm_num), ?_⟩
  intro A N hF hH
  exact ⟨testing_pair_positive p hκ A N hF hH, testing_pair_lower p hκ A N hF hH⟩

theorem testing_nontrivial_parameters (p : Parameters) (hκ : 8192 ≤ p.κ)
    (hg : 80 * p.ε ^ 2 ≤ p.L * p.gap) :
    1120 * p.μ ≤ p.L ∧ 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hh : 8192 * p.μ ≤ p.L := (le_div_iff₀ p.μ_pos).mp hκ
  refine ⟨by linarith [p.μ_pos], ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  have hs : 151424 * p.μ ≤ 80 * p.L := by linarith [p.μ_pos]
  have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg p.ε)
  have h2 := mul_le_mul_of_nonneg_left hg hL.le
  nlinarith only [h1, h2]

theorem testing_nontrivial_budget_lower (p : Parameters) (hκ : 8192 ≤ p.κ)
    (hg : 80 * p.ε ^ 2 ≤ p.L * p.gap) {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    1 ≤ N ∧ (2 / (9 * 903168) : ℝ) * p.testing ≤ N := by
  obtain ⟨hκ', hg'⟩ := testing_nontrivial_parameters p hκ hg
  exact ⟨testing_localized_budget_positive p hκ' hg' hN,
    testing_localized_budget_lower p hκ' hg' hN⟩

theorem testing_localized_complexity_lower (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hg : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap) :
    (⌈(2 / (9 * 903168) : ℝ) * p.testing⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast Nat.ceil_le.mpr (testing_localized_budget_lower p hκ hg N.property)

theorem testing_unlocalized_complexity_lower (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hg : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap) :
    (⌈(2 / (9 * 903168) : ℝ) * p.testing⌉₊ : ℕ∞) ≤ unlocalizedComplexity p :=
  (testing_localized_complexity_lower p hκ hg).trans (localized_complexity_le_unlocalized p)

end FreshGradientMinimax
