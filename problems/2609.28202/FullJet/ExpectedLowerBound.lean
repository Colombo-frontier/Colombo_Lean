import FullJet.ExpectedAlgorithm

namespace FullJet

/-- Fixed loss in the accuracy rate when Markov capping uses tolerance 16ε. -/
noncomputable def expectedToleranceFactor (p : ℕ) : ℝ := (16 : ℝ) ^ (-(1 + 1 / (p : ℝ)))

theorem expectedToleranceFactor_pos (p : ℕ) : 0 < expectedToleranceFactor p := by
  unfold expectedToleranceFactor
  positivity

theorem expectedToleranceFactor_le_one (p : ℕ) : expectedToleranceFactor p ≤ 1 := by
  unfold expectedToleranceFactor
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have h : 0 ≤ 1 / (p : ℝ) := by positivity
  linarith

theorem fullRate_tolerance_scale_lower (p n : ℕ) (Δ L ε : ℝ) (hε : 0 < ε) :
    expectedToleranceFactor p * fullRate p n Δ L ε ≤ fullRate p n Δ L (16 * ε) := by
  have hn := mul_le_mul_of_nonneg_right (expectedToleranceFactor_le_one p) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  unfold fullRate accuracyRate accuracyWork
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hε.le]
  change expectedToleranceFactor p * (n + _ * (Δ * L ^ (1 / (p : ℝ)) * ε ^ (-(1 + 1 / (p : ℝ))))) ≤
    n + _ * (Δ * L ^ (1 / (p : ℝ)) * (expectedToleranceFactor p * ε ^ (-(1 + 1 / (p : ℝ)))))
  nlinarith only [hn]

noncomputable def expectedLowerCoefficient (p : ℕ) : ℝ :=
  mainLowerConstant p * expectedToleranceFactor p

theorem expectedLowerCoefficient_pos (p : ℕ) : 0 < expectedLowerCoefficient p :=
  mul_pos (mainLowerConstant_pos p) (expectedToleranceFactor_pos p)

noncomputable def expectedLowerConstant (p : ℕ) : ℝ := expectedLowerCoefficient p / 32

theorem expectedLowerConstant_pos (p : ℕ) : 0 < expectedLowerConstant p := by
  have := expectedLowerCoefficient_pos p
  unfold expectedLowerConstant
  positivity

/-- A p-dependent sample threshold absorbs integer capping and the harmless
positive slack Q+1, including the case Q=0. -/
noncomputable def expectedSampleThreshold (p : ℕ) : ℕ :=
  max largeSampleThreshold ⌈34 / expectedLowerCoefficient p⌉₊

theorem expectedSampleThreshold_pos (p : ℕ) : 0 < expectedSampleThreshold p := by
  have h : 0 < largeSampleThreshold := by norm_num [largeSampleThreshold, rowBudgetDivisor]
  exact h.trans_le (le_max_left _ _)

theorem expected_method_budget_lower {n p : ℕ} (M : RandomizedStoppingMethod n p)
    (hp : 2 ≤ p) (hn : expectedSampleThreshold p ≤ n) (Δ L Q ε : ℝ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hQ : 0 ≤ Q) (hε : 0 < ε)
    (hM : M.expectedGuarantee Δ L Q ε) :
    expectedLowerConstant p * fullRate p n Δ L ε ≤ Q := by
  have hcap := M.capped_succeeds hM (Q + 1) (1 / 8) (by linarith) (by positivity) hε (by norm_num)
  have he : ε / ((1 / 8 : ℝ) / 2) = 16 * ε := by ring
  have hR : (Q + 1) / ((1 / 8 : ℝ) / 2) = 16 * (Q + 1) := by ring
  rw [he, hR] at hcap
  have hlarge : largeSampleThreshold ≤ n := (le_max_left _ _).trans hn
  have hb := method_budget_lower M.capped hp hlarge Δ L (16 * ε) (1 / 8)
    hΔ hL (by positivity) (by norm_num) hcap
  have hscale := mul_le_mul_of_nonneg_left (fullRate_tolerance_scale_lower p n Δ L ε hε)
    (mainLowerConstant_pos p).le
  have hlower : expectedLowerCoefficient p * fullRate p n Δ L ε ≤ (⌈16 * (Q + 1)⌉₊ : ℝ) := by
    apply le_trans _ hb
    simpa only [expectedLowerCoefficient, mul_assoc] using hscale
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 16 * (Q + 1) by positivity)).le
  have hcoef := expectedLowerCoefficient_pos p
  have hcn : (⌈34 / expectedLowerCoefficient p⌉₊ : ℕ) ≤ n := (le_max_right _ _).trans hn
  have hfrac : 34 / expectedLowerCoefficient p ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcn)
  have h34 := (div_le_iff₀ hcoef).mp hfrac
  have hacc := mul_nonneg hcoef.le (accuracyRate_nonneg p n Δ L ε hΔ hL hε)
  have hfull : 34 ≤ expectedLowerCoefficient p * fullRate p n Δ L ε := by
    unfold fullRate
    nlinarith only [h34, hacc]
  unfold expectedLowerConstant
  nlinarith only [hlower, hceil, hfull]

theorem expectedOracleComplexity_lower (p n : ℕ) (hp : 2 ≤ p) (hn : expectedSampleThreshold p ≤ n)
    (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    ENNReal.ofReal (expectedLowerConstant p * fullRate p n Δ L ε) ≤
      expectedOracleComplexity n p Δ L ε := by
  apply le_sInf
  rintro b ⟨Q, M, hQ, rfl, hM⟩
  exact ENNReal.ofReal_le_ofReal (expected_method_budget_lower M hp hn Δ L Q ε hΔ hL hQ hε hM)

/-- The lower half of the expected-cost / expected-gradient corollary, for
actual stopping rules and with the source's confidence gap repaired. -/
theorem main_expected_complexity_lower_bound (p : ℕ) (hp : 2 ≤ p) :
    ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ 0 < n₀ ∧ ∀ n, n₀ ≤ n →
      ∀ (Δ L ε : ℝ), 0 < Δ → 0 < L → 0 < ε →
        ENNReal.ofReal (c * ((n : ℝ) + (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) *
          (Δ * L ^ (1 / (p : ℝ)) * ε ^ (-((p : ℝ) + 1) / p)))) ≤
            expectedOracleComplexity n p Δ L ε := by
  refine ⟨expectedLowerConstant p, expectedSampleThreshold p, expectedLowerConstant_pos p,
    expectedSampleThreshold_pos p, ?_⟩
  intro n hn Δ L ε hΔ hL hε
  simpa only [fullRate, accuracyRate, accuracyWork_eq_manuscript p (by omega)] using
    expectedOracleComplexity_lower p n hp hn Δ L ε hΔ hL hε

end FullJet
