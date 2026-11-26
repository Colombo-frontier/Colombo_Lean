import FullJet.ExpectedRestart
import FullJet.CertifiedTrial
import FullJet.UpperRate

open MeasureTheory
open scoped ENNReal

namespace FullJet

/-- A uniform stopping method driven by one fixed infinite stream of
independent finite seeds. Every attempt pays for generation and validation. -/
noncomputable def expectedJetMethod (p n : ℕ) (hp : 1 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) : RandomizedStoppingMethod n p := by
  letI : MeasurableSpace (UpperSeed p Δ L ε n 1 n) := ⊤
  exact {
    Seed := ℕ → UpperSeed p Δ L ε n 1 n
    seedSpace := inferInstance
    law := independentTrialLaw (upperSeedLaw p Δ L ε n 1 n hΔ hL hε hn hn).toMeasure
    probability := inferInstance
    algorithm := fun E _ _ _ => restartStoppingAlgorithm ⟨0, hn⟩
      (certifiedTrialProgram hp ⟨0, hn⟩ (upperModelScale p L n 1) (upperRadius p L ε n 1) ε
        (upperRadius_pos p L ε n 1 hL hε).le) }

theorem expectedJetMethod_guarantee (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    (expectedJetMethod p n (by omega) hn Δ L ε hΔ hL hε).expectedGuarantee
      Δ L (((upperQueryBudget p n Δ L ε n 1 : ℝ) + n) * (4 / 3)) ε := by
  letI : MeasurableSpace (UpperSeed p Δ L ε n 1 n) := ⊤
  change ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    (restartStoppingAlgorithm (E := E) ⟨0, hn⟩
      (certifiedTrialProgram (H := upperEpochCount p Δ L ε n 1) (m := n) (B := 1)
        (by omega) ⟨0, hn⟩ (upperModelScale p L n 1) (upperRadius p L ε n 1) ε
        (upperRadius_pos p L ε n 1 hL hε).le)).ExpectedGuarantee
      (independentTrialLaw (upperSeedLaw p Δ L ε n 1 n hΔ hL hε hn hn).toMeasure)
      Δ L (((upperQueryBudget p n Δ L ε n 1 : ℝ) + n) * (4 / 3)) ε
  intro E _ _ _
  rw [← Nat.cast_add]
  apply restartStoppingAlgorithm_expectedGuarantee
  · omega
  · intro a
    exact certifiedTrialProgram_uses _ _ _ _ _ _ a
  · intro f hf a x hx
    rw [eval_certifiedTrialProgram hf.smooth] at hx
    split at hx
    · have heq := Option.some.inj hx
      subst x
      assumption
    · cases hx
  · intro f hf
    change ((upperSeedLaw p Δ L ε n 1 n hΔ hL hε hn hn).toMeasure _).toReal ≤ _
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ _ (Set.toFinite _).measurableSet]
    simp only [eval_certifiedTrialProgram hf.smooth, ite_eq_right_iff, reduceCtorEq, imp_false, not_le]
    exact hf.upperCandidate_failure_quarter hp hΔ hL hε n 1 hn (by omega)

noncomputable def expectedUpperConstant (p : ℕ) : ℝ := (4 / 3) * mainUpperConstant p

theorem expectedUpperConstant_pos (p : ℕ) : 0 < expectedUpperConstant p := by
  have := mainUpperConstant_pos p
  unfold expectedUpperConstant
  positivity

theorem expectedOracleComplexity_upper (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    expectedOracleComplexity n p Δ L ε ≤ ENNReal.ofReal (expectedUpperConstant p * fullRate p n Δ L ε) := by
  have hm := expectedOracleComplexity_le_of_method
    (expectedJetMethod p n (by omega) hn Δ L ε hΔ hL hε) Δ L
    (((upperQueryBudget p n Δ L ε n 1 : ℝ) + n) * (4 / 3)) ε (by positivity)
    (expectedJetMethod_guarantee p n hp hn Δ L ε hΔ hL hε)
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right
    (upperQueryBudget_with_validation_le p n (by omega) hn Δ L ε hΔ hL hε) (by norm_num : (0 : ℝ) ≤ 4 / 3)
  unfold expectedUpperConstant
  nlinarith only [h]

end FullJet
