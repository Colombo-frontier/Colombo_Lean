import FullJet.OracleCandidate
import FullJet.ConstantSuccess
import FullJet.OracleComplexity

open MeasureTheory

namespace FullJet

noncomputable def upperQueryBudget (p n : ℕ) (Δ L ε : ℝ) (m B : ℕ) : ℕ :=
  upperEpochCount p Δ L ε m B * epochQueryCost n m B

/-- A genuine randomized method in the original oracle model. The seed has
the discrete sigma algebra, so its arbitrary internal model minimizations
create no measurable-selection requirement. -/
noncomputable def upperJetMethod (p n : ℕ) (hp : 1 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (m B : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) :
    RandomizedJetMethod n p := by
  letI : MeasurableSpace (UpperSeed p Δ L ε m B n) := ⊤
  exact {
    Seed := UpperSeed p Δ L ε m B n
    seedSpace := ⊤
    law := (upperSeedLaw p Δ L ε m B n hΔ hL hε hm hn).toMeasure
    probability := inferInstance
    algorithm := fun E _ _ _ => candidateJetAlgorithm hp ⟨0, hn⟩
      (upperModelScale p L m B) (upperRadius p L ε m B)
      (upperRadius_pos p L ε m B hL hε).le }

/-- Explicit fixed query budget and success probability for the actual
method, uniformly in every finite-dimensional real inner product space. -/
theorem upperJetMethod_succeeds (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (m B : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (hm : 0 < m) (hB : 0 < B) :
    (upperJetMethod p n (by omega) hn Δ L ε m B hΔ hL hε hm).succeeds
      (upperQueryBudget p n Δ L ε m B) Δ L ε (1 / 4) := by
  letI : MeasurableSpace (UpperSeed p Δ L ε m B n) := ⊤
  change ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    (candidateJetAlgorithm (E := E) (H := upperEpochCount p Δ L ε m B) (m := m) (B := B)
      (by omega) ⟨0, hn⟩ (upperModelScale p L m B) (upperRadius p L ε m B)
      (upperRadius_pos p L ε m B hL hε).le).succeeds
      (upperSeedLaw p Δ L ε m B n hΔ hL hε hm hn).toMeasure
      (upperEpochCount p Δ L ε m B * epochQueryCost n m B) Δ L ε (1 / 4)
  intro E _ _ _
  constructor
  · intro f hf
    exact measurable_of_finite _
  · intro f hf
    change ((upperSeedLaw p Δ L ε m B n hΔ hL hε hm hn).toMeasure
      {seed | ε < ‖fderiv ℝ (average f)
        ((candidateJetAlgorithm (by omega) ⟨0, hn⟩
          (upperModelScale p L m B) (upperRadius p L ε m B)
          (upperRadius_pos p L ε m B hL hε).le).result
            (upperEpochCount p Δ L ε m B * epochQueryCost n m B) f seed)‖}).toReal ≤ 1 / 4
    simp only [candidateJetAlgorithm_result]
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ _ (Set.toFinite _).measurableSet]
    exact hf.upperCandidate_failure_quarter hp hΔ hL hε m B hm hB

theorem oracleComplexity_constant_upper (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε : ℝ) (m B : ℕ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (hm : 0 < m) (hB : 0 < B) :
    oracleComplexity n p Δ L ε (1 / 4) ≤ upperQueryBudget p n Δ L ε m B :=
  oracleComplexity_le_of_method (upperJetMethod p n (by omega) hn Δ L ε m B hΔ hL hε hm)
    Δ L ε (1 / 4) (upperJetMethod_succeeds p n hp hn Δ L ε m B hΔ hL hε hm hB)

end FullJet
