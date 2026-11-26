import LowRank.GaussianOracleTranscript

/-! Unit directions throughout an enlarged-history Gaussian policy. A
compiled visible unit policy satisfies this property on every state. -/

namespace LowRank
open MeasureTheory
noncomputable section
universe u

def GaussianPolicy.IsUnit (r s : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    GaussianPolicy r s n S → Prop
  | 0, _, _, _ => True
  | n + 1, _, _, policy =>
      (∀ x, ‖(basisCoordinates (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ)).symm
        (policy.1.1 x)‖ = 1) ∧ GaussianPolicy.IsUnit r s n policy.2

theorem compileVisibleOracle_unit (d t r s n q : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : VisibleOraclePolicy d r n q T)
    (st : MeasurableStateMap S (FactorData d t q (r + n) (s + n))) (mem : MeasurableStateMap S T)
    (hunit : VisibleOraclePolicy.IsUnit d r n q policy) :
    GaussianPolicy.IsUnit r s n (compileVisibleOracle d t r s n q policy st mem) := by
  induction n generalizing q S T with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro x
      exact hunit.1 (mem.1 x, visibleFactorData (st.1 x))
    · exact ih (q + 1) policy.2 _ _ hunit.2

theorem compileGramOracle_unit (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) :
    GaussianPolicy.IsUnit r s n (compileGramOracle r s n policy) :=
  compileVisibleOracle_unit _ _ _ _ _ _ policy _ _ hunit

end
end LowRank
