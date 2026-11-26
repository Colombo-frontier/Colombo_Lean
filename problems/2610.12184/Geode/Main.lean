import Geode.ResistingOracle
import Geode.UpperAlgorithm
import Geode.StrictLocalization

/-! The manuscript's main matching-complexity theorem and strict-localization
corollary, proved for the actual hyperboloid and first-order oracle model. -/
namespace Geode.Lorentz

open scoped ENNReal

theorem uniformComplexity_lower {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (Geode.curvatureFactor R / (260 * ε ^ 2)) ≤
      uniformComplexity R L ε := by
  apply uniform_lower_of_failure_witness hR hL hε hεmax
  exact horizon_failure_witness origin hR hL hε hεmax
    (by rw [ambient_finrank_query_dimension])

/-- `thm:main`: the explicit dimension-uniform lower and upper bounds. -/
theorem matching_complexity {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (Geode.curvatureFactor R / (260 * ε ^ 2)) ≤ uniformComplexity R L ε ∧
      uniformComplexity R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞) :=
  ⟨uniformComplexity_lower hR hL hε hεmax, uniformComplexity_upper_three hR hL hε⟩

theorem matchingComplexityStatement_verified : MatchingComplexityStatement := by
  intro R L ε hR hL hε hεmax
  exact matching_complexity hR hL hε hεmax

/-- The precise lower assertion in dimension `T + 2`. -/
theorem main_precise_lower {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (A : FirstOrderAlgorithm (EuclideanSpace ℝ (Fin (Geode.queryHorizon R ε + 2)))) :
    ∃ (f : HyperbolicSpace (Geode.queryHorizon R ε + 2) → ℝ)
      (O : HyperbolicSpace (Geode.queryHorizon R ε + 2) →
        FirstOrderReply (EuclideanSpace ℝ (Fin (Geode.queryHorizon R ε + 2))))
      (p : HyperbolicSpace (Geode.queryHorizon R ε + 2)),
      AdmissibleObjective origin R L f ∧ LegalOracle f O ∧
      (∀ y, (∀ z, f y ≤ f z) ↔ y = p) ∧ f p = 0 ∧ dist origin p = R ∧
      Geode.OracleReplay.RunFails (fun output => 2 * ε * L * R ≤ f output - f p)
        (Geode.OracleReplay.run A (Geode.OracleReplay.fixedResponder O)
          (Geode.queryHorizon R ε) []) :=
  precise_failure_witness origin hR hL hε hεmax
    (by rw [ambient_finrank_query_dimension]) A

theorem strictUniformComplexity_lower {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (3 * Geode.curvatureFactor R / (1040 * ε ^ 2)) ≤
      strictUniformComplexity R L ε := by
  apply strictUniformComplexity_lower_of_failure_witness hR hL hε hεmax
  exact horizon_failure_witness origin (by linarith) hL hε hεmax
    (by rw [ambient_finrank_query_dimension])

/-- `cor:open-ball`: the same rate with the minimizer strictly inside the ball. -/
theorem strict_localization {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (3 * Geode.curvatureFactor R / (1040 * ε ^ 2)) ≤
        strictUniformComplexity R L ε ∧
      strictUniformComplexity R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞) :=
  ⟨strictUniformComplexity_lower hR hL hε hεmax, strictUniformComplexity_upper hR hL hε⟩

end Geode.Lorentz
