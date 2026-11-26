import Bilevel.CachedOracleCodeEstimator
import Bilevel.CachedOracleHistoryPrimitive
import Bilevel.CachedEstimatorProcedure

/-! Public causal syntax for the actual cached two-solve estimator. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode.History
open Stateful OracleCode
variable {X Y : Type} {H : OracleCode.Space}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)]

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=H) (X:=X) (Y:=Y) σf σg)

omit [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem denote_estimator (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (estimator (X:=X) (Y:=Y) μ Lg σg t D r δ q)=
      CachedEstimatorProcedure.estimator O μ Lg t D r δ q := by
  simp only [estimator,transcript,solvePair,untilted,tilted,firstGradient,lastGradient,gxMean,
    OracleCode.History.denote_map,OracleCode.History.denote,OracleCode.History.denote_amplify,denote_tiltedSolve O,denote_gxBatch O,
    CachedEstimatorProcedure.estimator,CachedEstimatorProcedure.transcript,CachedEstimatorProcedure.solvePair,
    CachedEstimatorProcedure.untilted,CachedEstimatorProcedure.tilted,CachedEstimatorProcedure.firstGradient,
    CachedEstimatorProcedure.lastGradient,CachedEstimatorProcedure.gxMean]

end Bilevel.CachedOracleCode.History
