import Bilevel.CachedOracleCodeAnchor
import Bilevel.CachedOracleHistoryPrimitive
import Bilevel.CachedAnchorProcedure

/-! Public causal syntax for the executed lower solve and joint upper batch
which refresh the anchor cache. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode.History
open Stateful PrimitiveGeometry OracleCode
variable {X Y : Type} {H : OracleCode.Space}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=H) (X:=X) (Y:=Y) σf σg)

theorem denote_anchorRefresh (μ Lg Cf D rA η : ℝ) (q : ℕ) [NeZero q] :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (anchorRefresh (X:=X) (Y:=Y) μ Lg Cf σf σg D rA η q)=
      CachedAnchorProcedure.refresh O μ Lg Cf D rA η q := by
  simp only [anchorRefresh,anchorLower,anchorUpperAfter,anchorUpper,OracleCode.History.denote_map,OracleCode.History.denote,
    OracleCode.History.denote_amplify,denote_tiltedSolve O,denote_upperBatch O,
    CachedAnchorProcedure.refresh,CachedAnchorProcedure.refreshRaw,CachedAnchorProcedure.lower,
    CachedAnchorProcedure.upperAfter,CachedAnchorProcedure.upper]

end Bilevel.CachedOracleCode.History
