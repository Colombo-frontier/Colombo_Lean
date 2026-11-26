import Bilevel.CachedOracleCodePrimitive
import Bilevel.OracleHistoryAccelerated
import Bilevel.OracleHistoryConfidence

/-! The public primitive cached code denotes the exact full-history SFO
procedures, including the hidden updates after each original full sample. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode.History
open Stateful PrimitiveGeometry OracleCode
set_option autoImplicit false
variable {X Y : Type} {H : OracleCode.Space}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=H) (X:=X) (Y:=Y) σf σg)

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem denote_tiltedSolve (μ Lg t R r : ℝ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (tiltedSolve (X:=X) (Y:=Y) μ Lg σg t R r)=
      ParameterizedStatefulAccelerated.tiltedSolve O μ Lg t R r := by
  exact OracleCode.History.denote_acceleratedSolve
    (Q:=of (X × Y)) (O:=of (FullResponse X Y)) (E:=Y) (Param:=of (X × Y)) (H:=H)
    (fun z : (X × Y) × Y => (z.1.1,z.2)) (by fun_prop)
    (fun p : X × Y => t • p.2) (by fun_prop) O.gy μ Lg (Real.sqrt (μ/Lg)) R r

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem denote_gxBatch (radius : ℝ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (gxBatch (X:=X) (Y:=Y) σg radius)=O.gx.batchAtRadius radius :=
  OracleCode.History.denote_batch (Q:=of (X × Y)) (O:=of (FullResponse X Y))
    (E:=of X) (H:=H) O.gx _

theorem denote_upperBatch (radius : ℝ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (upperBatch (X:=X) (Y:=Y) σf radius)=O.fullUpper.batchAtRadius radius :=
  OracleCode.History.denote_batch (Q:=of (X × Y)) (O:=of (FullResponse X Y))
    (E:=of (Joint X Y)) (H:=H) O.fullUpper _

end Bilevel.CachedOracleCode.History
