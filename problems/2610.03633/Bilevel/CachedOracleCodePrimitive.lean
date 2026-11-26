import Bilevel.OracleCodeAccelerated
import Bilevel.OracleCodeConfidence
import Bilevel.ParameterizedStatefulAcceleratedPrimitive
import Bilevel.StatefulJointBatch

/-! Public causal code for primitive cached-solver operations. Reads are
literal projections of one complete original full SFO reply. No oracle law,
truth, response minimizer or hidden instance occurs in these code definitions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode
open Stateful PrimitiveGeometry OracleCode
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

abbrev Flow (A B : Type) [MeasurableSpace A] [MeasurableSpace B] :=
  Code (of (X × Y)) (of (FullResponse X Y)) (of A) (of B)

def tiltedSolve (μ Lg σg t R r : ℝ) : Flow (X:=X) (Y:=Y) ((X × Y) × Y) Y :=
  acceleratedSolve (Param:=of (X × Y)) (fun z : FullResponse X Y => z.2.2) (by fun_prop)
    (fun z : (X × Y) × Y => (z.1.1,z.2)) (by fun_prop)
    (fun p : X × Y => t • p.2) (by fun_prop) μ Lg (Real.sqrt (μ/Lg)) σg R r

def gxBatch (σg radius : ℝ) : Flow (X:=X) (Y:=Y) (X × Y) X :=
  batch (fun z : FullResponse X Y => z.2.1) (by fun_prop) (FreshBatchKernel.count σg radius)

def upperBatch (σf radius : ℝ) : Flow (X:=X) (Y:=Y) (X × Y) (Joint X Y) :=
  batch (fun z : FullResponse X Y => pack z.1.1 z.1.2) (by
    exact (packLinear.continuous.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_fst)))) (FreshBatchKernel.count σf radius)

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=Unit) (X:=X) (Y:=Y) σf σg)
  (K : Kernel (X × Y) (FullResponse X Y)) [IsMarkovKernel K]
  (hK : ∀ q,O.law (q,())=K q)

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
include hK in
theorem denote_tiltedSolve (μ Lg t R r : ℝ) :
    denote K (tiltedSolve (X:=X) (Y:=Y) μ Lg σg t R r)=
      ParameterizedStatefulAccelerated.tiltedSolve O μ Lg t R r := by
  exact denote_acceleratedSolve (Q:=of (X × Y)) (O:=of (FullResponse X Y))
    (E:=Y) (Param:=of (X × Y))
    (fun z : (X × Y) × Y => (z.1.1,z.2)) (by fun_prop)
    (fun p : X × Y => t • p.2) (by fun_prop) K O.gy hK μ Lg (Real.sqrt (μ/Lg)) R r

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
include hK in
theorem denote_gxBatch (radius : ℝ) :
    denote K (gxBatch (X:=X) (Y:=Y) σg radius)=O.gx.batchAtRadius radius :=
  denote_batch (Q:=of (X × Y)) (O:=of (FullResponse X Y)) (E:=of X) K O.gx hK _

include hK in
theorem denote_upperBatch (radius : ℝ) :
    denote K (upperBatch (X:=X) (Y:=Y) σf radius)=O.fullUpper.batchAtRadius radius :=
  denote_batch (Q:=of (X × Y)) (O:=of (FullResponse X Y)) (E:=of (Joint X Y)) K O.fullUpper hK _

end Bilevel.CachedOracleCode
