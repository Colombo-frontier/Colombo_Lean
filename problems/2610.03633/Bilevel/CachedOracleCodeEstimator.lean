import Bilevel.CachedOracleCodePrimitive
import Bilevel.CachedEstimatorProcedure

/-! Public causal syntax for the actual cached two-solve estimator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode
open Stateful OracleCode
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)]

def untilted (μ Lg σg D r : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y) Y :=
  .reparam (amplify (tiltedSolve (X:=X) (Y:=Y) μ Lg σg 0 D (r/12)) q)
    (fun p : CachedEstimatorProcedure.Input X Y => ((p.1,(0:Y)),p.2.2.2)) (by fun_prop)

def tilted (μ Lg σg t D r : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y) Y :=
  .reparam (amplify (tiltedSolve (X:=X) (Y:=Y) μ Lg σg t D (r/12)) q)
    (fun p : CachedEstimatorProcedure.Input X Y => ((p.1,p.2.2.1),p.2.2.2)) (by fun_prop)

def solvePair (μ Lg σg t D r : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y) (Y × Y) :=
  .bind (untilted μ Lg σg D r q)
    (map (.reparam (tilted μ Lg σg t D r q) Prod.fst measurable_fst)
      (fun z => (z.1.2,z.2)) (by fun_prop))

def gxMean (σg δ : ℝ) (q : ℕ) [NeZero q] : Flow (X:=X) (Y:=Y) (X × Y) X :=
  amplify (gxBatch σg (δ/12)) q

def firstGradient (σg δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y × (Y × Y)) ((Y × Y) × X) :=
  map (.reparam (gxMean σg δ q) (fun z => (z.1.1,z.2.1)) (by fun_prop))
    (fun z => (z.1.2,z.2)) (by fun_prop)

def lastGradient (σg δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y × ((Y × Y) × X))
      (CachedEstimatorProcedure.Transcript X Y) :=
  map (.reparam (gxMean σg δ q) (fun z => (z.1.1,z.2.1.2)) (by fun_prop))
    (fun z => (z.1.2.1,(z.1.2.2,z.2))) (by fun_prop)

def transcript (μ Lg σg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y) (CachedEstimatorProcedure.Transcript X Y) :=
  .bind (.bind (solvePair μ Lg σg t D r q) (firstGradient σg δ q)) (lastGradient σg δ q)

def estimator (μ Lg σg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y) X :=
  map (transcript μ Lg σg t D r δ q) (fun z => CachedEstimatorProcedure.estimate t z.1 z.2)
    (by unfold CachedEstimatorProcedure.estimate; fun_prop)

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=Unit) (X:=X) (Y:=Y) σf σg)
  (K : Kernel (X × Y) (FullResponse X Y)) [IsMarkovKernel K]
  (hK : ∀ q,O.law (q,())=K q)

omit [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
include hK in
theorem denote_estimator (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    denote K (estimator (X:=X) (Y:=Y) μ Lg σg t D r δ q)=
      CachedEstimatorProcedure.estimator O μ Lg t D r δ q := by
  simp only [estimator,transcript,solvePair,untilted,tilted,firstGradient,lastGradient,gxMean,
    denote_map,denote,denote_amplify,denote_tiltedSolve O K hK,denote_gxBatch O K hK,
    CachedEstimatorProcedure.estimator,CachedEstimatorProcedure.transcript,CachedEstimatorProcedure.solvePair,
    CachedEstimatorProcedure.untilted,CachedEstimatorProcedure.tilted,CachedEstimatorProcedure.firstGradient,
    CachedEstimatorProcedure.lastGradient,CachedEstimatorProcedure.gxMean]

end Bilevel.CachedOracleCode
