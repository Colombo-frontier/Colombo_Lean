import Bilevel.PolishedCodeCalls

/-! Exact pointwise original-call counts of the implemented cached primitives.
No law or accuracy hypothesis is used. -/
noncomputable section
open MeasureTheory
namespace Bilevel.CachedOracleCode
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure
variable {X Y Seed : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  (response : (X × Y) → Seed → FullResponse X Y)

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [BorelSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem tiltedSolve_exactCalls (μ Lg σg t R r : ℝ) :
    ExactCalls response (tiltedSolve μ Lg σg t R r)
      (StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg R r) := by
  unfold tiltedSolve
  exact exactCalls_acceleratedSolve (Q:=of (X × Y)) (O:=of (FullResponse X Y))
    (Param:=of (X × Y)) (E:=Y) response
    (fun z : FullResponse X Y => z.2.2) (by fun_prop)
    (fun z : (X × Y) × Y => (z.1.1,z.2)) (by fun_prop)
    (fun p : X × Y => t • p.2) (by fun_prop) μ Lg (Real.sqrt (μ/Lg)) σg R r

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem gxBatch_exactCalls (σg radius : ℝ) :
    ExactCalls response (gxBatch σg radius) (FreshBatchKernel.count σg radius) := by
  unfold gxBatch
  exact exactCalls_batch (Q:=of (X × Y)) (O:=of (FullResponse X Y)) (E:=of X) response _ _ _

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y] in
theorem upperBatch_exactCalls (σf radius : ℝ) :
    ExactCalls response (upperBatch σf radius) (FreshBatchKernel.count σf radius) := by
  unfold upperBatch
  exact exactCalls_batch (Q:=of (X × Y)) (O:=of (FullResponse X Y))
    (E:=of (Joint X Y)) response _ _ _

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [BorelSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem anchorLower_exactCalls (μ Lg σg D rA : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (anchorLower μ Lg σg D rA q)
      (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (rA/12)) :=
  (exactCalls_amplify (tiltedSolve_exactCalls response μ Lg σg 0 D (rA/12)) q).reparam _ _

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y] in
theorem anchorUpper_exactCalls (σf η : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (anchorUpper σf η q) (q * FreshBatchKernel.count σf (η/12)) :=
  exactCalls_amplify (upperBatch_exactCalls response σf (η/12)) q

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y] in
theorem anchorUpperAfter_exactCalls (σf η : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (anchorUpperAfter σf η q) (q * FreshBatchKernel.count σf (η/12)) :=
  ((anchorUpper_exactCalls response σf η q).reparam _ _).map _ _

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y] in
theorem anchorRefresh_exactCalls (μ Lg Cf σf σg D rA η : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (anchorRefresh μ Lg Cf σf σg D rA η q)
      (anchorCalls μ Lg σf σg D rA η q) := by
  unfold anchorRefresh anchorCalls
  exact ((anchorLower_exactCalls response μ Lg σg D rA q).bind
    (anchorUpperAfter_exactCalls response σf η q)).map _ _

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [BorelSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem untilted_exactCalls (μ Lg σg D r : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (untilted μ Lg σg D r q)
      (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12)) :=
  (exactCalls_amplify (tiltedSolve_exactCalls response μ Lg σg 0 D (r/12)) q).reparam _ _

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [BorelSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem tilted_exactCalls (μ Lg σg t D r : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (tilted μ Lg σg t D r q)
      (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12)) :=
  (exactCalls_amplify (tiltedSolve_exactCalls response μ Lg σg t D (r/12)) q).reparam _ _

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [BorelSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem solvePair_exactCalls (μ Lg σg t D r : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (solvePair μ Lg σg t D r q)
      (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12) +
       q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12)) := by
  unfold solvePair
  exact (untilted_exactCalls response μ Lg σg D r q).bind
    (((tilted_exactCalls response μ Lg σg t D r q).reparam _ _).map _ _)

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem gxMean_exactCalls (σg δ : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (gxMean σg δ q) (q * FreshBatchKernel.count σg (δ/12)) :=
  exactCalls_amplify (gxBatch_exactCalls response σg (δ/12)) q

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem firstGradient_exactCalls (σg δ : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (firstGradient σg δ q) (q * FreshBatchKernel.count σg (δ/12)) :=
  ((gxMean_exactCalls response σg δ q).reparam _ _).map _ _

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem lastGradient_exactCalls (σg δ : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (lastGradient σg δ q) (q * FreshBatchKernel.count σg (δ/12)) :=
  ((gxMean_exactCalls response σg δ q).reparam _ _).map _ _

omit [CompleteSpace X] [CompleteSpace Y] [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem estimator_exactCalls (μ Lg σg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (estimator μ Lg σg t D r δ q)
      (estimatorCalls μ Lg σg D r δ q) := by
  have h := (((solvePair_exactCalls response μ Lg σg t D r q).bind
    (firstGradient_exactCalls response σg δ q)).bind
    (lastGradient_exactCalls response σg δ q)).map (C:=of X)
      (fun z : CachedEstimatorProcedure.Input X Y × CachedEstimatorProcedure.Transcript X Y =>
        CachedEstimatorProcedure.estimate t z.1 z.2) (by
        unfold CachedEstimatorProcedure.estimate
        fun_prop)
  convert h using 1
  simp only [estimatorCalls]
  ring

end Bilevel.CachedOracleCode
