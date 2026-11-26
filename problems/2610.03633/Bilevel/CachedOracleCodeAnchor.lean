import Bilevel.CachedOracleCodePrimitive
import Bilevel.CachedAnchorProcedure

/-! Public causal syntax for the executed lower solve and joint upper batch
which refresh the anchor cache. -/
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

def anchorLower (μ Lg σg D rA : ℝ) (q : ℕ) [NeZero q] : Flow (X:=X) (Y:=Y) (X × Y) Y :=
  .reparam (amplify (tiltedSolve (X:=X) (Y:=Y) μ Lg σg 0 D (rA/12)) q)
    (fun p : X × Y => ((p.1,(0:Y)),p.2)) (by fun_prop)

def anchorUpper (σf η : ℝ) (q : ℕ) [NeZero q] : Flow (X:=X) (Y:=Y) (X × Y) (Joint X Y) :=
  amplify (upperBatch σf (η/12)) q

def anchorUpperAfter (σf η : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) ((X × Y) × Y) (CachedAnchorProcedure.Raw X Y) :=
  map (.reparam (anchorUpper σf η q) (fun z => (z.1.1,z.2)) (by fun_prop))
    (fun z => (z.1.2,z.2)) (by fun_prop)

def anchorRefresh (μ Lg Cf σf σg D rA η : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (X × Y) (CachedAnchorProcedure.Stored X Y) :=
  map (.bind (anchorLower μ Lg σg D rA q) (anchorUpperAfter σf η q))
    (fun z => CachedAnchorProcedure.store Cf z.2)
    ((CachedAnchorProcedure.store_measurable Cf).comp measurable_snd)

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=Unit) (X:=X) (Y:=Y) σf σg)
  (K : Kernel (X × Y) (FullResponse X Y)) [IsMarkovKernel K]
  (hK : ∀ q,O.law (q,())=K q)

include hK in
theorem denote_anchorRefresh (μ Lg Cf D rA η : ℝ) (q : ℕ) [NeZero q] :
    denote K (anchorRefresh (X:=X) (Y:=Y) μ Lg Cf σf σg D rA η q)=
      CachedAnchorProcedure.refresh O μ Lg Cf D rA η q := by
  simp only [anchorRefresh,anchorLower,anchorUpperAfter,anchorUpper,denote_map,denote,
    denote_amplify,denote_tiltedSolve O K hK,denote_upperBatch O K hK,
    CachedAnchorProcedure.refresh,CachedAnchorProcedure.refreshRaw,CachedAnchorProcedure.lower,
    CachedAnchorProcedure.upperAfter,CachedAnchorProcedure.upper]

end Bilevel.CachedOracleCode
