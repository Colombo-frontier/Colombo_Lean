import Bilevel.CachedOracleCodeEstimator
import Bilevel.CachedOracleCodeAnchor
import Bilevel.CachedUpperAccuracy

/-! Public causal code for the actual capped cached outer loop. The refresh
test dispatches before reading a new oracle reply and all actual calls are
those already counted by CachedOuterProcedure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

def refreshAt (μ Lg Cf σf σg D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  map (.reparam (anchorRefresh μ Lg Cf σf σg D rA η q)
    (fun s => (current Λ cap x₀ n s,yinit))
    ((current_measurable Λ cap x₀ n).prodMk measurable_const))
    (fun z => (z.1.1,(current Λ cap x₀ n z.1,z.2)))
    ((measurable_fst.comp measurable_fst).prodMk
      (((current_measurable Λ cap x₀ n).comp measurable_fst).prodMk measurable_snd))

def maybeRefresh (μ Lg Cf σf σg D rA η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  .choose (fun k => if k=0 then .pure id measurable_id else
    refreshAt μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n)
    (refreshIndex Λ cap radius x₀ n) (refreshIndex_measurable Λ cap radius x₀ n)

def estimateStep (μ Lg Cf σg t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  map (.reparam (estimator μ Lg σg t D r δ q)
    (estimatorInput Cf Λ cap x₀ yinit n) (estimatorInput_measurable Cf Λ cap x₀ yinit n))
    (fun z => (put z.1.1 n z.2,z.1.2))
    (((put_measurable n).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst))

def iteration (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  .bind (maybeRefresh μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n)
    (.reparam (estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n) Prod.snd measurable_snd)

def run (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) : ℕ → Flow (X:=X) (Y:=Y) Unit (State X Y)
  | 0 => .pure (fun _ => initialState x₀) measurable_const
  | n+1 => .bind (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)
      (.reparam (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)
        Prod.snd measurable_snd)

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=Unit) (X:=X) (Y:=Y) σf σg)
  (K : Kernel (X × Y) (FullResponse X Y)) [IsMarkovKernel K]
  (hK : ∀ q,O.law (q,())=K q)

include hK in
theorem denote_refreshAt (μ Lg Cf D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    denote K (refreshAt μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n)=
      CachedOuterProcedure.refreshAt O μ Lg Cf D rA η Λ cap q x₀ yinit n := by
  simp only [refreshAt,denote_map,denote,denote_anchorRefresh O K hK,CachedOuterProcedure.refreshAt]

include hK in
theorem denote_maybeRefresh (μ Lg Cf D rA η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    denote K (maybeRefresh μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n)=
      CachedOuterProcedure.maybeRefresh O μ Lg Cf D rA η Λ cap radius q x₀ yinit n := by
  simp only [maybeRefresh,denote,apply_ite,denote_refreshAt O K hK,CachedOuterProcedure.maybeRefresh]

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
include hK in
theorem denote_estimateStep (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    denote K (estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n)=
      CachedOuterProcedure.estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n := by
  simp only [estimateStep,denote_map,denote,denote_estimator O K hK,CachedOuterProcedure.estimateStep]

include hK in
theorem denote_iteration (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    denote K (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)=
      CachedOuterProcedure.iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n := by
  simp only [iteration,denote,denote_maybeRefresh O K hK,denote_estimateStep O K hK,CachedOuterProcedure.iteration]

include hK in
theorem denote_run (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    denote K (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)=
      CachedOuterProcedure.run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,denote,ih,denote_iteration O K hK,CachedOuterProcedure.run]

end Bilevel.CachedOracleCode
