import Bilevel.CachedOuterProcedure
import Bilevel.CachedOracleCost

/-! Exact original-SFO counters for the executed outer branches. Calls for a
refresh are charged only when the observable refresh test is true. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOuterProcedure
open Stateful

def anchorCalls (μ Lg σf σg D rA η : ℝ) (q : ℕ) : ℕ :=
  q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (rA/12) +
    q * FreshBatchKernel.count σf (η/12)

def estimatorCalls (μ Lg σg D r δ : ℝ) (q : ℕ) : ℕ :=
  2 * (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12)) +
    2 * (q * FreshBatchKernel.count σg (δ/12))

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

theorem refreshAt_calls (μ Lg Cf D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    (refreshAt O μ Lg Cf D rA η Λ cap q x₀ yinit n).CallsEq
      (fun _ => anchorCalls μ Lg σf σg D rA η q) := by
  unfold refreshAt
  exact Procedure.CallsEq.map _ _
    (Procedure.CallsEq.reparam _ _ (CachedAnchorProcedure.refresh_calls O μ Lg Cf D rA η q) _ _) _ _

omit [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem estimateStep_calls (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    (estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).CallsEq
      (fun _ => estimatorCalls μ Lg σg D r δ q) := by
  unfold estimateStep
  exact Procedure.CallsEq.map _ _
    (Procedure.CallsEq.reparam _ _ (CachedEstimatorProcedure.estimator_calls O μ Lg t D r δ q) _ _) _ _

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem refreshIndex_cases (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) (s : State X Y) :
    refreshIndex Λ cap radius x₀ n s = 0 ∨ refreshIndex Λ cap radius x₀ n s = 1 := by
  unfold refreshIndex
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem maybeRefresh_calls (μ Lg Cf D rA η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    (maybeRefresh O μ Lg Cf D rA η Λ cap radius q x₀ yinit n).CallsEq
      (fun s => refreshIndex Λ cap radius x₀ n s * anchorCalls μ Lg σf σg D rA η q) := by
  intro s h
  unfold maybeRefresh
  rw [Procedure.choose_law]
  rcases refreshIndex_cases Λ cap radius x₀ n s with hi | hi
  · simp only [hi, if_pos rfl, Nat.zero_mul]
    exact Procedure.calls_pure id measurable_id s h
  · simp only [hi, Nat.one_ne_zero, if_false, Nat.one_mul]
    exact refreshAt_calls O μ Lg Cf D rA η Λ cap q x₀ yinit n s h

theorem iteration_calls (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    (iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).CallsEq
      (fun s => refreshIndex Λ cap radius x₀ n s * anchorCalls μ Lg σf σg D rA η q +
        estimatorCalls μ Lg σg D r δ q) := by
  unfold iteration
  exact Procedure.CallsEq.bind _ _ _ _
    (maybeRefresh_calls O μ Lg Cf D rA η Λ cap radius q x₀ yinit n)
    (Procedure.CallsEq.reparam _ _ (estimateStep_calls O μ Lg Cf t D r δ Λ cap q x₀ yinit n) _ _)

end Bilevel.CachedOuterProcedure
