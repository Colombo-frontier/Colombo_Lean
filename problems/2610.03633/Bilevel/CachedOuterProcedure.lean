import Bilevel.CachedEstimatorAccuracy
import Bilevel.CachedAnchorProcedure
import Bilevel.CappedMeasurability
import Bilevel.CachedAnchorCount

/-! An actual cached outer procedure on the original full SFO history.
Iteration zero refreshes the dummy cache; subsequent refreshes occur exactly
when the current capped point exits the stored anchor ball. The finite trace
is stored as a zero-padded sequence. All N estimators are executed, including
after a cap rejection; the cap ignores those later vectors. This harmless
variant has the same N estimator count and introduces no post-stop anchors.
No minimizer, derivative, or accuracy event enters the algorithm. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.CachedOuterProcedure
open Stateful

abbrev State (X Y : Type*) := (ℕ → X) × (X × CachedAnchorProcedure.Stored X Y)

section Trace
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

def put (G : ℕ → E) (n : ℕ) (v : E) (i : ℕ) : E := if i = n then v else G i

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem put_measurable (n : ℕ) : Measurable (fun p : (ℕ → E) × E => put p.1 n p.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = n
  · simpa only [put, if_pos hi] using (measurable_snd : Measurable (Prod.snd : (ℕ → E) × E → E))
  · simpa only [put, if_neg hi] using ((measurable_pi_apply i).comp measurable_fst)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem run_put_prefix (Λ cap : ℝ) (x₀ : E) (G : ℕ → E) (n : ℕ) (v : E)
    (i : ℕ) (hi : i ≤ n) :
    CappedExecution.run Λ cap x₀ (put G n v) i = CappedExecution.run Λ cap x₀ G i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [CappedExecution.run, CappedExecution.run, ih (by omega)]
    simp only [put, if_neg (by omega : i ≠ n)]

end Trace

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def current (Λ cap : ℝ) (x₀ : X) (n : ℕ) (s : State X Y) : X :=
  (CappedExecution.run Λ cap x₀ s.1 n).point

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem current_measurable (Λ cap : ℝ) (x₀ : X) (n : ℕ) :
    Measurable (current (Y := Y) Λ cap x₀ n) :=
  (CappedExecution.run_measurable Λ cap x₀ (fun i (s : State X Y) => s.1 i)
    (fun i => (measurable_pi_apply i).comp measurable_fst) n).1

def refreshAt (μ Lg Cf D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  ((CachedAnchorProcedure.refresh O μ Lg Cf D rA η q).reparam
    (fun s => (current Λ cap x₀ n s,yinit))
    ((current_measurable Λ cap x₀ n).prodMk measurable_const)).map
    (fun z => (z.1.1,(current Λ cap x₀ n z.1,z.2)))
    ((measurable_fst.comp measurable_fst).prodMk
      (((current_measurable Λ cap x₀ n).comp measurable_fst).prodMk measurable_snd))

def refreshIndex (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) (s : State X Y) : ℕ :=
  if n = 0 ∨ radius < ‖current Λ cap x₀ n s - s.2.1‖ then 1 else 0

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem refreshIndex_measurable (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) :
    Measurable (refreshIndex (Y := Y) Λ cap radius x₀ n) := by
  by_cases hn : n = 0
  · simp only [refreshIndex, hn, true_or, ite_true]
    exact measurable_const
  · have hs : MeasurableSet {s : State X Y | radius < ‖current Λ cap x₀ n s-s.2.1‖} := measurableSet_lt measurable_const
      (((current_measurable (Y := Y) Λ cap x₀ n).sub (measurable_fst.comp measurable_snd)).norm)
    unfold refreshIndex
    simp only [hn, false_or]
    exact (measurable_const.ite hs measurable_const : Measurable (fun s : State X Y =>
      if radius < ‖current Λ cap x₀ n s-s.2.1‖ then (1 : ℕ) else 0))

def maybeRefresh (μ Lg Cf D rA η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  Procedure.choose (fun k => if k = 0 then Procedure.pure id measurable_id else
    refreshAt O μ Lg Cf D rA η Λ cap q x₀ yinit n)
    (refreshIndex Λ cap radius x₀ n) (refreshIndex_measurable Λ cap radius x₀ n)

def estimatorInput (Cf Λ cap : ℝ) (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) :
    CachedEstimatorProcedure.Input X Y :=
  (current Λ cap x₀ n s,s.2.2.2.1,Clipping.clip Cf s.2.2.2.2.1,yinit)

omit [CompleteSpace X] [CompleteSpace Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem estimatorInput_measurable (Cf Λ cap : ℝ) (x₀ : X) (yinit : Y) (n : ℕ) :
    Measurable (estimatorInput Cf Λ cap x₀ yinit n) := by
  have hb : Measurable (fun s : State X Y => s.2.2.2.1) := by fun_prop
  have ha : Measurable (fun s : State X Y => s.2.2.2.2.1) := by fun_prop
  exact (current_measurable Λ cap x₀ n).prodMk
    (hb.prodMk (((BatchMean.clip_stronglyMeasurable Cf ha.stronglyMeasurable).measurable).prodMk measurable_const))

def estimateStep (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  ((CachedEstimatorProcedure.estimator O μ Lg t D r δ q).reparam
    (estimatorInput Cf Λ cap x₀ yinit n) (estimatorInput_measurable Cf Λ cap x₀ yinit n)).map
    (fun z => (put z.1.1 n z.2,z.1.2))
    (((put_measurable n).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst))

def iteration (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  (maybeRefresh O μ Lg Cf D rA η Λ cap radius q x₀ yinit n).bind
    ((estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).reparam Prod.snd measurable_snd)

def initialState (x₀ : X) : State X Y := (fun _ => 0,x₀,0,0,0,0)

def run (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) : ℕ → Procedure Unit History (State X Y)
  | 0 => Procedure.pure (fun _ => initialState x₀) measurable_const
  | n+1 => (run μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).bind
      ((iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).reparam Prod.snd measurable_snd)

end Bilevel.CachedOuterProcedure
