import LowRank.BoundedRectangularPolicy
import LowRank.PolicyOutputMap

/-! Measurable postprocessing of rectangular algorithm outputs preserves
the executable oracle queries and each path's actual number of calls. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v w

def BoundedRectangularPolicy.mapOutput (a b : ℕ) {O : Type v} {O' : Type w}
    [MeasurableSpace O] [MeasurableSpace O'] (f : MeasurableStateMap O O') :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] → BoundedRectangularPolicy a b O n S →
      BoundedRectangularPolicy a b O' n S
  | 0, _, _, policy => ⟨fun x => f.1 (policy.1 x), f.2.comp policy.2⟩
  | n + 1, _, _, policy =>
      ({stop := policy.1.stop
        output := ⟨fun x => f.1 (policy.1.output.1 x), f.2.comp policy.1.output.2⟩
        query := policy.1.query}, policy.2.mapOutput a b f n)

theorem BoundedRectangularPolicy.toProgram_mapOutput (a b n : ℕ)
    {S : Type u} {O : Type v} {O' : Type w}
    [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace O']
    (f : MeasurableStateMap O O') (policy : BoundedRectangularPolicy a b O n S) (x : S) :
    (policy.mapOutput a b f n).toProgram a b n x = (policy.toProgram a b n x).mapOutput f.1 := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      simp only [mapOutput, toProgram]
      split_ifs
      · rfl
      · simp only [OracleProgram.mapOutput]
        congr 1
        funext reply
        exact ih policy.2 (x, reply)

theorem runBoundedRectangular_mapOutput (a b n : ℕ) {S : Type u} {O : Type v} {O' : Type w}
    [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace O']
    (f : MeasurableStateMap O O') (policy : BoundedRectangularPolicy a b O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    runBoundedRectangular a b n (policy.mapOutput a b f n) A x =
      f.1 (runBoundedRectangular a b n policy A x) := by
  simp only [runBoundedRectangular, BoundedRectangularPolicy.toProgram_mapOutput,
    OracleProgram.eval_mapOutput]

theorem BoundedRectangularPolicy.calls_mapOutput (a b n : ℕ)
    {S : Type u} {O : Type v} {O' : Type w}
    [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace O']
    (f : MeasurableStateMap O O') (policy : BoundedRectangularPolicy a b O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    ((policy.mapOutput a b f n).toProgram a b n x).calls (rectangularOracle A) =
      (policy.toProgram a b n x).calls (rectangularOracle A) := by
  rw [toProgram_mapOutput, OracleProgram.calls_mapOutput]

end
end LowRank
