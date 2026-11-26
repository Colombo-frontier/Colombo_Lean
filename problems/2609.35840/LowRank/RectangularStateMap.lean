import LowRank.BoundedRectangularPolicy

/-! Measurable changes of the initial state of a rectangular oracle policy.
The compiled program is unchanged after substituting the initial state. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v w

def BoundedRectangularPolicy.mapState (a b : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → {T : Type w} → [MeasurableSpace S] → [MeasurableSpace T] →
      MeasurableStateMap T S → BoundedRectangularPolicy a b O n S →
      BoundedRectangularPolicy a b O n T
  | 0, _, _, _, _, f, policy => ⟨fun x => policy.1 (f.1 x), policy.2.comp f.2⟩
  | n + 1, _, _, _, _, f, policy =>
      ({ stop := ⟨fun x => policy.1.stop.1 (f.1 x), policy.1.stop.2.comp f.2⟩
         output := ⟨fun x => policy.1.output.1 (f.1 x), policy.1.output.2.comp f.2⟩
         query := ⟨fun x => policy.1.query.1 (f.1 x), policy.1.query.2.comp f.2⟩ },
        policy.2.mapState a b n
          ⟨fun x => (f.1 x.1, x.2), (f.2.comp measurable_fst).prodMk measurable_snd⟩)

theorem BoundedRectangularPolicy.toProgram_mapState (a b n : ℕ)
    {S : Type u} {T : Type w} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (f : MeasurableStateMap T S) (policy : BoundedRectangularPolicy a b O n S) (x : T) :
    (policy.mapState a b n f).toProgram a b n x = policy.toProgram a b n (f.1 x) := by
  induction n generalizing S T with
  | zero => rfl
  | succ n ih =>
      simp only [mapState, toProgram]
      split_ifs
      · rfl
      · congr 1
        funext reply
        exact ih _ _ (x, reply)

theorem runBoundedRectangular_mapState (a b n : ℕ)
    {S : Type u} {T : Type w} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (f : MeasurableStateMap T S) (policy : BoundedRectangularPolicy a b O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : T) :
    runBoundedRectangular a b n (policy.mapState a b n f) A x =
      runBoundedRectangular a b n policy A (f.1 x) := by
  simp only [runBoundedRectangular, BoundedRectangularPolicy.toProgram_mapState]

theorem BoundedRectangularPolicy.calls_mapState (a b n : ℕ)
    {S : Type u} {T : Type w} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (f : MeasurableStateMap T S) (policy : BoundedRectangularPolicy a b O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : T) :
    ((policy.mapState a b n f).toProgram a b n x).calls (rectangularOracle A) =
      (policy.toProgram a b n (f.1 x)).calls (rectangularOracle A) := by
  rw [toProgram_mapState]

theorem BoundedRectangularPolicy.calls_step (a b n : ℕ)
    {S : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy a b O (n + 1) S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    (policy.toProgram a b (n + 1) x).calls (rectangularOracle A) =
      if policy.1.stop.1 x then 0 else
        (policy.2.toProgram a b n (x, rectangularOracle A (policy.1.query.1 x))).calls
          (rectangularOracle A) + 1 := by
  cases h : policy.1.stop.1 x <;>
    simp only [toProgram, h, Bool.false_eq_true, if_false, if_true, OracleProgram.calls]

end
end LowRank
