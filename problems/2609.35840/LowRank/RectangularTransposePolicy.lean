import LowRank.RectangularStateMap

/-! Transposing a two-sided oracle policy swaps the query and reply tags.
The construction is measurable, preserves early stopping, and uses one
original-matrix query for each transposed-matrix query. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

theorem measurable_rectangular_swap (a b : ℕ) :
    Measurable (Sum.swap : RectangularQuery a b → RectangularQuery b a) := by
  change Measurable (Sum.elim Sum.inr Sum.inl)
  exact measurable_inr.sumElim measurable_inl

theorem rectangularOracle_transpose_swap {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (q : RectangularQuery b a) :
    Sum.swap (rectangularOracle A (Sum.swap q)) = rectangularOracle Aᵀ q := by
  cases q <;> simp [rectangularOracle]

def BoundedRectangularPolicy.transpose (a b : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
      BoundedRectangularPolicy b a O n S → BoundedRectangularPolicy a b O n S
  | 0, _, _, policy => policy
  | n + 1, _, _, policy =>
      ({ stop := policy.1.stop
         output := policy.1.output
         query := ⟨fun x => Sum.swap (policy.1.query.1 x),
           (measurable_rectangular_swap b a).comp policy.1.query.2⟩ },
       (policy.2.transpose a b n).mapState a b n
         ⟨fun x => (x.1, Sum.swap x.2),
           measurable_fst.prodMk ((measurable_rectangular_swap b a).comp measurable_snd)⟩)

theorem BoundedRectangularPolicy.toProgram_transpose (a b n : ℕ)
    {S : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy b a O n S) (x : S) :
    (policy.transpose a b n).toProgram a b n x =
      (policy.toProgram b a n x).simulate Sum.swap (fun _ r => Sum.swap r) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      simp only [transpose, toProgram]
      split_ifs
      · rfl
      · simp only [OracleProgram.simulate]
        congr 1
        funext reply
        rw [toProgram_mapState]
        exact ih _ _

theorem runBoundedRectangular_transpose (a b n : ℕ)
    {S : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy b a O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    runBoundedRectangular a b n (policy.transpose a b n) A x =
      runBoundedRectangular b a n policy Aᵀ x := by
  rw [runBoundedRectangular, BoundedRectangularPolicy.toProgram_transpose]
  exact OracleProgram.eval_simulate _ _ Sum.swap (fun _ r => Sum.swap r)
    (rectangularOracle_transpose_swap A) _

theorem BoundedRectangularPolicy.calls_transpose (a b n : ℕ)
    {S : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy b a O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    ((policy.transpose a b n).toProgram a b n x).calls (rectangularOracle A) =
      (policy.toProgram b a n x).calls (rectangularOracle Aᵀ) := by
  rw [toProgram_transpose]
  exact OracleProgram.calls_simulate _ _ Sum.swap (fun _ r => Sum.swap r)
    (rectangularOracle_transpose_swap A) _

end
end LowRank
