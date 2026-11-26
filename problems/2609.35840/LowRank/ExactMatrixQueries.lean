import LowRank.RectangularBatchQueries

/-! Recover every entry of a rectangular matrix by querying standard
columns or standard rows. Choosing the shorter side uses min(a,b) calls. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def decodeColumnReplies (a b : ℕ) (replies : Fin b → RectangularReply a b) :
    Matrix (Fin a) (Fin b) ℝ :=
  fun i j => Sum.elim (fun v => v i) (fun _ => 0) (replies j)

def decodeRowReplies (a b : ℕ) (replies : Fin a → RectangularReply a b) :
    Matrix (Fin a) (Fin b) ℝ :=
  fun i j => Sum.elim (fun _ => 0) (fun v => v j) (replies i)

theorem measurable_decodeColumnReplies (a b : ℕ) : Measurable (decodeColumnReplies a b) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact ((measurable_pi_apply i).sumElim measurable_const).comp (measurable_pi_apply j)

theorem measurable_decodeRowReplies (a b : ℕ) : Measurable (decodeRowReplies a b) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hd : Measurable (fun r : RectangularReply a b =>
      Sum.elim (fun _ => (0 : ℝ)) (fun v => v j) r) :=
    measurable_const.sumElim (measurable_pi_apply j)
  exact hd.comp (measurable_pi_apply i)

def readAllColumnsPolicy (a b : ℕ) (S : Type u) [MeasurableSpace S] :
    BoundedRectangularPolicy a b (Matrix (Fin a) (Fin b) ℝ) b S :=
  rectangularBatchPolicy a b b (fun j => Sum.inl (Pi.single j 1))
    ⟨fun z => decodeColumnReplies a b z.2, (measurable_decodeColumnReplies a b).comp measurable_snd⟩

def readAllRowsPolicy (a b : ℕ) (S : Type u) [MeasurableSpace S] :
    BoundedRectangularPolicy a b (Matrix (Fin a) (Fin b) ℝ) a S :=
  rectangularBatchPolicy a b a (fun i => Sum.inr (Pi.single i 1))
    ⟨fun z => decodeRowReplies a b z.2, (measurable_decodeRowReplies a b).comp measurable_snd⟩

theorem readAllColumnsPolicy_run (a b : ℕ) {S : Type u} [MeasurableSpace S]
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b b (readAllColumnsPolicy a b S) A seed = A := by
  rw [readAllColumnsPolicy, rectangularBatchPolicy_run]
  ext i j
  simp [decodeColumnReplies, rectangularOracle, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem readAllRowsPolicy_run (a b : ℕ) {S : Type u} [MeasurableSpace S]
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b a (readAllRowsPolicy a b S) A seed = A := by
  rw [readAllRowsPolicy, rectangularBatchPolicy_run]
  ext i j
  simp [decodeRowReplies, rectangularOracle, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_exactMatrixPolicy (a b : ℕ) (S : Type u) [MeasurableSpace S] :
    ∃ policy : BoundedRectangularPolicy a b (Matrix (Fin a) (Fin b) ℝ) (min a b) S,
      (∀ A seed, runBoundedRectangular a b (min a b) policy A seed = A) ∧
      (∀ A seed, (policy.toProgram a b (min a b) seed).calls (rectangularOracle A) = min a b) := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h]
    exact ⟨readAllRowsPolicy a b S, readAllRowsPolicy_run a b,
      fun A seed => rectangularBatchPolicy_calls a b a _ _ A seed⟩
  · rw [Nat.min_eq_right (Nat.le_of_not_ge h)]
    exact ⟨readAllColumnsPolicy a b S, readAllColumnsPolicy_run a b,
      fun A seed => rectangularBatchPolicy_calls a b b _ _ A seed⟩

def exactMatrixPolicy (a b : ℕ) (S : Type u) [MeasurableSpace S] :
    BoundedRectangularPolicy a b (Matrix (Fin a) (Fin b) ℝ) (min a b) S :=
  (exists_exactMatrixPolicy a b S).choose

theorem exactMatrixPolicy_run (a b : ℕ) {S : Type u} [MeasurableSpace S]
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b (min a b) (exactMatrixPolicy a b S) A seed = A :=
  (exists_exactMatrixPolicy a b S).choose_spec.1 A seed

theorem exactMatrixPolicy_calls (a b : ℕ) {S : Type u} [MeasurableSpace S]
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    ((exactMatrixPolicy a b S).toProgram a b (min a b) seed).calls (rectangularOracle A) = min a b :=
  (exists_exactMatrixPolicy a b S).choose_spec.2 A seed

end
end LowRank
