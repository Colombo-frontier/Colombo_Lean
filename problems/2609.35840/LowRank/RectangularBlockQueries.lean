import LowRank.RectangularSeedBatch

/-! Actual block products with A and its transpose. The current block may
depend on earlier oracle replies. All its columns are queried separately. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u v

def forwardBlockQueries {a b s : ℕ} (B : Matrix (Fin b) (Fin s) ℝ) :
    Fin s → RectangularQuery a b := fun j => Sum.inl (fun i => B i j)

def transposeBlockQueries {a b s : ℕ} (B : Matrix (Fin a) (Fin s) ℝ) :
    Fin s → RectangularQuery a b := fun j => Sum.inr (fun i => B i j)

def forwardBlockReplies (a b s : ℕ) (replies : Fin s → RectangularReply a b) :
    Matrix (Fin a) (Fin s) ℝ :=
  fun i j => Sum.elim (fun v => v i) (fun _ => 0) (replies j)

def transposeBlockReplies (a b s : ℕ) (replies : Fin s → RectangularReply a b) :
    Matrix (Fin b) (Fin s) ℝ :=
  fun i j => Sum.elim (fun _ => 0) (fun v => v i) (replies j)

theorem measurable_forwardBlockQueries (a b s : ℕ) :
    Measurable (forwardBlockQueries (a := a) (b := b) (s := s)) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_inl.comp
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply j).comp (measurable_pi_apply i))

theorem measurable_transposeBlockQueries (a b s : ℕ) :
    Measurable (transposeBlockQueries (a := a) (b := b) (s := s)) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_inr.comp
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply j).comp (measurable_pi_apply i))

theorem measurable_forwardBlockReplies (a b s : ℕ) : Measurable (forwardBlockReplies a b s) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact ((measurable_pi_apply i).sumElim measurable_const).comp (measurable_pi_apply j)

theorem measurable_transposeBlockReplies (a b s : ℕ) : Measurable (transposeBlockReplies a b s) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hd : Measurable (fun r : RectangularReply a b =>
      Sum.elim (fun _ => (0 : ℝ)) (fun v => v i) r) :=
    measurable_const.sumElim (measurable_pi_apply i)
  exact hd.comp (measurable_pi_apply j)

theorem forwardBlockReplies_oracle {a b s : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (B : Matrix (Fin b) (Fin s) ℝ) :
    forwardBlockReplies a b s (fun j => rectangularOracle A (forwardBlockQueries B j)) = A * B := rfl

theorem transposeBlockReplies_oracle {a b s : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (B : Matrix (Fin a) (Fin s) ℝ) :
    transposeBlockReplies a b s (fun j => rectangularOracle A (transposeBlockQueries B j)) = Aᵀ * B := rfl

def rectangularForwardBlock (a b s m : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin b) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × Matrix (Fin a) (Fin s) ℝ)) :
    BoundedRectangularPolicy a b O (m + s) S :=
  rectangularSeedBatch a b m s
    ⟨fun x => forwardBlockQueries (block.1 x), (measurable_forwardBlockQueries a b s).comp block.2⟩
    (next.mapState a b m ⟨fun x => (x.1, forwardBlockReplies a b s x.2),
      measurable_fst.prodMk ((measurable_forwardBlockReplies a b s).comp measurable_snd)⟩)

def rectangularTransposeBlock (a b s m : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin a) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × Matrix (Fin b) (Fin s) ℝ)) :
    BoundedRectangularPolicy a b O (m + s) S :=
  rectangularSeedBatch a b m s
    ⟨fun x => transposeBlockQueries (block.1 x), (measurable_transposeBlockQueries a b s).comp block.2⟩
    (next.mapState a b m ⟨fun x => (x.1, transposeBlockReplies a b s x.2),
      measurable_fst.prodMk ((measurable_transposeBlockReplies a b s).comp measurable_snd)⟩)

theorem rectangularForwardBlock_run (a b s m : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin b) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × Matrix (Fin a) (Fin s) ℝ))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b (m + s) (rectangularForwardBlock a b s m block next) A seed =
      runBoundedRectangular a b m next A (seed, A * block.1 seed) := by
  rw [rectangularForwardBlock, rectangularSeedBatch_run, runBoundedRectangular_mapState]
  rfl

theorem rectangularTransposeBlock_run (a b s m : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin a) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × Matrix (Fin b) (Fin s) ℝ))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b (m + s) (rectangularTransposeBlock a b s m block next) A seed =
      runBoundedRectangular a b m next A (seed, Aᵀ * block.1 seed) := by
  rw [rectangularTransposeBlock, rectangularSeedBatch_run, runBoundedRectangular_mapState]
  rfl

theorem rectangularForwardBlock_calls (a b s m : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin b) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × Matrix (Fin a) (Fin s) ℝ))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    ((rectangularForwardBlock a b s m block next).toProgram a b (m + s) seed).calls (rectangularOracle A) =
      (next.toProgram a b m (seed, A * block.1 seed)).calls (rectangularOracle A) + s := by
  rw [rectangularForwardBlock, rectangularSeedBatch_calls, BoundedRectangularPolicy.toProgram_mapState]
  rfl

theorem rectangularTransposeBlock_calls (a b s m : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin a) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × Matrix (Fin b) (Fin s) ℝ))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    ((rectangularTransposeBlock a b s m block next).toProgram a b (m + s) seed).calls (rectangularOracle A) =
      (next.toProgram a b m (seed, Aᵀ * block.1 seed)).calls (rectangularOracle A) + s := by
  rw [rectangularTransposeBlock, rectangularSeedBatch_calls, BoundedRectangularPolicy.toProgram_mapState]
  rfl

end
end LowRank
