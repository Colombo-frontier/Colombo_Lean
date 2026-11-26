import LowRank.PairedKrylovPolicy

/-! Retain both Krylov transcripts and continue with further oracle work.
The extra budget is added once, after both Krylov runs. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe v

def pairedKrylovContinuationBudget (s t m n r : ℕ) : ℕ :=
  krylovQueryBudget s (krylovQueryBudget t m r) n

theorem pairedKrylovContinuationBudget_eq (s t m n r : ℕ) :
    pairedKrylovContinuationBudget s t m n r = m + 2 * s * n + 2 * t * r := by
  simp only [pairedKrylovContinuationBudget, krylovQueryBudget_eq]
  omega

def pairedKrylovBlockContinuation (a b s t m n r : ℕ) {O : Type v} [MeasurableSpace O]
    (next : BoundedRectangularPolicy a b O m
      (PairedKrylovSeed a s t × PairedKrylovData a b s t n r)) :
    BoundedRectangularPolicy a b O (pairedKrylovContinuationBudget s t m n r) (PairedKrylovSeed a s t) :=
  krylovBlockContinuation a b s (krylovQueryBudget t m r) n ⟨Prod.fst, measurable_fst⟩
    (krylovBlockContinuation a b t m r ⟨fun x => x.1.2, measurable_fst.snd⟩
      (next.mapState a b m ⟨fun x => (x.1.1, (x.1.2, x.2)),
        measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)⟩))

theorem pairedKrylovBlockContinuation_run {a b s t m n r : ℕ} {O : Type v} [MeasurableSpace O]
    (next : BoundedRectangularPolicy a b O m
      (PairedKrylovSeed a s t × PairedKrylovData a b s t n r))
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    runBoundedRectangular a b (pairedKrylovContinuationBudget s t m n r)
      (pairedKrylovBlockContinuation a b s t m n r next) A U =
        runBoundedRectangular a b m next A (U, (krylovBlockData A n U.1, krylovBlockData A r U.2)) := by
  change runBoundedRectangular a b (krylovQueryBudget s (krylovQueryBudget t m r) n) _ A U = _
  rw [pairedKrylovBlockContinuation, krylovBlockContinuation_run,
    krylovBlockContinuation_run, runBoundedRectangular_mapState]

theorem pairedKrylovBlockContinuation_calls {a b s t m n r : ℕ} {O : Type v} [MeasurableSpace O]
    (next : BoundedRectangularPolicy a b O m
      (PairedKrylovSeed a s t × PairedKrylovData a b s t n r))
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    ((pairedKrylovBlockContinuation a b s t m n r next).toProgram a b
      (pairedKrylovContinuationBudget s t m n r) U).calls (rectangularOracle A) =
        (next.toProgram a b m (U, (krylovBlockData A n U.1, krylovBlockData A r U.2))).calls
          (rectangularOracle A) + 2 * s * n + 2 * t * r := by
  change (BoundedRectangularPolicy.toProgram a b (krylovQueryBudget s (krylovQueryBudget t m r) n)
    _ U).calls (rectangularOracle A) = _
  rw [pairedKrylovBlockContinuation, krylovBlockContinuation_calls,
    krylovBlockContinuation_calls, BoundedRectangularPolicy.calls_mapState]
  dsimp only
  omega

end
end LowRank
