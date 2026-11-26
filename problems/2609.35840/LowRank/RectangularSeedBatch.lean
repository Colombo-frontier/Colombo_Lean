import LowRank.RectangularStateMap
import LowRank.RectangularBatchQueries

/-! Query batches chosen measurably from the current state, followed by an
arbitrary bounded continuation. Each listed vector costs one real oracle call. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

def rectangularSeedBatch (a b m : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
      MeasurableStateMap S (Fin n → RectangularQuery a b) →
      BoundedRectangularPolicy a b O m (S × (Fin n → RectangularReply a b)) →
      BoundedRectangularPolicy a b O (m + n) S
  | 0, _, _, _, next =>
      next.mapState a b m ⟨fun x => (x, Fin.elim0), measurable_id.prodMk measurable_const⟩
  | n + 1, S, _, queries, next =>
      ({ stop := ⟨fun _ => false, measurable_const⟩
         output := ⟨fun x => runBoundedRectangular a b m next 0 (x, fun _ => Sum.inl 0),
           (measurable_runBoundedRectangular a b m next).comp
             (measurable_const.prodMk (measurable_id.prodMk measurable_const))⟩
         query := ⟨fun x => queries.1 x 0, (measurable_pi_apply 0).comp queries.2⟩ },
        rectangularSeedBatch a b m n
          ⟨fun x j => queries.1 x.1 j.succ,
            measurable_pi_lambda _ (fun j =>
              (measurable_pi_apply j.succ).comp (queries.2.comp measurable_fst))⟩
          (next.mapState a b m
            ⟨fun x => (x.1.1, Fin.cons x.1.2 x.2),
              measurable_fst.fst.prodMk
                (measurable_fin_cons n
                  (fun x : (S × RectangularReply a b) × (Fin n → RectangularReply a b) => x.1.2)
                  (fun x => x.2) measurable_fst.snd measurable_snd)⟩))

theorem rectangularSeedBatch_run (a b m n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (queries : MeasurableStateMap S (Fin n → RectangularQuery a b))
    (next : BoundedRectangularPolicy a b O m (S × (Fin n → RectangularReply a b)))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b (m + n) (rectangularSeedBatch a b m n queries next) A seed =
      runBoundedRectangular a b m next A (seed, fun j => rectangularOracle A (queries.1 seed j)) := by
  induction n generalizing S with
  | zero =>
      change runBoundedRectangular a b m _ A seed = _
      rw [rectangularSeedBatch, runBoundedRectangular_mapState]
      congr 1
      apply congrArg (Prod.mk seed)
      funext j
      exact Fin.elim0 j
  | succ n ih =>
      change runBoundedRectangular a b ((m + n) + 1) _ A seed = _
      rw [runBoundedRectangular_step]
      simp only [rectangularSeedBatch, Bool.false_eq_true, if_false]
      rw [ih, runBoundedRectangular_mapState]
      congr 1
      apply congrArg (Prod.mk seed)
      funext j
      exact Fin.cases rfl (fun _ => rfl) j

theorem rectangularSeedBatch_calls (a b m n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (queries : MeasurableStateMap S (Fin n → RectangularQuery a b))
    (next : BoundedRectangularPolicy a b O m (S × (Fin n → RectangularReply a b)))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    ((rectangularSeedBatch a b m n queries next).toProgram a b (m + n) seed).calls
        (rectangularOracle A) =
      (next.toProgram a b m (seed, fun j => rectangularOracle A (queries.1 seed j))).calls
        (rectangularOracle A) + n := by
  induction n generalizing S with
  | zero =>
      simp only [rectangularSeedBatch, BoundedRectangularPolicy.toProgram_mapState, Nat.add_zero]
      congr 2
      apply congrArg (Prod.mk seed)
      funext j
      exact Fin.elim0 j
  | succ n ih =>
      change (BoundedRectangularPolicy.toProgram a b ((m + n) + 1) _ seed).calls
        (rectangularOracle A) = _
      rw [BoundedRectangularPolicy.calls_step]
      simp only [rectangularSeedBatch, Bool.false_eq_true, if_false]
      rw [ih, BoundedRectangularPolicy.toProgram_mapState]
      rw [Nat.add_assoc]
      congr 2
      apply congrArg (next.toProgram a b m)
      apply congrArg (Prod.mk seed)
      funext j
      exact Fin.cases rfl (fun _ => rfl) j

end
end LowRank
