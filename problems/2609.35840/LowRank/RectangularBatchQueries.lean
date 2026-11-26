import LowRank.BoundedRectangularPolicy

/-! Fixed rectangular query batches with an arbitrary measurable output
decoder. All replies are real oracle responses, and the program performs
exactly one call per listed query. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

theorem measurable_fin_cons (n : ℕ) {S R : Type*} [MeasurableSpace S] [MeasurableSpace R]
    (x : S → R) (xs : S → Fin n → R) (hx : Measurable x) (hxs : Measurable xs) :
    Measurable (fun s => (Fin.cons (x s) (xs s) : Fin (n + 1) → R)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx
  · exact (measurable_pi_apply j).comp hxs

def rectangularBatchPolicy (a b : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
      (Fin n → RectangularQuery a b) →
      MeasurableStateMap (S × (Fin n → RectangularReply a b)) O →
      BoundedRectangularPolicy a b O n S
  | 0, _, _, _, output =>
      ⟨fun seed => output.1 (seed, Fin.elim0),
        output.2.comp (measurable_id.prodMk measurable_const)⟩
  | n + 1, _, _, queries, output =>
      ({ stop := ⟨fun _ => false, measurable_const⟩
         output := ⟨fun seed => output.1 (seed, fun _ => Sum.inl 0),
           output.2.comp (measurable_id.prodMk measurable_const)⟩
         query := ⟨fun _ => queries 0, measurable_const⟩ },
        rectangularBatchPolicy a b n (fun j => queries j.succ)
          ⟨fun z => output.1 (z.1.1, Fin.cons z.1.2 z.2),
            output.2.comp (measurable_fst.fst.prodMk
              (measurable_fin_cons n _ _ measurable_fst.snd measurable_snd))⟩)

theorem rectangularBatchPolicy_run (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (queries : Fin n → RectangularQuery a b)
    (output : MeasurableStateMap (S × (Fin n → RectangularReply a b)) O)
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b n (rectangularBatchPolicy a b n queries output) A seed =
      output.1 (seed, fun j => rectangularOracle A (queries j)) := by
  induction n generalizing S with
  | zero =>
      change output.1 (seed, Fin.elim0) = _
      apply congrArg output.1
      apply congrArg (Prod.mk seed)
      funext j
      exact Fin.elim0 j
  | succ n ih =>
      rw [runBoundedRectangular_step]
      simp only [rectangularBatchPolicy, Bool.false_eq_true, if_false]
      rw [ih]
      change output.1 (seed, Fin.cons (rectangularOracle A (queries 0))
        (fun j => rectangularOracle A (queries j.succ))) = _
      apply congrArg output.1
      apply congrArg (Prod.mk seed)
      funext j
      exact Fin.cases rfl (fun _ => rfl) j

theorem rectangularBatchPolicy_calls (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (queries : Fin n → RectangularQuery a b)
    (output : MeasurableStateMap (S × (Fin n → RectangularReply a b)) O)
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    ((rectangularBatchPolicy a b n queries output).toProgram a b n seed).calls
      (rectangularOracle A) = n := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      simp only [rectangularBatchPolicy, BoundedRectangularPolicy.toProgram,
        Bool.false_eq_true, if_false, OracleProgram.calls]
      rw [ih]

end
end LowRank
