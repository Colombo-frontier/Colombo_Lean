import UpperQueryLedger
import ReadOnceIndependence

open MeasureTheory

namespace Task006.Full
namespace OracleAlgorithm

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

theorem scalarReply_measurable (F : Space d → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun w : (ℕ → Ω) × QueryAction d => scalarReply F w.1 w.2) := by
  have heval : Measurable (fun w : (ℕ → Ω) × ℕ => w.1 w.2) := by
    apply measurable_from_prod_countable_left
    intro k
    exact measurable_pi_apply k
  let f : (Unit × (ℕ → Ω)) ⊕ ((ℕ × Space d) × (ℕ → Ω)) → ℝ :=
    Sum.elim (fun _ => 0) (fun w => F w.1.2 (w.2 w.1.1))
  have hf : Measurable f := by
    apply Measurable.sumElim measurable_const
    exact hF.comp (measurable_fst.snd.prodMk
      (heval.comp (measurable_snd.prodMk measurable_fst.fst)))
  have hs := (MeasurableEquiv.sumProdDistrib Unit (ℕ × Space d) (ℕ → Ω)).measurable
  have hm := hf.comp (hs.comp
    (((measurable_actionToSum d).comp measurable_snd).prodMk measurable_fst))
  have heq : (fun w : (ℕ → Ω) × QueryAction d => scalarReply F w.1 w.2) =
      fun w => f ((MeasurableEquiv.sumProdDistrib Unit (ℕ × Space d) (ℕ → Ω))
        (actionToSum d w.2,w.1)) := by
    funext w
    rcases w with ⟨tape,a⟩
    cases a <;> rfl
  rw [heq]
  exact hm

theorem runPrefix_measurable (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (k : ℕ) :
    Measurable (fun w : S × (ℕ → Ω) => A.runPrefix F w.2 w.1 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases hk : k < N
    · have ha := (A.action_measurable ⟨k,hk⟩).comp (measurable_fst.prodMk ih)
      have hr := (scalarReply_measurable F hF).comp (measurable_snd.prodMk ha)
      have hm : Measurable (fun w : S × (ℕ → Ω) =>
          Function.update (A.runPrefix F w.2 w.1 k) ⟨k,hk⟩
            (scalarReply F w.2 (A.action ⟨k,hk⟩ w.1 (A.runPrefix F w.2 w.1 k)))) :=
        measurable_update'.comp (ih.prodMk hr)
      simpa only [runPrefix, dif_pos hk] using hm
    · simpa only [runPrefix, dif_neg hk] using ih

theorem executedAction_measurable (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (k : Fin N) :
    Measurable (fun w : S × (ℕ → Ω) => A.executedAction F w.2 w.1 k) := by
  exact (A.action_measurable k).comp
    (measurable_fst.prodMk (A.runPrefix_measurable F hF k.val))

theorem measurableSet_action_handle (h : ℕ) :
    MeasurableSet {a : QueryAction d | a.map Prod.fst = some h} := by
  have hs : MeasurableSet (Sum.inr '' ({h} ×ˢ (Set.univ : Set (Space d))) :
      Set (Unit ⊕ (ℕ × Space d))) :=
    ((measurableSet_singleton h).prod MeasurableSet.univ).inr_image
  convert hs.preimage (measurable_actionToSum d) using 1
  ext a
  cases a with
  | none => simp [actionToSum]
  | some a => rcases a with ⟨k,x⟩; simp [actionToSum]

theorem measurableSet_queriedBefore (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (h t : ℕ) :
    MeasurableSet {w : S × (ℕ → Ω) | A.queriedBefore F w.2 w.1 h t} := by
  change MeasurableSet {w : S × (ℕ → Ω) | ∃ i : Fin N,
    i.val < t ∧ (A.executedAction F w.2 w.1 i).map Prod.fst = some h}
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i.val < t
  · simp only [hi,true_and]
    exact (measurableSet_action_handle h).preimage (A.executedAction_measurable F hF i)
  · simp only [hi,false_and,Set.setOf_false]
    exact MeasurableSet.empty

end OracleAlgorithm
end Task006.Full
