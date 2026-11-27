import InformativeHandleCount

open MeasureTheory

namespace Task006.Full
namespace OracleAlgorithm

variable {d N : ℕ} {S Ω Z : Type*}
  [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Z]

theorem scalarReply_parameter_measurable (F : Z → Space d → Ω → ℝ)
    (hF : Measurable (fun p : Z × (Space d × Ω) => F p.1 p.2.1 p.2.2)) :
    Measurable (fun w : Z × ((ℕ → Ω) × QueryAction d) => scalarReply (F w.1) w.2.1 w.2.2) := by
  have heval : Measurable (fun w : (ℕ → Ω) × ℕ => w.1 w.2) := by
    exact measurable_from_prod_countable_left (fun k => measurable_pi_apply k)
  let f : (Unit × (Z × (ℕ → Ω))) ⊕ ((ℕ × Space d) × (Z × (ℕ → Ω))) → ℝ :=
    Sum.elim (fun _ => 0) (fun w => F w.2.1 w.1.2 (w.2.2 w.1.1))
  have hf : Measurable f := by
    apply Measurable.sumElim measurable_const
    exact hF.comp (measurable_snd.fst.prodMk (measurable_fst.snd.prodMk
      (heval.comp (measurable_snd.snd.prodMk measurable_fst.fst))))
  have hs := (MeasurableEquiv.sumProdDistrib Unit (ℕ × Space d) (Z × (ℕ → Ω))).measurable
  have hm := hf.comp (hs.comp
    (((measurable_actionToSum d).comp measurable_snd.snd).prodMk
      (measurable_fst.prodMk measurable_snd.fst)))
  have heq : (fun w : Z × ((ℕ → Ω) × QueryAction d) => scalarReply (F w.1) w.2.1 w.2.2) =
      fun w => f ((MeasurableEquiv.sumProdDistrib Unit (ℕ × Space d) (Z × (ℕ → Ω)))
        (actionToSum d w.2.2,(w.1,w.2.1))) := by
    funext w
    rcases w with ⟨z,tape,a⟩
    cases a <;> rfl
  rw [heq]
  exact hm

theorem runPrefix_parameter_measurable (A : OracleAlgorithm d N S)
    (F : Z → Space d → Ω → ℝ)
    (hF : Measurable (fun p : Z × (Space d × Ω) => F p.1 p.2.1 p.2.2)) (k : ℕ) :
    Measurable (fun w : (Z × S) × (ℕ → Ω) => A.runPrefix (F w.1.1) w.2 w.1.2 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases hk : k < N
    · have ha := (A.action_measurable ⟨k,hk⟩).comp (measurable_fst.snd.prodMk ih)
      have hr := (scalarReply_parameter_measurable F hF).comp
        (measurable_fst.fst.prodMk (measurable_snd.prodMk ha))
      have hm : Measurable (fun w : (Z × S) × (ℕ → Ω) =>
          Function.update (A.runPrefix (F w.1.1) w.2 w.1.2 k) ⟨k,hk⟩
            (scalarReply (F w.1.1) w.2 (A.action ⟨k,hk⟩ w.1.2
              (A.runPrefix (F w.1.1) w.2 w.1.2 k)))) :=
        measurable_update'.comp (ih.prodMk hr)
      simpa only [runPrefix, dif_pos hk] using hm
    · simpa only [runPrefix, dif_neg hk] using ih

theorem executedAction_parameter_measurable (A : OracleAlgorithm d N S)
    (F : Z → Space d → Ω → ℝ)
    (hF : Measurable (fun p : Z × (Space d × Ω) => F p.1 p.2.1 p.2.2)) (k : Fin N) :
    Measurable (fun w : (Z × S) × (ℕ → Ω) => A.executedAction (F w.1.1) w.2 w.1.2 k) :=
  (A.action_measurable k).comp
    (measurable_fst.snd.prodMk (A.runPrefix_parameter_measurable F hF k.val))

theorem measurableSet_queriedBefore_parameter (A : OracleAlgorithm d N S)
    (F : Z → Space d → Ω → ℝ)
    (hF : Measurable (fun p : Z × (Space d × Ω) => F p.1 p.2.1 p.2.2)) (h t : ℕ) :
    MeasurableSet {w : (Z × S) × (ℕ → Ω) | A.queriedBefore (F w.1.1) w.2 w.1.2 h t} := by
  change MeasurableSet {w : (Z × S) × (ℕ → Ω) | ∃ i : Fin N,
    i.val < t ∧ (A.executedAction (F w.1.1) w.2 w.1.2 i).map Prod.fst = some h}
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i.val < t
  · simp only [hi,true_and]
    exact (measurableSet_action_handle h).preimage (A.executedAction_parameter_measurable F hF i)
  · simp only [hi,false_and,Set.setOf_false]
    exact MeasurableSet.empty

end OracleAlgorithm
end Task006.Full
