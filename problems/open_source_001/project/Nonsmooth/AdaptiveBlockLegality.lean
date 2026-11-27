import Nonsmooth.AdaptiveBlockPolicy

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem adaptiveBlockPolicy_measurable {C S I X : Type}
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace S] [MeasurableSpace X]
    (p : Policy Unit S I) (hp : p.IsMeasurable) (T : ℕ)
    (q : C → I → X) (next : C → I → C) (out : C → X) (c0 : C) :
    (adaptiveBlockPolicy p T q next out c0).IsMeasurable := by
  have hq : Measurable (fun z : C × I => q z.1 z.2) := measurable_of_countable _
  have hn : Measurable (fun z : C × I => next z.1 z.2) := measurable_of_countable _
  constructor
  · exact measurable_const
  · intro t
    have hpack : Measurable (fun z : Unit × (C × S) => ((), z.2.2)) := by fun_prop
    exact hq.comp (measurable_snd.fst.prodMk ((hp.query (t % T)).comp hpack))
  · intro t
    have hpack : Measurable (fun z : Unit × (C × S) × ℝ => ((), z.2.1.2, z.2.2)) := by fun_prop
    have hs : Measurable (fun z : Unit × (C × S) × ℝ => p.update (t % T) () z.2.1.2 z.2.2) :=
      (hp.update (t % T)).comp hpack
    by_cases ht : (t + 1) % T = 0
    · simp only [adaptiveBlockPolicy, if_pos ht]
      have ho : Measurable (fun z : Unit × (C × S) × ℝ =>
          p.output () (p.update (t % T) () z.2.1.2 z.2.2)) :=
        hp.output.comp (measurable_const.prodMk hs)
      exact (hn.comp (measurable_snd.fst.fst.prodMk ho)).prodMk measurable_const
    · simpa only [adaptiveBlockPolicy, if_neg ht] using measurable_snd.fst.fst.prodMk hs
  · exact (measurable_of_countable out).comp measurable_snd.fst

theorem adaptiveBlockPolicy_legal_exact {C S I X : Type}
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] [StandardBorelSpace C]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace X]
    (p : Policy Unit S I) (hp : p.IsMeasurable) {T : ℕ} (hT : 0 < T)
    (q : C → I → X) (next : C → I → C) (out : C → X) (c0 : C) :
    StandardBorelSpace (C × S) ∧ (adaptiveBlockPolicy p T q next out c0).IsMeasurable ∧
      ∀ f : X → ℝ, ∀ m : ℕ,
        (adaptiveBlockPolicy p T q next out c0).result f () (m * T) =
          out (adaptiveBlockController p T q next f c0 m) :=
  ⟨inferInstance, adaptiveBlockPolicy_measurable p hp T q next out c0,
    fun f m => adaptiveBlockPolicy_result_exact p hT q next out c0 f m⟩

end
end Nonsmooth
