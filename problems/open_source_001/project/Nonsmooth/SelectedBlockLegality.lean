import Nonsmooth.SelectedBlockPolicy

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Jointly measurable local policies can be selected and restarted by a measurable controller. -/
theorem selectedBlockPolicy_measurable {C S X : Type}
    [MeasurableSpace C] [MeasurableSpace S] [MeasurableSpace X]
    (p : C → Policy Unit S X)
    (hi : Measurable (fun c => (p c).initial ()))
    (hq : ∀ n, Measurable (fun z : C × S => (p z.1).query n () z.2))
    (hu : ∀ n, Measurable (fun z : C × S × ℝ => (p z.1).update n () z.2.1 z.2.2))
    (T : ℕ) (next : C → S → C) (hn : Measurable (fun z : C × S => next z.1 z.2))
    (out : C → X) (ho : Measurable out) (c0 : C) :
    (selectedBlockPolicy p T next out c0).IsMeasurable := by
  constructor
  · exact measurable_const
  · intro t
    exact (hq (t % T)).comp measurable_snd
  · intro t
    have hpack : Measurable (fun z : Unit × (C × S) × ℝ => (z.2.1.1, z.2.1.2, z.2.2)) := by fun_prop
    have hs : Measurable (fun z : Unit × (C × S) × ℝ => (p z.2.1.1).update (t % T) () z.2.1.2 z.2.2) :=
      (hu (t % T)).comp hpack
    have hc : Measurable (fun z : Unit × (C × S) × ℝ =>
        next z.2.1.1 ((p z.2.1.1).update (t % T) () z.2.1.2 z.2.2)) :=
      hn.comp (measurable_snd.fst.fst.prodMk hs)
    by_cases ht : (t + 1) % T = 0
    · simpa only [selectedBlockPolicy, if_pos ht, Function.comp_def] using hc.prodMk (hi.comp hc)
    · simpa only [selectedBlockPolicy, if_neg ht] using measurable_snd.fst.fst.prodMk hs
  · exact ho.comp measurable_snd.fst

/-- Countably many geometry choices require only the measurability of each individual local policy. -/
theorem selectedBlockPolicy_countable_measurable {C S X : Type}
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    [MeasurableSpace S] [MeasurableSpace X]
    (p : C → Policy Unit S X) (hp : ∀ c, (p c).IsMeasurable)
    (T : ℕ) (next : C → S → C) (hn : ∀ c, Measurable (next c))
    (out : C → X) (c0 : C) :
    (selectedBlockPolicy p T next out c0).IsMeasurable := by
  have hq : ∀ n, Measurable (fun z : C × S => (p z.1).query n () z.2) := by
    intro n
    have h : Measurable (fun z : S × C => (p z.2).query n () z.1) :=
      measurable_from_prod_countable_left (fun c => (hp c).query n |>.comp (measurable_const.prodMk measurable_id))
    exact h.comp measurable_swap
  have hu : ∀ n, Measurable (fun z : C × S × ℝ => (p z.1).update n () z.2.1 z.2.2) := by
    intro n
    have h : Measurable (fun z : (S × ℝ) × C => (p z.2).update n () z.1.1 z.1.2) :=
      measurable_from_prod_countable_left (fun c => (hp c).update n |>.comp (measurable_const.prodMk measurable_id))
    exact h.comp measurable_swap
  have hnext : Measurable (fun z : C × S => next z.1 z.2) := by
    have h : Measurable (fun z : S × C => next z.2 z.1) := measurable_from_prod_countable_left hn
    exact h.comp measurable_swap
  exact selectedBlockPolicy_measurable p (measurable_of_countable _) hq hu T next hnext out
    (measurable_of_countable out) c0

end
end Nonsmooth
