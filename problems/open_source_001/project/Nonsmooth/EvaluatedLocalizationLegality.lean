import Nonsmooth.EvaluatedLocalizationPolicy
import Nonsmooth.SelectedBlockLegality

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem countable_policy_family_measurable {C S X : Type}
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    [MeasurableSpace S] [MeasurableSpace X]
    (p : C → Policy Unit S X) (hp : ∀ c, (p c).IsMeasurable) :
    Measurable (fun c => (p c).initial ()) ∧
      (∀ n, Measurable (fun z : C × S => (p z.1).query n () z.2)) ∧
      (∀ n, Measurable (fun z : C × S × ℝ => (p z.1).update n () z.2.1 z.2.2)) ∧
      Measurable (fun z : C × S => (p z.1).output () z.2) := by
  refine ⟨measurable_of_countable _, ?_, ?_, ?_⟩
  · intro n
    have h : Measurable (fun z : S × C => (p z.2).query n () z.1) :=
      measurable_from_prod_countable_left (fun c => (hp c).query n |>.comp (measurable_const.prodMk measurable_id))
    exact h.comp measurable_swap
  · intro n
    have h : Measurable (fun z : (S × ℝ) × C => (p z.2).update n () z.1.1 z.1.2) :=
      measurable_from_prod_countable_left (fun c => (hp c).update n |>.comp (measurable_const.prodMk measurable_id))
    exact h.comp measurable_swap
  · have h : Measurable (fun z : S × C => (p z.2).output () z.1) :=
      measurable_from_prod_countable_left (fun c => (hp c).output.comp (measurable_const.prodMk measurable_id))
    exact h.comp measurable_swap

theorem evaluatedLocalizationPolicy_measurable {C S X : Type}
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    [MeasurableSpace S] [MeasurableSpace X]
    (p : C → Policy Unit S X) (hp : ∀ c, (p c).IsMeasurable) (T : ℕ)
    (next : C → S → C) (hn : ∀ c, Measurable (next c)) (c0 : C) (x0 : X) :
    (evaluatedLocalizationPolicy p T next c0 x0).IsMeasurable := by
  obtain ⟨hi, hq, hu, _⟩ := countable_policy_family_measurable
    (fun c => queryOutputValue (p c) T) (fun c => queryOutputValue_measurable (p c) (hp c) T)
  have ho := (countable_policy_family_measurable p hp).2.2.2
  have hnext : Measurable (fun z : C × S => next z.1 z.2) := by
    have h : Measurable (fun z : S × C => next z.2 z.1) := measurable_from_prod_countable_left hn
    exact h.comp measurable_swap
  have hstep : Measurable (fun z : (C × BestValueRecord X) × (S × ℝ) =>
      evaluatedLocalizationStep p next z.1 z.2) := by
    have hpack : Measurable (fun z : (C × BestValueRecord X) × (S × ℝ) => (z.1.1, z.2.1)) := by fun_prop
    have hpoint : Measurable (fun z : (C × BestValueRecord X) × (S × ℝ) =>
        (p z.1.1).output () z.2.1) := ho.comp hpack
    exact (hnext.comp hpack).prodMk
      (updateBestValue_measurable.comp (measurable_fst.snd.prodMk (hpoint.prodMk measurable_snd.snd)))
  unfold evaluatedLocalizationPolicy
  apply selectedBlockPolicy_measurable
  · exact hi.comp measurable_fst
  · intro n
    have hpack : Measurable (fun z : (C × BestValueRecord X) × (S × ℝ) => (z.1.1, z.2)) := by fun_prop
    exact (hq n).comp hpack
  · intro n
    have hpack : Measurable (fun z : (C × BestValueRecord X) × (S × ℝ) × ℝ => (z.1.1, z.2.1, z.2.2)) := by fun_prop
    exact (hu n).comp hpack
  · exact hstep
  · exact measurable_snd.snd.fst

end
end Nonsmooth
