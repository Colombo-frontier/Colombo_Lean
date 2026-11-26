import SecondOrder.BalancedVectors
import SecondOrder.AdaptiveAnchor

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

variable {A : Type*} [MeasurableSpace A] {η : Measure A}

theorem rademacherSum_joint_measurable {d : ℕ} {a : A → Fin d → ℝ}
    (ha : Measurable a) :
    Measurable (fun w : A × (Fin d → Bool) => rademacherSum (a w.1) w.2) := by
  unfold rademacherSum
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_pi_apply i).comp ha).comp measurable_fst).mul
    ((measurable_of_countable (fun w : Fin d → Bool => signValue (w i))).comp measurable_snd)

theorem balancedVectorSum_joint_measurable {m : ℕ} {a : A → Fin (2*m) → ℝ}
    (ha : Measurable a) :
    Measurable (fun w : A × BalancedVector m => balancedVectorSum (a w.1) w.2) := by
  unfold balancedVectorSum
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_pi_apply i).comp ha).comp measurable_fst).mul
    ((measurable_of_countable (fun w : BalancedVector m => signValue (w.1 i))).comp measurable_snd)

/-- A query may depend on an arbitrary past, provided the hidden sign vector
is sampled independently of that past. The conclusion is localized to every
measurable history event, without conditioning on a positive-probability atom. -/
theorem rademacherSum_past_hoeffding {d : ℕ} {a : A → Fin d → ℝ}
    (ha : Measurable a) {v t : ℝ} (hv : 0 < v) (ht : 0 < t)
    (hb : ∀ x, ∑ i, a x i^2 ≤ v) {past : Set A} (hp : MeasurableSet past) :
    (η.prod (signLaw d)) {w | w.1 ∈ past ∧ t ≤ |rademacherSum (a w.1) w.2|} ≤
      ENNReal.ofReal (2*Real.exp (-t^2/(2*v)))*η past :=
  fresh_event_past_bound
    (by simpa only [Real.norm_eq_abs] using
      measurableSet_le measurable_const (rademacherSum_joint_measurable ha).norm)
    (fun x => rademacherSum_hoeffding_proxy (a x) hv ht (hb x)) hp

theorem balancedVector_past_hoeffding {m : ℕ} {a : A → Fin (2*m) → ℝ}
    (ha : Measurable a) (hb : ∀ x i, |a x i| ≤ 1) {t : ℝ} (ht : 0 < t)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod (balancedVectorLaw m))
      {w | w.1 ∈ past ∧ t ≤ |balancedVectorSum (a w.1) w.2|} ≤
      ENNReal.ofReal (2*Real.exp (-t^2/(4*(2*m:ℕ))))*η past :=
  fresh_event_past_bound
    (by simpa only [Real.norm_eq_abs] using
      measurableSet_le measurable_const (balancedVectorSum_joint_measurable ha).norm)
    (fun x => balancedVector_hoeffding (hb x) ht) hp

end
end SecondOrder
