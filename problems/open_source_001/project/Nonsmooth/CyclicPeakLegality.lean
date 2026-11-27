import Nonsmooth.ActualCyclicPeak

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem cyclicPeakInitialState_measurable (N : ℕ) : Measurable (cyclicPeakInitialState N) := by
  have hi : Measurable (fun v : Fin 4 → ℝ => ((bestFourResponse v).val : ℤ) * 2 ^ N) :=
    (measurable_of_countable (fun i : Fin 4 => (i.val : ℤ) * 2 ^ N)).comp bestFourResponse_measurable
  exact (measurable_const.prodMk hi).prodMk (measurable_const.prodMk measurable_const)

theorem cyclicPeakPolicy_measurable (N : ℕ) : (cyclicPeakPolicy N).IsMeasurable := by
  have hp := dyadicPeakPolicy_measurable N 0
  constructor
  · exact measurable_const
  · intro t
    by_cases ht : t < 4
    · simp only [cyclicPeakPolicy, if_pos ht]
      exact measurable_const
    · simp only [cyclicPeakPolicy, if_neg ht]
      have hpack : Measurable (fun z : Unit × CyclicPeakState => ((), z.2.2)) := by fun_prop
      exact (hp.query (t - 4)).comp hpack
  · intro t
    by_cases ht : t < 4
    · have hv : Measurable (fun z : Unit × CyclicPeakState × ℝ =>
          Function.update z.2.1.1 ⟨t, ht⟩ z.2.2) :=
        measurable_update'.comp ((measurable_snd.fst.fst).prodMk measurable_snd.snd)
      by_cases ht3 : t = 3
      · convert! hv.prodMk ((cyclicPeakInitialState_measurable N).comp hv) using 1 <;>
          simp only [cyclicPeakPolicy, dif_pos ht, if_pos ht3, Function.comp_def]
      · simpa only [cyclicPeakPolicy, dif_pos ht, if_neg ht3] using
          hv.prodMk (measurable_snd.fst.snd)
    · simp only [cyclicPeakPolicy, dif_neg ht]
      apply Measurable.prodMk (measurable_snd.fst.fst)
      have hpack : Measurable (fun z : Unit × CyclicPeakState × ℝ => ((), z.2.1.2, z.2.2)) := by fun_prop
      exact (hp.update (t - 4)).comp hpack
  · exact measurable_snd.snd.fst.snd

theorem cyclicPeakPolicy_legal_local_max (N : ℕ) :
    StandardBorelSpace CyclicPeakState ∧ (cyclicPeakPolicy N).IsMeasurable ∧
      ∀ f : ℤ → ℝ, Function.Periodic f (4 * 2 ^ N) →
        let z := (cyclicPeakPolicy N).result f () (3 * N + 4)
        f (z - 1) ≤ f z ∧ f (z + 1) ≤ f z :=
  ⟨inferInstance, cyclicPeakPolicy_measurable N, fun f hp => cyclicPeakPolicy_local_max N f hp⟩

/-- A fixed periodic geometric grid gives a legal value-query policy before f is chosen. -/
theorem cyclicPeakPolicy_on_periodic_points {X : Type} [MeasurableSpace X]
    (N : ℕ) (q : ℤ → X) (hq : Function.Periodic q (4 * 2 ^ N)) :
    ((cyclicPeakPolicy N).simulate q (fun _ y => y)).IsMeasurable ∧
      ∀ f : X → ℝ, ∃ z : ℤ,
        ((cyclicPeakPolicy N).simulate q (fun _ y => y)).result f () (3 * N + 4) = q z ∧
        f (q (z - 1)) ≤ f (q z) ∧ f (q (z + 1)) ≤ f (q z) := by
  refine ⟨simulation_measurable (cyclicPeakPolicy_measurable N)
    (measurable_of_countable q) measurable_snd, ?_⟩
  intro f
  let z := (cyclicPeakPolicy N).result (fun j => f (q j)) () (3 * N + 4)
  have hfper : Function.Periodic (fun j => f (q j)) (4 * 2 ^ N) :=
    fun j => congrArg f (hq j)
  have hm := cyclicPeakPolicy_local_max N (fun j => f (q j)) hfper
  refine ⟨z, ?_, hm.1, hm.2⟩
  exact simulation_output_exact (cyclicPeakPolicy N) q (fun _ y => y) f
    (fun j => f (q j)) (fun _ => rfl) () (3 * N + 4)

end
end Nonsmooth
