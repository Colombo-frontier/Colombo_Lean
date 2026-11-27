import Nonsmooth.ActualDyadicPeak

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem dyadicPeakUpdate_measurable :
    Measurable (fun z : (ℕ × ℤ) × ℝ × ℝ × ℝ => dyadicPeakUpdate z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  apply Measurable.prodMk
  · exact (measurable_of_countable (fun st : ℕ × ℤ => st.1 - 1)).comp measurable_fst
  · change Measurable (fun z : (ℕ × ℤ) × ℝ × ℝ × ℝ =>
      if z.2.2.1 < z.2.1 then
        (if z.2.2.2 ≤ z.2.1 then z.1.2 - 2 ^ (z.1.1 - 1) else z.1.2 + 2 ^ (z.1.1 - 1))
      else (if z.2.2.1 < z.2.2.2 then z.1.2 + 2 ^ (z.1.1 - 1) else z.1.2))
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
    · apply Measurable.ite
      · exact measurableSet_le (by fun_prop) (by fun_prop)
      · exact (measurable_of_countable (fun st : ℕ × ℤ => st.2 - 2 ^ (st.1 - 1))).comp measurable_fst
      · exact (measurable_of_countable (fun st : ℕ × ℤ => st.2 + 2 ^ (st.1 - 1))).comp measurable_fst
    · apply Measurable.ite
      · exact measurableSet_lt (by fun_prop) (by fun_prop)
      · exact (measurable_of_countable (fun st : ℕ × ℤ => st.2 + 2 ^ (st.1 - 1))).comp measurable_fst
      · fun_prop

theorem dyadicPeakPolicy_measurable (N : ℕ) (c : ℤ) : (dyadicPeakPolicy N c).IsMeasurable := by
  constructor
  · exact measurable_const
  · intro t
    have hm (g : ℕ × ℤ → ℤ) :
        Measurable (fun z : Unit × ((ℕ × ℤ) × ℝ × ℝ) => g z.2.1) :=
      (measurable_of_countable g).comp (measurable_snd.fst)
    by_cases ht0 : t % 3 = 0
    · simpa only [dyadicPeakPolicy, if_pos ht0] using hm (fun st => st.2 - 2 ^ (st.1 - 1))
    · by_cases ht1 : t % 3 = 1
      · simpa only [dyadicPeakPolicy, if_neg ht0, if_pos ht1] using hm Prod.snd
      · simpa only [dyadicPeakPolicy, if_neg ht0, if_neg ht1] using hm (fun st => st.2 + 2 ^ (st.1 - 1))
  · intro t
    by_cases ht0 : t % 3 = 0
    · simp only [dyadicPeakPolicy, if_pos ht0]
      fun_prop
    · by_cases ht1 : t % 3 = 1
      · simp only [dyadicPeakPolicy, if_neg ht0, if_pos ht1]
        fun_prop
      · simp only [dyadicPeakPolicy, if_neg ht0, if_neg ht1]
        apply Measurable.prodMk _ (measurable_const.prodMk measurable_const)
        have hpack : Measurable (fun z : Unit × ((ℕ × ℤ) × ℝ × ℝ) × ℝ =>
            (z.2.1.1, z.2.1.2.1, z.2.1.2.2, z.2.2)) := by fun_prop
        exact dyadicPeakUpdate_measurable.comp hpack
  · exact measurable_snd.fst.snd

theorem dyadicPeakPolicy_legal_local_max (N : ℕ) (c : ℤ) :
    StandardBorelSpace ((ℕ × ℤ) × ℝ × ℝ) ∧ (dyadicPeakPolicy N c).IsMeasurable ∧
      ∀ f : ℤ → ℝ, f (c - 2 ^ N) ≤ f c → f (c + 2 ^ N) ≤ f c →
        let z := (dyadicPeakPolicy N c).result f () (3 * N)
        f (z - 1) ≤ f z ∧ f (z + 1) ≤ f z :=
  ⟨inferInstance, dyadicPeakPolicy_measurable N c, fun f hl hr => dyadicPeakPolicy_local_max N c f hl hr⟩

end
end Nonsmooth
