import Nonsmooth.FixedBudgetPadding

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- One additional charged query records the actual value of the local algorithm's output. -/
def queryOutputValue {Ω S X : Type} (p : Policy Ω S X) (T : ℕ) : Policy Ω (S × ℝ) X where
  initial ω := (p.initial ω, 0)
  query n ω st := if n < T then p.query n ω st.1 else p.output ω st.1
  update n ω st y := if n < T then (p.update n ω st.1 y, st.2) else (st.1, y)
  output ω st := p.output ω st.1

theorem queryOutputValue_run_prefix {Ω S X : Type} (p : Policy Ω S X) (T : ℕ)
    (f : X → ℝ) (ω : Ω) (n : ℕ) (hn : n ≤ T) :
    (queryOutputValue p T).run f ω n = (p.run f ω n, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnT : n < T := by omega
    rw [Policy.run, ih (by omega)]
    simp only [queryOutputValue, if_pos hnT, Policy.run]

theorem queryOutputValue_run_exact {Ω S X : Type} (p : Policy Ω S X) (T : ℕ)
    (f : X → ℝ) (ω : Ω) :
    (queryOutputValue p T).run f ω (T + 1) = (p.run f ω T, f (p.result f ω T)) := by
  rw [Policy.run, queryOutputValue_run_prefix p T f ω T le_rfl]
  simp only [queryOutputValue, lt_self_iff_false, if_false, Policy.result]

theorem queryOutputValue_result_exact {Ω S X : Type} (p : Policy Ω S X) (T : ℕ)
    (f : X → ℝ) (ω : Ω) :
    (queryOutputValue p T).result f ω (T + 1) = p.result f ω T := by
  unfold Policy.result
  rw [queryOutputValue_run_exact]
  rfl

theorem queryOutputValue_measurable {Ω S X : Type}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]
    (p : Policy Ω S X) (hp : p.IsMeasurable) (T : ℕ) :
    (queryOutputValue p T).IsMeasurable := by
  constructor
  · exact hp.initial.prodMk measurable_const
  · intro n
    have hpack : Measurable (fun z : Ω × S × ℝ => (z.1, z.2.1)) := by fun_prop
    by_cases hn : n < T
    · convert! (hp.query n).comp hpack using 1 <;>
        simp only [queryOutputValue, if_pos hn, Function.comp_def]
    · convert! hp.output.comp hpack using 1 <;>
        simp only [queryOutputValue, if_neg hn, Function.comp_def]
  · intro n
    have hpack : Measurable (fun z : Ω × (S × ℝ) × ℝ => (z.1, z.2.1.1, z.2.2)) := by fun_prop
    by_cases hn : n < T
    · convert! ((hp.update n).comp hpack).prodMk measurable_snd.fst.snd using 1 <;>
        simp only [queryOutputValue, if_pos hn, Function.comp_def]
    · simpa only [queryOutputValue, if_neg hn] using
        (measurable_snd.fst.fst.prodMk measurable_snd.snd :
          Measurable (fun z : Ω × (S × ℝ) × ℝ => (z.2.1.1, z.2.2)))
  · exact hp.output.comp (measurable_fst.prodMk measurable_snd.fst)

end
end Nonsmooth
