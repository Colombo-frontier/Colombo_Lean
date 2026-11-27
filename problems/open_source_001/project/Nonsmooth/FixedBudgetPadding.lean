import Nonsmooth.MeasurableSimulation
import Mathlib.Tactic

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- After the original budget, repeat the current output as a charged query and freeze the state. -/
def fixedBudgetPadding {Ω S X : Type} (p : Policy Ω S X) (T : ℕ) : Policy Ω S X where
  initial := p.initial
  query n ω st := if n < T then p.query n ω st else p.output ω st
  update n ω st y := if n < T then p.update n ω st y else st
  output := p.output

theorem fixedBudgetPadding_run {Ω S X : Type} (p : Policy Ω S X) (T : ℕ)
    (f : X → ℝ) (ω : Ω) (n : ℕ) :
    (fixedBudgetPadding p T).run f ω n = p.run f ω (min n T) := by
  induction n with
  | zero => rw [Nat.zero_min]; rfl
  | succ n ih =>
    rw [Policy.run, ih]
    by_cases hn : n < T
    · have hn1 : n + 1 ≤ T := by omega
      simp only [fixedBudgetPadding, if_pos hn, min_eq_left hn.le, min_eq_left hn1, Policy.run]
    · have hTn : T ≤ n := by omega
      simp only [fixedBudgetPadding, if_neg hn, min_eq_right hTn,
        min_eq_right (show T ≤ n + 1 by omega)]

theorem fixedBudgetPadding_final_state {Ω S X : Type} (p : Policy Ω S X) {T B : ℕ}
    (hTB : T ≤ B) (f : X → ℝ) (ω : Ω) :
    (fixedBudgetPadding p T).run f ω B = p.run f ω T := by
  rw [fixedBudgetPadding_run, min_eq_right hTB]

theorem fixedBudgetPadding_result {Ω S X : Type} (p : Policy Ω S X) {T B : ℕ}
    (hTB : T ≤ B) (f : X → ℝ) (ω : Ω) :
    (fixedBudgetPadding p T).result f ω B = p.result f ω T := by
  unfold Policy.result
  rw [fixedBudgetPadding_final_state p hTB]
  rfl

theorem fixedBudgetPadding_measurable {Ω S X : Type}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]
    (p : Policy Ω S X) (hp : p.IsMeasurable) (T : ℕ) :
    (fixedBudgetPadding p T).IsMeasurable := by
  constructor
  · exact hp.initial
  · intro n
    by_cases hn : n < T
    · simpa only [fixedBudgetPadding, if_pos hn] using hp.query n
    · simpa only [fixedBudgetPadding, if_neg hn] using hp.output
  · intro n
    by_cases hn : n < T
    · simpa only [fixedBudgetPadding, if_pos hn] using hp.update n
    · simpa only [fixedBudgetPadding, if_neg hn] using
        (measurable_snd.fst : Measurable (fun z : Ω × S × ℝ => z.2.1))
  · exact hp.output

/-- Rounding a common real cap upward gives a uniform budget and preserves every state-derived output. -/
theorem fixedBudgetPadding_uniform_real_cap {Ω S X Y : Type}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]
    (p : Policy Ω S X) (hp : p.IsMeasurable) {T : ℕ} {A : ℝ} (hT : (T : ℝ) ≤ A)
    (readout : S → Y) :
    (fixedBudgetPadding p T).IsMeasurable ∧
      ∀ f : X → ℝ, ∀ ω : Ω,
        (fixedBudgetPadding p T).result f ω ⌈A⌉₊ = p.result f ω T ∧
        readout ((fixedBudgetPadding p T).run f ω ⌈A⌉₊) = readout (p.run f ω T) := by
  have hceil : T ≤ ⌈A⌉₊ := by exact_mod_cast hT.trans (Nat.le_ceil A)
  exact ⟨fixedBudgetPadding_measurable p hp T, fun f ω =>
    ⟨fixedBudgetPadding_result p hceil f ω, congrArg readout (fixedBudgetPadding_final_state p hceil f ω)⟩⟩

end
end Nonsmooth
