import Bilevel.BorelAdaptiveCalls
import Bilevel.BorelAdaptivePrior
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Actual total calls of an absorbing execution, including nontermination.
An infinite live execution costs infinity; the natural stopping-time
fallback zero is never used as its oracle cost. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.BorelAdaptive

variable {S Q O Y I C Private : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace C]
  [MeasurableSpace Private]

open Classical in
def totalCalls (A : Program S Q O Y) (response : I → Q → C → O) (p : Sample I S C) : ℝ≥0∞ :=
  if Terminated A response p then (stopTime A response p:ℝ≥0∞) else ⊤

theorem totalCalls_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) :
    Measurable (totalCalls A response) := by
  classical
  exact ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
    (stopTime_measurable A response hr)).ite (terminated_measurable A response hr) measurable_const

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem totalCalls_eq_top_iff (A : Program S Q O Y) (response : I → Q → C → O) (p : Sample I S C) :
    totalCalls A response p=⊤ ↔ ¬Terminated A response p := by
  classical
  by_cases ht : Terminated A response p <;> simp [totalCalls,ht]

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem totalCalls_eq_iSup_calls (A : Program S Q O Y) (response : I → Q → C → O) (p : Sample I S C) :
    totalCalls A response p=⨆ n : ℕ,(calls A response p.1 p.2.2 p.2.1 n:ℝ≥0∞) := by
  classical
  by_cases ht : Terminated A response p
  · rw [totalCalls,if_pos ht]
    apply le_antisymm
    · have hh := le_iSup (fun n : ℕ => (calls A response p.1 p.2.2 p.2.1 n:ℝ≥0∞)) (stopTime A response p)
      rwa [calls_at_stop A response p ht] at hh
    · apply iSup_le
      intro n
      rw [calls_capped A response p ht n]
      exact Nat.cast_le.mpr (Nat.min_le_right _ _)
  · have hl (n : ℕ) : calls A response p.1 p.2.2 p.2.1 n=n := by
      apply calls_eq_live
      intro t _
      exact Bool.eq_false_of_not_eq_true (fun hh => ht ⟨t,hh⟩)
    simp only [totalCalls,if_neg ht,hl,ENNReal.iSup_natCast]

theorem ae_terminated_of_totalCalls_finite (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (μ : Measure (Sample I S C)) (hf : (∫⁻ p,totalCalls A response p ∂μ)≠⊤) :
    ∀ᵐ p ∂μ,Terminated A response p := by
  filter_upwards [ae_lt_top (totalCalls_measurable A response hr) hf] with p hp
  exact not_not.mp (fun ht => hp.ne ((totalCalls_eq_top_iff A response p).mpr ht))

def seededCalls (A : Program S Q O Y) (response : I → Q → C → O) (initial : Private → S)
    (p : Sample I Private C) : ℝ≥0∞ := totalCalls A response (seedInput initial p)

theorem seededCalls_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) : Measurable (seededCalls A response initial) :=
  (totalCalls_measurable A response hr).comp (seedInput_measurable initial hi)

theorem seeded_ae_terminated_of_calls_finite (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) (μ : Measure (Sample I Private C))
    (hf : (∫⁻ p,seededCalls A response initial p ∂μ)≠⊤) :
    ∀ᵐ p ∂μ,Terminated A response (seedInput initial p) := by
  filter_upwards [ae_lt_top (seededCalls_measurable A response hr initial hi) hf] with p hp
  exact not_not.mp (fun ht => hp.ne ((totalCalls_eq_top_iff A response (seedInput initial p)).mpr ht))

theorem seededCalls_integral_eq_time (A : Program S Q O Y) (response : I → Q → C → O)
    (initial : Private → S) (μ : Measure (Sample I Private C))
    (ht : ∀ᵐ p ∂μ,Terminated A response (seedInput initial p)) :
    (∫⁻ p,seededCalls A response initial p ∂μ)=∫⁻ p,(seededTime A response initial p:ℝ≥0∞) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [ht] with p hp
  simp only [seededCalls,totalCalls,if_pos hp,seededTime]

end Bilevel.BorelAdaptive
