import SampleReuse.RandomFrameTranscript

/-! Conversion from a fixed-cap success bound to a genuine expected-call lower
bound. The cost is the actual natural-valued stopping cost; the capped output
must agree with the execution whenever it has already stopped. -/

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory

variable {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem expected_calls_from_capped_success (cost : Ω → ℕ)
    (hcost : Integrable (fun ω => (cost ω : ℝ)) μ)
    (output cappedOutput : Ω → X) (success : X → Prop) (N : ℕ)
    (hagree : ∀ ω, cost ω ≤ N → cappedOutput ω = output ω)
    {p δ : ℝ} (hsuccess : p ≤ μ.real {ω | success (output ω)})
    (hcap : μ.real {ω | success (cappedOutput ω)} ≤ δ) :
    ((N+1 : ℕ) : ℝ) * (p-δ) ≤ ∫ ω, (cost ω : ℝ) ∂μ := by
  have hsub : {ω | success (output ω)} ⊆
      {ω | success (cappedOutput ω)} ∪ {ω | (N+1 : ℕ) ≤ cost ω} := by
    intro ω hω
    by_cases hc : cost ω ≤ N
    · left
      change success (cappedOutput ω)
      change success (output ω) at hω
      simpa only [hagree ω hc] using hω
    · right
      change N+1 ≤ cost ω
      omega
  have hprob : p-δ ≤ μ.real {ω | (N+1 : ℕ) ≤ cost ω} := by
    have hm := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
    linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg (cost ω))) hcost ((N+1 : ℕ) : ℝ)
  have hevent : {ω | ((N+1 : ℕ) : ℝ) ≤ (cost ω : ℝ)} =
      {ω | (N+1 : ℕ) ≤ cost ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Nat.cast_le]
  rw [hevent] at hmarkov
  exact (mul_le_mul_of_nonneg_left hprob (by positivity)).trans hmarkov

end SampleReuse.RandomFrame
