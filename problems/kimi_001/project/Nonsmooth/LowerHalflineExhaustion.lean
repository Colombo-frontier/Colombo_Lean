import Nonsmooth.ConditioningAEExhaustion

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def lowerHalflineInterval (b : ℝ) (n : ℕ) : Set ℝ := Icc (b - ((n : ℝ) + 1)) b

theorem lowerHalflineInterval_exhausts (b : ℝ) :
    Monotone (lowerHalflineInterval b) ∧ (⋃ n, lowerHalflineInterval b n) = Iic b := by
  constructor
  · intro m n hmn x hx
    have hcast : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    change b - ((m : ℝ) + 1) ≤ x ∧ x ≤ b at hx
    exact ⟨by change b - ((n : ℝ) + 1) ≤ x; linarith [hx.1], hx.2⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.2
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt (b - x)
      exact mem_iUnion.mpr ⟨n, ⟨by change b - ((n : ℝ) + 1) ≤ x; linarith, hx⟩⟩

theorem lowerHalflineInterval_condition (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) (n : ℕ) :
    μ[|Iic b][|lowerHalflineInterval b n] = μ[|lowerHalflineInterval b n] := by
  dsimp only [lowerHalflineInterval]
  rw [cond_cond_eq_cond_inter measurableSet_Iic measurableSet_Icc μ,
    inter_eq_right.mpr (fun x hx => hx.2)]

theorem lowerHalflineInterval_cond_positive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (b : ℝ) (n : ℕ) (hpos : μ (lowerHalflineInterval b n) ≠ 0) :
    μ[|Iic b] (lowerHalflineInterval b n) ≠ 0 := by
  rw [cond_apply measurableSet_Iic, inter_eq_right.mpr (fun x hx => hx.2)]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hpos

theorem lower_halfline_variance_of_intervals (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hf : MemLp (fun x : ℝ => x) 2 μ) (b : ℝ)
    (hpos : ∀ n, μ (lowerHalflineInterval b n) ≠ 0) {C : ℝ}
    (hbound : ∀ n, variance (fun x : ℝ => x) μ[|lowerHalflineInterval b n] ≤ C) :
    variance (fun x : ℝ => x) μ[|Iic b] ≤ C := by
  have hspos : μ (Iic b) ≠ 0 := by
    intro hz
    exact hpos 0 (measure_mono_null (fun x hx => hx.2) hz)
  letI : IsProbabilityMeasure μ[|Iic b] := cond_isProbabilityMeasure hspos
  have hf' : MemLp (fun x : ℝ => x) 2 μ[|Iic b] :=
    (hf.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hspos)
  have hcover : ∀ᵐ x ∂μ[|Iic b], x ∈ ⋃ n, lowerHalflineInterval b n := by
    rw [(lowerHalflineInterval_exhausts b).2]
    exact ae_cond_mem measurableSet_Iic
  apply variance_le_of_ae_conditioning_exhaustion _ hf' (lowerHalflineInterval b)
    (fun _ => measurableSet_Icc) (lowerHalflineInterval_exhausts b).1 hcover
    (fun n => lowerHalflineInterval_cond_positive μ b n (hpos n))
  intro n
  rw [lowerHalflineInterval_condition]
  exact hbound n

theorem lower_halfline_centered_mgf_of_intervals (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hf : Integrable (fun x : ℝ => x) μ) (b t : ℝ)
    (hExp : Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hpos : ∀ n, μ (lowerHalflineInterval b n) ≠ 0) {C : ℝ}
    (hbound : ∀ n, (∫ x, Real.exp (t * (x - ∫ y : ℝ, y ∂μ[|lowerHalflineInterval b n]))
      ∂μ[|lowerHalflineInterval b n]) ≤ C) :
    (∫ x, Real.exp (t * (x - ∫ y : ℝ, y ∂μ[|Iic b])) ∂μ[|Iic b]) ≤ C := by
  have hspos : μ (Iic b) ≠ 0 := by
    intro hz
    exact hpos 0 (measure_mono_null (fun x hx => hx.2) hz)
  letI : IsProbabilityMeasure μ[|Iic b] := cond_isProbabilityMeasure hspos
  have hcover : ∀ᵐ x ∂μ[|Iic b], x ∈ ⋃ n, lowerHalflineInterval b n := by
    rw [(lowerHalflineInterval_exhausts b).2]
    exact ae_cond_mem measurableSet_Iic
  apply centered_mgf_le_of_ae_conditioning_exhaustion _ (integrable_under_event hf hspos) t
    (integrable_under_event hExp hspos) (lowerHalflineInterval b) (fun _ => measurableSet_Icc)
    (lowerHalflineInterval_exhausts b).1 hcover
  intro n
  simpa only [lowerHalflineInterval_condition] using hbound n

end
end Nonsmooth
