import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Uniform choice of a finite output index and a measurable success event -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NCBall

def uniformIndex (K : ℕ) (hK : 0 < K) : Measure (Fin K) :=
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  (PMF.uniformOfFintype (Fin K)).toMeasure

instance uniformIndex_probability (K : ℕ) (hK : 0 < K) : IsProbabilityMeasure (uniformIndex K hK) := by
  unfold uniformIndex
  infer_instance

theorem uniformIndex_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : ℕ) (hK : 0 < K) (f : Fin K → E) :
    (∫ k, f k ∂uniformIndex K hK) = (K : ℝ)⁻¹ • ∑ k, f k := by
  unfold uniformIndex
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Finset.smul_sum]

theorem uniformIndex_nat_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : ℕ) (hK : 0 < K) (f : ℕ → E) :
    (∫ k, f k.val ∂uniformIndex K hK) = (K : ℝ)⁻¹ • ∑ k ∈ Finset.range K, f k := by
  rw [uniformIndex_integral, Fin.sum_univ_eq_sum_range]

theorem uniform_choice_integral {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [SFinite ν]
    (K : ℕ) (hK : 0 < K) (f : Ω → ℕ → ℝ)
    (hi : Integrable (fun w : Ω × Fin K => f w.1 w.2.val) (ν.prod (uniformIndex K hK))) :
    (∫ w : Ω × Fin K, f w.1 w.2.val ∂ν.prod (uniformIndex K hK)) =
      (K : ℝ)⁻¹ * ∫ ω, ∑ k ∈ Finset.range K, f ω k ∂ν := by
  rw [integral_prod _ hi]
  simp_rw [uniformIndex_nat_integral, smul_eq_mul]
  rw [integral_const_mul]

theorem nonnegative_half_success {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (Z : Ω → ℝ)
    (hZ : Measurable Z) (hi : Integrable Z ν) (hn : ∀ ω, 0 ≤ Z ω)
    {ε : ℝ} (hε : 0 < ε) (hmean : (∫ ω, Z ω ∂ν) ≤ ε / 2) :
    1 / 2 ≤ ν.real {ω | Z ω ≤ ε} := by
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hi ε
  have hb : ν.real {ω | ε ≤ Z ω} ≤ 1 / 2 := by nlinarith
  have hbl : ν.real {ω | ε < Z ω} ≤ 1 / 2 :=
    (measureReal_mono (μ := ν) (show {ω | ε < Z ω} ⊆ {ω | ε ≤ Z ω} from
      fun ω hω => (show ε < Z ω from hω).le)).trans hb
  have hc := measureReal_add_measureReal_compl (μ := ν) (s := {ω | Z ω ≤ ε})
    (measurableSet_le hZ measurable_const)
  simp only [compl_setOf, not_le, measureReal_univ_eq_one] at hc
  linarith

end NCBall
