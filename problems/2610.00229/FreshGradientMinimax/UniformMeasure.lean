import FreshGradientMinimax.FiniteMixture

/-! Uniform mixtures of finitely many actual output distributions. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X : Type*} [MeasurableSpace X]

def uniformMeasure (ρ : ℕ → Measure X) (T : ℕ) : Measure X :=
  finiteMixtureKernel (fun _ => 1 / (T : ℝ)) (fun j => Kernel.const Unit (ρ j)) T ()

theorem uniform_weights_sum {T : ℕ} (hT : 0 < T) : (∑ _j ∈ Finset.range T, (1 : ℝ) / T) = 1 := by
  have ht : (T : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hT)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem uniformMeasure_probability (ρ : ℕ → Measure X) [∀ j, IsProbabilityMeasure (ρ j)]
    {T : ℕ} (hT : 0 < T) : IsProbabilityMeasure (uniformMeasure ρ T) := by
  letI := finiteMixtureKernel_markov (fun _ => 1 / (T : ℝ)) (fun j => Kernel.const Unit (ρ j)) T
    (fun _ _ => by positivity) (uniform_weights_sum hT)
  exact inferInstanceAs (IsProbabilityMeasure (finiteMixtureKernel (fun _ => 1 / (T : ℝ))
    (fun j => Kernel.const Unit (ρ j)) T ()))

theorem uniformMeasure_integrable (ρ : ℕ → Measure X) (T : ℕ) (f : X → ℝ)
    (hi : ∀ j < T, Integrable f (ρ j)) : Integrable f (uniformMeasure ρ T) :=
  finiteMixtureKernel_integrable _ _ _ _ _ hi

theorem uniformMeasure_integral (ρ : ℕ → Measure X) (T : ℕ) (f : X → ℝ)
    (hi : ∀ j < T, Integrable f (ρ j)) :
    (∫ x, f x ∂uniformMeasure ρ T) = (∑ j ∈ Finset.range T, ∫ x, f x ∂ρ j) / T := by
  rw [uniformMeasure, finiteMixtureKernel_integral _ _ _ _ _ (fun _ _ => by positivity) hi]
  simp only [Kernel.const_apply, smul_eq_mul, one_div, ← Finset.mul_sum]
  ring

theorem uniformMeasure_mean_bound (ρ : ℕ → Measure X) {T : ℕ} (hT : 0 < T) (f : X → ℝ)
    (hi : ∀ j < T, Integrable f (ρ j)) {B : ℝ} (hb : ∀ j < T, (∫ x, f x ∂ρ j) ≤ B) :
    (∫ x, f x ∂uniformMeasure ρ T) ≤ B := by
  rw [uniformMeasure_integral ρ T f hi]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hT)).mpr
  calc
    _ ≤ ∑ _j ∈ Finset.range T, B := Finset.sum_le_sum (fun j hj => hb j (Finset.mem_range.mp hj))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end FreshGradientMinimax
