import RandomizedFO2003.QuadraticSpectral
import RandomizedFO2003.FunctionClassTaylor
import RandomizedFO2003.EpochTerminal

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ) (η θ : ℝ) (start : E)

noncomputable def epochTaylorError (n : ℕ) : E :=
  gradient f (epochQuery f η θ start n) - gradient f start -
    fderiv ℝ (gradient f) start (epochQuery f η θ start n - start)

theorem epoch_query_translation (n : ℕ) :
    epochQuery f η θ start n - start =
      (epochPoint f η θ start n - start) +
        (1 - θ) • ((epochPoint f η θ start n - start) - ((epochState f η θ start n).1 - start)) := by
  unfold epochQuery epochPoint extrapolate
  module

/-- The genuine nonlinear trajectory is exactly a perturbed quadratic
trajectory after translating by the epoch start. -/
theorem epoch_quadratic_recurrence (n : ℕ) :
    epochPoint f η θ start (n + 1) - start =
      vectorAGDStep (η • fderiv ℝ (gradient f) start) (η • gradient f start) θ
        (η • epochTaylorError f η θ start n)
        ((epochState f η θ start n).1 - start) (epochPoint f η θ start n - start) := by
  unfold vectorAGDStep
  rw [← epoch_query_translation]
  simp only [ContinuousLinearMap.smul_apply]
  rw [epochPoint_succ]
  unfold epochTaylorError gradientStep
  module

omit [CompleteSpace E] in
theorem vectorQuadratic_scale (A : E →L[ℝ] E) (g x : E) :
    vectorQuadratic (η • A) (η • g) x = η * vectorQuadratic A g x := by
  simp only [vectorQuadratic, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  ring

variable [FiniteDimensional ℝ E]
variable {f η θ}

theorem epoch_quadratic_energy_scaled (hf : ContDiff ℝ 2 f)
    (hη : 0 ≤ η) (hnorm : η * ‖fderiv ℝ (gradient f) start‖ ≤ 1)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (N : ℕ) :
    8 * θ * η * vectorQuadratic (fderiv ℝ (gradient f) start) (gradient f start)
        (epochPoint f η θ start N - start) +
      3 * θ ^ 2 * epochEnergy f η θ start N ≤
        16 * η ^ 2 * ∑ k ∈ Finset.range N, ‖epochTaylorError f η θ start k‖ ^ 2 := by
  have hA : IsSelfAdjoint (η • fderiv ℝ (gradient f) start) :=
    (show IsSelfAdjoint η from by simp [IsSelfAdjoint]).smul (Calculus.hessian_selfAdjoint hf start)
  have hAnorm : ‖η • fderiv ℝ (gradient f) start‖ ≤ 1 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] using hnorm
  have hs := vector_quadratic_epoch (η • fderiv ℝ (gradient f) start) (η • gradient f start)
    hA hAnorm hθ hθ1
    (fun n => η • epochTaylorError f η θ start n)
    (fun n => (epochState f η θ start n).1 - start)
    (fun n => epochPoint f η θ start n - start)
    rfl (fun _ => rfl) (epoch_quadratic_recurrence f η θ start) N
  have hd (k : ℕ) :
      (epochPoint f η θ start (k + 1) - start) - (epochPoint f η θ start k - start) =
        epochIncrement f η θ start k := by unfold epochIncrement; abel
  have hz : vectorQuadratic (fderiv ℝ (gradient f) start) (gradient f start) (0 : E) = 0 := by
    simp [vectorQuadratic]
  simp only [vectorQuadratic_scale] at hs
  simp only [epochPoint_zero, sub_self, hz, mul_zero, sub_zero, hd,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum] at hs
  change _ + 3 * θ ^ 2 * epochEnergy f η θ start N ≤ _ at hs
  nlinarith

/-- Quadratic-model decrease along the actual nonlinear accelerated epoch. -/
theorem epoch_quadratic_decrease (hf : ContDiff ℝ 2 f)
    (hη : 0 < η) (hnorm : η * ‖fderiv ℝ (gradient f) start‖ ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (N : ℕ) :
    vectorQuadratic (fderiv ℝ (gradient f) start) (gradient f start)
        (epochPoint f η θ start N - start) ≤
      -(3 * θ / (8 * η)) * epochEnergy f η θ start N +
        (2 * η / θ) * ∑ k ∈ Finset.range N, ‖epochTaylorError f η θ start k‖ ^ 2 := by
  have hs := epoch_quadratic_energy_scaled start hf hη.le hnorm hθ.le hθ1 N
  apply (mul_le_mul_left (show 0 < 8 * θ * η by positivity)).mp
  have he : 8 * θ * η * (-(3 * θ / (8 * η)) * epochEnergy f η θ start N +
      (2 * η / θ) * ∑ k ∈ Finset.range N, ‖epochTaylorError f η θ start k‖ ^ 2) =
      -(3 * θ ^ 2 * epochEnergy f η θ start N) +
        16 * η ^ 2 * ∑ k ∈ Finset.range N, ‖epochTaylorError f η θ start k‖ ^ 2 := by
    field_simp
    ring
  rw [he]
  linarith

end RandomizedFO2003.Accelerated
