import GradientHessian.InnerDisjointDerivatives
import GradientHessian.SelectorCoordinateBounds

/-! The actual last-register selector coordinates satisfy the Hilbert direct
sum contraction used in the uniform selector theorem. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lastProjection (m k : ℕ) (i : Fin m) : Space Y E m (k + 2) →L[ℝ] E :=
  (PiLp.proj 2 (fun _ : Fin (k + 2) => E) (Fin.last (k + 1))).comp (taskProjection m k i)

@[simp] theorem lastProjection_apply (m k : ℕ) (i : Fin m) (Z : Space Y E m (k + 2)) :
    lastProjection m k i Z = tasks Y E m (k + 2) Z i (Fin.last (k + 1)) := rfl

theorem lastProjection_coordinate_contraction (m k : ℕ) :
    SelectorCoordinateBounds.CoordinateContraction (lastProjection (Y := Y) (E := E) m k) := by
  intro H
  calc
    _ ≤ ∑ i : Fin m, ‖tasks Y E m (k + 2) H i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (PiLp.norm_apply_le (tasks Y E m (k + 2) H i) (Fin.last (k + 1))) 2
    _ ≤ _ := task_norm_square_sum_le H

theorem ports_eq_lastProjection (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2))
    (i : Fin m) : ports v Z i = Profiles.varpi (LatchActivation.readout
      (v i (Fin.last (k + 1))) ((lastRadius k)⁻¹ • lastProjection m k i Z)) := by
  simp only [ports, completion, LatchChain.port, radius_last, LatchChain.u, lastProjection_apply]

theorem ports_eq_selectorPort (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2))
    (i : Fin m) : ports v Z i = SelectorPortBounds.port (lastRadius k)
      (v i (Fin.last (k + 1))) (lastProjection m k i Z) := by
  exact ports_eq_lastProjection v Z i

end GradientHessian.Inner
