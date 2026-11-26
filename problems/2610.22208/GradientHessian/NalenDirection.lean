import GradientHessian.NalenTrajectory

/-! Total normalized descent directions, including a zero gradient.
These serve both initialization and the proof's block comparator. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def descentDirection (D : ℝ) (g : E) : E := -(D/‖g‖) • g

theorem descentDirection_norm {D : ℝ} (hD : 0 ≤ D) (g : E) :
    ‖descentDirection D g‖ ≤ D := by
  by_cases hg : g=0
  · simp [descentDirection,hg,hD]
  have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  rw [descentDirection,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (div_nonneg hD (norm_nonneg _))]
  exact (div_mul_cancel₀ D hn).le

theorem descentDirection_inner (D : ℝ) (g : E) :
    ⟪g,descentDirection D g⟫_ℝ = -D*‖g‖ := by
  by_cases hg : g=0
  · simp [descentDirection,hg]
  have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  simp only [descentDirection,inner_smul_right,real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem descentDirection_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (D : ℝ) : Measurable (descentDirection (E := E) D) :=
  (measurable_const.div continuous_norm.measurable).neg.smul measurable_id

end GradientHessian.Nalen
