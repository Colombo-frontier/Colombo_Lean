import UpperOptimization

/-! Exact projected energy recurrence after the actual mean-gradient inequality
has been obtained by fresh-block integration. -/
open MeasureTheory
namespace Task006.Full
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem projected_step_expected_of_inner
    {r η C B W : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hC : 0 ≤ C)
    (x xn g v : Ω → E) (Δ : Ω → ℝ) (z : E) (hz : ‖z‖ ≤ r)
    (hstep : ∀ᵐ ω ∂μ, xn ω = ballProj r hr (x ω - η • g ω))
    (hinner : Integrable (fun ω => inner ℝ (x ω - z) (g ω)) μ)
    (hsq : Integrable (fun ω => ‖x ω - z‖ ^ 2) μ)
    (hnsq : Integrable (fun ω => ‖xn ω - z‖ ^ 2) μ)
    (hgsq : Integrable (fun ω => ‖g ω‖ ^ 2) μ)
    (hΔ : Integrable Δ μ)
    (hgradient : (∫ ω, Δ ω ∂μ) ≤
      (∫ ω, inner ℝ (x ω - z) (g ω) ∂μ) + C * B)
    (hmoment : (∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ W) :
    (∫ ω, Δ ω ∂μ) ≤
      ((∫ ω, ‖x ω - z‖ ^ 2 ∂μ) - (∫ ω, ‖xn ω - z‖ ^ 2 ∂μ)) / (2 * η)
        + C * B + η * W / 2 := by
  have henergy : ∀ᵐ ω ∂μ,
      ‖xn ω - z‖ ^ 2 ≤ ‖x ω - z‖ ^ 2 -
        2 * η * inner ℝ (x ω - z) (g ω) + η ^ 2 * ‖g ω‖ ^ 2 := by
    filter_upwards [hstep] with ω hw
    rw [hw]
    exact projected_step_sq hr (le_of_lt hη) _ _ _ hz
  have henergyInt := integral_mono_ae hnsq
    ((hsq.sub (hinner.const_mul (2 * η))).add (hgsq.const_mul (η ^ 2))) henergy
  simp only [Pi.add_apply, Pi.sub_apply] at henergyInt
  have heqAdd := integral_add (hsq.sub (hinner.const_mul (2 * η)))
    (hgsq.const_mul (η ^ 2))
  have heqSub := integral_sub hsq (hinner.const_mul (2 * η))
  simp only [Pi.add_apply, Pi.sub_apply] at heqAdd heqSub
  rw [heqAdd, heqSub, integral_const_mul, integral_const_mul] at henergyInt
  have hmoment' := mul_le_mul_of_nonneg_left hmoment (sq_nonneg η)
  have hnum : ((∫ ω, Δ ω ∂μ) - C * B - η * W / 2) * (2 * η) ≤
      (∫ ω, ‖x ω - z‖ ^ 2 ∂μ) - (∫ ω, ‖xn ω - z‖ ^ 2 ∂μ) := by
    nlinarith
  have hdiv := (le_div_iff₀ (by positivity : 0 < 2 * η)).mpr hnum
  linarith

#print axioms projected_step_expected_of_inner
end Task006.Full
