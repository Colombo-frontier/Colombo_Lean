import HeavyTail.EntropyVariational
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Variational control between two actual densities and the quadratic mean
penalty. The reference density need not equal the base probability density. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace HeavyTail

theorem density_pair_exponential_pointwise {q v g Z : ℝ}
    (hq : 0 < q) (hv : 0 < v) (hZ : 0 < Z) :
    q * g - q * Real.log (q / v) - q * Real.log Z ≤ v * Real.exp g / Z - q := by
  have h := mul_le_mul_of_nonneg_left (entropy_exponential_pointwise (g := g) (div_pos hq hv) hZ) hv.le
  have hcancel : v * (q / v) = q := by field_simp
  simpa only [mul_sub, ← mul_assoc, hcancel, mul_div_assoc] using h

theorem density_pair_entropy_variational
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q v g : Ω → ℝ} (hqpos : ∀ ω, 0 < q ω) (hvpos : ∀ ω, 0 < v ω)
    (hqint : Integrable q μ) (hqnorm : (∫ ω, q ω ∂μ) = 1)
    (hqgint : Integrable (fun ω => q ω * g ω) μ)
    (hKL : Integrable (fun ω => q ω * Real.log (q ω / v ω)) μ)
    (hvg : Integrable (fun ω => v ω * Real.exp (g ω)) μ) :
    (∫ ω, q ω * g ω ∂μ) - densityRelativeEntropy μ q v ≤
      Real.log (∫ ω, v ω * Real.exp (g ω) ∂μ) := by
  let Z := ∫ ω, v ω * Real.exp (g ω) ∂μ
  have hZ : 0 < Z := by
    have heq : (fun ω => Real.exp (Real.log (v ω) + g ω)) =
        (fun ω => v ω * Real.exp (g ω)) := by
      funext ω
      rw [Real.exp_add, Real.exp_log (hvpos ω)]
    change 0 < ∫ ω, v ω * Real.exp (g ω) ∂μ
    rw [← heq]
    apply integral_exp_pos
    rw [heq]
    exact hvg
  have hleft : Integrable
      (fun ω => q ω * g ω - q ω * Real.log (q ω / v ω) - q ω * Real.log Z) μ :=
    (hqgint.sub hKL).sub (hqint.mul_const _)
  have hright : Integrable (fun ω => v ω * Real.exp (g ω) / Z - q ω) μ :=
    (hvg.div_const Z).sub hqint
  have h := integral_mono hleft hright
    (fun ω => density_pair_exponential_pointwise (hqpos ω) (hvpos ω) hZ)
  have hsub : Integrable (fun ω => q ω * g ω - q ω * Real.log (q ω / v ω)) μ :=
    hqgint.sub hKL
  rw [integral_sub hsub (hqint.mul_const _), integral_sub hqgint hKL,
    integral_mul_const, hqnorm, one_mul, integral_sub (hvg.div_const Z) hqint,
    integral_div, hqnorm] at h
  change (∫ ω, q ω * g ω ∂μ) - densityRelativeEntropy μ q v - Real.log Z ≤ Z / Z - 1 at h
  rw [div_self hZ.ne', sub_self] at h
  linarith

theorem quadratic_mean_penalty_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {β η M : ℝ} (hβ : 0 < β) (hη : 0 ≤ η) (_hM : 0 ≤ M)
    {b : E} (hb : ‖b‖ ≤ M) (d : E) :
    -η * ⟪b, d⟫_ℝ - β / 2 * ‖d‖ ^ 2 ≤ η ^ 2 * M ^ 2 / (2 * β) := by
  have hinner : -⟪b, d⟫_ℝ ≤ M * ‖d‖ := by
    have h := (neg_le_abs ⟪b, d⟫_ℝ).trans (abs_real_inner_le_norm b d)
    exact h.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hηinner := mul_le_mul_of_nonneg_left hinner hη
  have hβinner := mul_le_mul_of_nonneg_left hηinner hβ.le
  apply (le_div_iff₀ (by positivity : 0 < 2 * β)).mpr
  nlinarith [sq_nonneg (β * ‖d‖ - η * M)]

end HeavyTail
