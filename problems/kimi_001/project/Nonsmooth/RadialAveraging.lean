import Nonsmooth.RadialIndependence
import Nonsmooth.SupportCore
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory Filter Function
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def sphericalRadialAverage (f : E → ℝ) (r : ℝ) : ℝ := ∫ u : E, f (r • u) ∂sphericalLaw E

theorem sphericalRadialAverage_stronglyMeasurable {f : E → ℝ} (hf : Continuous f) :
    StronglyMeasurable (sphericalRadialAverage f) := by
  have h : StronglyMeasurable (fun z : ℝ × E => f (z.1 • z.2)) :=
    (hf.comp (continuous_fst.smul continuous_snd)).stronglyMeasurable
  exact h.integral_prod_right'

theorem rotational_radial_average (μ : Measure E) [IsProbabilityMeasure μ]
    (hn : ∀ᵐ z ∂μ, z ≠ 0) (hinv : ∀ e : E ≃ₗᵢ[ℝ] E, μ.map e = μ)
    {f : E → ℝ} (hf : Continuous f) (hfi : Integrable f μ) :
    Integrable (fun z : E => sphericalRadialAverage f ‖z‖) μ ∧
      (∫ z : E, f z ∂μ) = ∫ z : E, sphericalRadialAverage f ‖z‖ ∂μ := by
  let R : Measure ℝ := μ.map (fun z : E => ‖z‖)
  let P := R.prod (sphericalLaw E)
  have hrecon : P.map (fun z : ℝ × E => z.1 • z.2) = μ := by
    dsimp only [P, R]
    rw [← rotational_radius_direction_product μ hn hinv,
      Measure.map_map (g := fun p : ℝ × E => p.1 • p.2) (measurable_fst.smul measurable_snd)
        (continuous_norm.measurable.prodMk normalizedDirection_measurable)]
    have hid : ((fun p : ℝ × E => p.1 • p.2) ∘
        (fun z : E => (‖z‖, normalizedDirection z))) = id :=
      funext normalizedDirection_reconstruct
    rw [hid]
    exact Measure.map_id
  have hp : MeasurePreserving (fun z : ℝ × E => z.1 • z.2) P μ :=
    ⟨measurable_fst.smul measurable_snd, hrecon⟩
  have hprod : Integrable (fun z : ℝ × E => f (z.1 • z.2)) P :=
    (hp.integrable_comp hf.aestronglyMeasurable).mpr hfi
  have hF : Integrable (sphericalRadialAverage f) R := hprod.integral_prod_left
  have hFs := sphericalRadialAverage_stronglyMeasurable hf
  have hr : MeasurePreserving (fun z : E => ‖z‖) μ R := ⟨continuous_norm.measurable, rfl⟩
  refine ⟨(hr.integrable_comp hFs.aestronglyMeasurable).mpr hF, ?_⟩
  calc
    _ = ∫ z : ℝ × E, f (z.1 • z.2) ∂P := by
      have h := integral_map_of_stronglyMeasurable (μ := P) hp.measurable hf.stronglyMeasurable
      rwa [hrecon] at h
    _ = ∫ r : ℝ, sphericalRadialAverage f r ∂R := integral_prod _ hprod
    _ = _ := integral_map_of_stronglyMeasurable continuous_norm.measurable hFs

theorem spherical_cosh_integrable (u : E) (r : ℝ) :
    Integrable (fun x : E => Real.cosh ⟪u, r • x⟫_ℝ) (sphericalLaw E) := by
  have hm : AEStronglyMeasurable (fun x : E => Real.cosh ⟪u, r • x⟫_ℝ) (sphericalLaw E) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  apply Integrable.mono' (integrable_const (Real.cosh (|r| * ‖u‖))) hm
  filter_upwards [sphericalLaw_unit (E := E)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), Real.cosh_le_cosh]
  rw [abs_of_nonneg (by positivity : 0 ≤ |r| * ‖u‖)]
  calc
    |⟪u, r • x⟫_ℝ| = |r| * |⟪u, x⟫_ℝ| := by rw [inner_smul_right, abs_mul]
    _ ≤ |r| * (‖u‖ * ‖x‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ = _ := by rw [hx, mul_one]

theorem spherical_cosh_radial_mono (u : E) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    sphericalRadialAverage (fun x : E => Real.cosh ⟪u, x⟫_ℝ) r ≤
      sphericalRadialAverage (fun x : E => Real.cosh ⟪u, x⟫_ℝ) s := by
  apply integral_mono (spherical_cosh_integrable u r) (spherical_cosh_integrable u s)
  intro x
  rw [Real.cosh_le_cosh, inner_smul_right, inner_smul_right, abs_mul, abs_mul,
    abs_of_nonneg hr, abs_of_nonneg (hr.trans hrs)]
  exact mul_le_mul_of_nonneg_right hrs (abs_nonneg _)

end
end Nonsmooth
