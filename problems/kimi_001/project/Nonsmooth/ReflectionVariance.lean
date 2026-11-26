import Nonsmooth.GaussianAxialCap
import Nonsmooth.GaussianHalfspaceMean

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem measurePreserving_odd_integral_zero {α : Type} [MeasurableSpace α]
    (μ : Measure α) (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ)
    (f : α → ℝ) (hf : ∀ x, f (e x) = -f x) : (∫ x, f x ∂μ) = 0 := by
  have h := he.integral_comp e.measurableEmbedding f
  simp_rw [hf] at h
  rw [integral_neg] at h
  linarith

theorem reflection_variance_add {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ)
    (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfe : ∀ x, f (e x) = f x) (hge : ∀ x, g (e x) = -g x) :
    variance (fun x => f x + g x) μ = variance f μ + ∫ x, (g x) ^ 2 ∂μ := by
  have hgm := measurePreserving_odd_integral_zero μ e he g hge
  have hfgm : (∫ x, f x * g x ∂μ) = 0 :=
    measurePreserving_odd_integral_zero μ e he (fun x => f x * g x)
      (fun x => by
        change f (e x) * g (e x) = -(f x * g x)
        rw [hfe, hge, mul_neg])
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hs : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2) μ := hf.integrable_sq.add hg.integrable_sq
  have hsum : MemLp (fun x => f x + g x) 2 μ := hf.add hg
  rw [variance_eq_sub hsum, variance_eq_sub hf]
  simp only [Pi.pow_apply, Pi.add_apply]
  have hpoint (x : α) : (f x + g x) ^ 2 = (f x) ^ 2 + (g x) ^ 2 + 2 * (f x * g x) := by ring
  simp_rw [hpoint]
  rw [integral_add hs (hfg.const_mul 2), integral_add hf.integrable_sq hg.integrable_sq,
    integral_const_mul, hfgm, integral_add (hf.integrable (by norm_num)) (hg.integrable (by norm_num)), hgm]
  ring

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianHalfspaceKernel_isometry (u : E) (b : ℝ) (e : E ≃ₗᵢ[ℝ] E) (hu : e u = u) :
    (gaussianHalfspaceKernel u b).map e = gaussianHalfspaceKernel u b := by
  let C : Set E := {z : E | ⟪z, u⟫_ℝ ≤ b}
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hC : MeasurableSet C := measurableSet_le hr measurable_const
  have hpre : e ⁻¹' C = C := by
    ext z
    change ⟪e z, u⟫_ℝ ≤ b ↔ ⟪z, u⟫_ℝ ≤ b
    have hi : ⟪e z, u⟫_ℝ = ⟪z, u⟫_ℝ := by
      calc
        _ = ⟪e z, e u⟫_ℝ := by rw [hu]
        _ = _ := e.inner_map_map z u
    rw [hi]
  have hcond : ((gaussianAmbientRowLaw E)[|C]).map e = (gaussianAmbientRowLaw E)[|C] := by
    have h := conditioning_map_preimage (gaussianAmbientRowLaw E) e e.continuous.measurable C hC
    rw [gaussianAmbientRowLaw_isometry, hpre] at h
    exact h.symm
  by_cases hpos : gaussianAmbientRowLaw E C = 0
  · have hk : gaussianHalfspaceKernel u b = gaussianAmbientRowLaw E := by
      change (if gaussianAmbientRowLaw E C = 0 then _ else _) = _
      rw [if_pos hpos]
    rw [hk, gaussianAmbientRowLaw_isometry]
  · have hk : gaussianHalfspaceKernel u b = (gaussianAmbientRowLaw E)[|C] := by
      rw [gaussianHalfspaceKernel, parametricEventKernel_apply _ _ _ _ hpos]
      rfl
    rw [hk]
    exact hcond

end
end Nonsmooth
