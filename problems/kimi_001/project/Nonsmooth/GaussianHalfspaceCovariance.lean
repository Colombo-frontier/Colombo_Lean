import Nonsmooth.GaussianCapPerpendicular
import Nonsmooth.ReflectionVariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Every halfspace kernel of the actual scaled ball-truncated Gaussian satisfies
the sharp covariance bound, including its prescribed zero-mass fallback. -/
theorem gaussianHalfspaceKernel_covariance {u : E} (hu : ‖u‖ = 1) (b : ℝ) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ) (gaussianHalfspaceKernel u b) ≤
      ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  let K : Submodule ℝ E := ℝ ∙ u
  let a : ℝ := ⟪v, u⟫_ℝ
  let w : E := v - a • u
  let ν := gaussianHalfspaceKernel u b
  let e : E ≃ₗᵢ[ℝ] E := K.reflection
  let f : E → ℝ := fun z => a * ⟪u, z⟫_ℝ
  let g : E → ℝ := fun z => ⟪w, z⟫_ℝ
  have hwu : ⟪w, u⟫_ℝ = 0 := by
    simp only [w, a, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
    ring
  have hwm : w ∈ Kᗮ := by
    have h := K.sub_starProjection_mem_orthogonal v
    simpa only [Submodule.starProjection_apply, K, unit_orthogonalProjection_formula hu, w, a] using h
  have heu : e u = u := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton_self u)
  have hew : e w = -w := Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hwm
  have hp : MeasurePreserving e.toMeasurableEquiv ν ν :=
    ⟨e.continuous.measurable, gaussianHalfspaceKernel_isometry u b e heu⟩
  have hfu (z : E) : ⟪u, e z⟫_ℝ = ⟪u, z⟫_ℝ := by
    calc
      _ = ⟪e u, e z⟫_ℝ := by rw [heu]
      _ = _ := e.inner_map_map u z
  have hgw (z : E) : ⟪w, e z⟫_ℝ = -⟪w, z⟫_ℝ := by
    have h := e.inner_map_map w z
    rw [hew, inner_neg_left] at h
    linarith
  have hfe (z : E) : f (e.toMeasurableEquiv z) = f z := by
    change a * ⟪u, e z⟫_ℝ = a * ⟪u, z⟫_ℝ
    rw [hfu]
  have hge (z : E) : g (e.toMeasurableEquiv z) = -g z := hgw z
  have hac : ν ≪ gaussianAmbientRowLaw E := parametricEventKernel_absolutelyContinuous _ _ _ _
  have hV : MemLp (fun z : E => z) 2 ν := MemLp.of_bound measurable_id.aestronglyMeasurable 2
    (hac.ae_le gaussianAmbientRowLaw_norm_le_two)
  have hf : MemLp f 2 ν := (hV.const_inner u).const_mul a
  have hg : MemLp g 2 ν := hV.const_inner w
  have hsplit := reflection_variance_add ν e.toMeasurableEquiv hp f g hf hg hfe hge
  have hfun : (fun z => f z + g z) = fun z : E => ⟪v, z⟫_ℝ := by
    funext z
    simp only [f, g, w, inner_sub_left, real_inner_smul_left]
    ring
  rw [hfun] at hsplit
  have hvarf : variance f ν = a ^ 2 * variance (fun z : E => ⟪u, z⟫_ℝ) ν := variance_mul _ _ _
  have haxial : variance (fun z : E => ⟪u, z⟫_ℝ) ν ≤ 1 / (Module.finrank ℝ E : ℝ) := by
    simpa only [real_inner_comm u] using gaussianHalfspaceKernel_axial_variance hu b
  have hperp : (∫ z, (g z) ^ 2 ∂ν) ≤ ‖w‖ ^ 2 / (Module.finrank ℝ E : ℝ) :=
    gaussianHalfspaceKernel_perpendicular_second hu hwu b
  have hnorm : a ^ 2 + ‖w‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := orthogonal_components_energy K v
    simpa only [K, unit_orthogonalProjection_formula hu, norm_smul, Real.norm_eq_abs,
      hu, mul_one, sq_abs, w, a] using h
  rw [hsplit, hvarf]
  calc
    _ ≤ a ^ 2 * (1 / (Module.finrank ℝ E : ℝ)) + ‖w‖ ^ 2 / (Module.finrank ℝ E : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left haxial (sq_nonneg a)) hperp
    _ = (a ^ 2 + ‖w‖ ^ 2) / (Module.finrank ℝ E : ℝ) := by ring
    _ = _ := by rw [hnorm]

end
end Nonsmooth
