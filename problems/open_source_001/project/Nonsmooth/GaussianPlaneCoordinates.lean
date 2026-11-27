import Nonsmooth.GaussianOrthogonalCoordinateLaw
import Nonsmooth.SpanningGaussianPotentialLaw

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem unit_complement_finrank_drop {u : E} (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ + 1 = Module.finrank ℝ E := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hl : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
  have hs := (ℝ ∙ u).finrank_add_finrank_orthogonal
  omega

theorem orthonormal_pair_reconstruction_coordinates {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) (t x : ℝ) :
    (⟪u, t • u + x • v⟫_ℝ, ⟪v, t • u + x • v⟫_ℝ) = (t, x) := by
  have hov : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact ho
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hu, hv, one_pow, mul_one, ho, hov, mul_zero, add_zero, zero_add]

theorem orthonormal_pair_reconstruction_norm {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) (t x : ℝ) :
    ‖t • u + x • v‖ ^ 2 = t ^ 2 + x ^ 2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, hu, hv, mul_one, Real.norm_eq_abs, sq_abs,
    inner_smul_left, inner_smul_right, ho, mul_zero, add_zero]

theorem euclideanGaussian_plane_reconstruction (hd : Module.finrank ℝ E = 2)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => p.1 • u + p.2 • v) = euclideanGaussianLaw E := by
  let K : Submodule ℝ E := (ℝ ∙ v)ᗮ
  let uK : K := ⟨u, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr ho⟩
  have huK : ‖uK‖ = 1 := hu
  have hn : uK ≠ 0 := by intro h; simp [h] at huK
  letI : Nontrivial K := nontrivial_of_ne uK 0 hn
  have hdK : Module.finrank ℝ K = 1 := by
    have h := unit_complement_finrank_drop hv
    dsimp only [K]
    omega
  have hK : (gaussianReal 0 1).map (fun t : ℝ => t • uK) = euclideanGaussianLaw K :=
    euclideanGaussian_spanning_unit_reconstruction huK (unit_spans_of_finrank_one huK hdK)
  have hr := euclideanGaussian_complement_axis_reconstruction hv
  change ((euclideanGaussianLaw K).prod (gaussianReal 0 1)).map
    (fun p : K × ℝ => (p.1 : E) + p.2 • v) = euclideanGaussianLaw E at hr
  have hm : Measurable (fun t : ℝ => t • uK) := by fun_prop
  have hp := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1) hm measurable_id
  simp only [Measure.map_id] at hp
  rw [← hK, hp, Measure.map_map (by fun_prop) (hm.prodMap measurable_id)] at hr
  change ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
    (fun p : ℝ × ℝ => p.1 • u + p.2 • v) = euclideanGaussianLaw E at hr
  exact hr

end
end Nonsmooth
