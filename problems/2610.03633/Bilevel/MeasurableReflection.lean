import Bilevel.ResidualRotation

/-! Explicit measurable Householder updates, including zero residuals. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.MeasurableReflection
open EuclideanGaussian

def reflection (d : ℕ) (u : Space d) : Space d ≃ₗᵢ[ℝ] Space d :=
  (Submodule.span ℝ {u})ᗮ.reflection

theorem apply_formula (d : ℕ) (u x : Space d) :
    reflection d u x = x - (2 * ⟪u,x⟫ / ‖u‖ ^ 2) • u := by
  rw [reflection, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  change -(2 • (⟪u,x⟫ / ‖u‖ ^ 2) • u - x) = _
  module

theorem joint_measurable (d : ℕ) : Measurable (fun p : Space d × Space d => reflection d p.1 p.2) := by
  have he : (fun p : Space d × Space d => reflection d p.1 p.2) =
      fun p => p.2 - (2 * ⟪p.1,p.2⟫ / ‖p.1‖ ^ 2) • p.1 := by
    funext p
    exact apply_formula d p.1 p.2
  rw [he]
  have hi : Measurable (fun p : Space d × Space d => ⟪p.1,p.2⟫) :=
    (continuous_fst.inner continuous_snd).measurable
  exact measurable_snd.sub (((measurable_const.mul hi).div
    (measurable_fst.norm.pow_const 2)).smul measurable_fst)

def direction (d : ℕ) (anchor x : Space d) : Space d :=
  if x = 0 then anchor else ‖x‖⁻¹ • x

theorem direction_measurable (d : ℕ) (anchor : Space d) : Measurable (direction d anchor) := by
  exact measurable_const.ite (measurableSet_singleton 0) (measurable_norm.inv.smul measurable_id)

theorem direction_norm (d : ℕ) (anchor x : Space d) (he : ‖anchor‖ = 1) :
    ‖direction d anchor x‖ = 1 := by
  by_cases hx : x = 0
  · simp [direction, hx, he]
  · simp [direction, hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]

theorem direction_mem (d : ℕ) (V : Submodule ℝ (Space d)) (anchor x : Space d)
    (he : anchor ∈ V) (hx : x ∈ V) : direction d anchor x ∈ V := by
  unfold direction
  split_ifs
  · exact he
  · exact V.smul_mem _ hx

def align (d : ℕ) (anchor x : Space d) : Space d ≃ₗᵢ[ℝ] Space d :=
  reflection d (direction d anchor x - anchor)

theorem align_direction (d : ℕ) (anchor x : Space d) (he : ‖anchor‖ = 1) :
    align d anchor x (direction d anchor x) = anchor :=
  Submodule.reflection_sub ((direction_norm d anchor x he).trans he.symm)

theorem align_measurable (d : ℕ) (anchor : Space d) :
    Measurable (fun p : Space d × Space d => align d anchor p.1 p.2) := by
  have hm : Measurable (fun p : Space d × Space d => (direction d anchor p.1 - anchor, p.2)) :=
    (((direction_measurable d anchor).comp measurable_fst).sub measurable_const).prodMk measurable_snd
  have hc := (joint_measurable d).comp hm
  exact hc

theorem align_fixes_subspace (d : ℕ) (V : Submodule ℝ (Space d)) (anchor x : Space d)
    (he : anchor ∈ Vᗮ) (hx : x ∈ Vᗮ) (y : Space d) (hy : y ∈ V) :
    align d anchor x y = y := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  exact Submodule.inner_right_of_mem_orthogonal hy
    (Vᗮ.sub_mem (direction_mem d Vᗮ anchor x he hx) he)

end Bilevel.MeasurableReflection
