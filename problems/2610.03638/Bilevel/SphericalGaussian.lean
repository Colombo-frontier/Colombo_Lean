import Bilevel.EuclideanGaussian
import Mathlib.Analysis.InnerProductSpace.Projection

/-! Directional concentration for an actual rotationally invariant Gaussian. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.SphericalGaussian
open EuclideanGaussian

theorem measureReal_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {g : α → β} (hg : MeasurePreserving g μ ν)
    (s : Set β) (hs : MeasurableSet s) : μ.real (g ⁻¹' s) = ν.real s := by
  simp only [measureReal_def]
  rw [← hg.map_eq, Measure.map_apply hg.measurable hs]

theorem coordinate_tail (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 2) :
    (law (n + 1)).real {x : Space (n + 1) | t * ‖x‖ ^ 2 ≤ (x 0) ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) := by
  let s : Set (Fin (n + 1) → ℝ) := {x | t * (∑ i, (x i) ^ 2) ≤ (x 0) ^ 2}
  have hs : MeasurableSet s := by
    apply measurableSet_le
    · exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).pow_const 2))
    · exact (measurable_pi_apply 0).pow_const 2
  have he : {x : Space (n + 1) | t * ‖x‖ ^ 2 ≤ (x 0) ^ 2} =
      (EuclideanSpace.measurableEquiv (Fin (n + 1))) ⁻¹' s := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, s, PiLp.norm_sq_eq_of_L2,
      Real.norm_eq_abs, sq_abs]
    rfl
  rw [he, measureReal_preimage (coordinates_preserving (n + 1)) s hs]
  exact GaussianDirectionTail.direction_event_bound n t ht ht2

theorem directional_tail (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (w : Space (n + 1)) (hw : ‖w‖ = 1) :
    (law (n + 1)).real {x : Space (n + 1) | t * ‖x‖ ^ 2 ≤ ⟪w, x⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) := by
  let e : Space (n + 1) := EuclideanSpace.single 0 1
  let U : Space (n + 1) ≃ₗᵢ[ℝ] Space (n + 1) := (Submodule.span ℝ {w - e})ᗮ.reflection
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_single]
  have hUw : U w = e := Submodule.reflection_sub (hw.trans he.symm)
  have hcoord (x : Space (n + 1)) : (U x) 0 = ⟪w, x⟫ := by
    have hi := U.inner_map_map w x
    rw [hUw] at hi
    simpa [e, EuclideanSpace.inner_single_left] using hi
  let s : Set (Space (n + 1)) := {x | t * ‖x‖ ^ 2 ≤ (x 0) ^ 2}
  have hs : MeasurableSet s := by
    apply measurableSet_le
    · fun_prop
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).continuous.measurable.pow_const 2
  have hset : {x : Space (n + 1) | t * ‖x‖ ^ 2 ≤ ⟪w, x⟫ ^ 2} = U ⁻¹' s := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, s, U.norm_map, hcoord]
  rw [hset, measureReal_preimage (orthogonal_invariance (n + 1) U) s hs]
  exact coordinate_tail n t ht ht2

def direction {d : ℕ} (x : Space d) : Space d := ‖x‖⁻¹ • x

theorem direction_norm {d : ℕ} (x : Space d) (hx : x ≠ 0) : ‖direction x‖ = 1 := by
  simp [direction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), hx]

theorem direction_measurable (d : ℕ) : Measurable (@direction d) := by
  exact measurable_norm.inv.smul measurable_id

theorem direction_equivariant (d : ℕ) (U : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d) :
    direction (U x) = U (direction x) := by simp [direction, U.norm_map]

theorem normalized_direction_tail (n : ℕ) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w : Space (n + 1)) (hw : ‖w‖ = 1) :
    (law (n + 1)).real {x : Space (n + 1) | t ≤ ⟪w, direction x⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) := by
  have hsub : {x : Space (n + 1) | t ≤ ⟪w, direction x⟫ ^ 2} ⊆
      {x | t * ‖x‖ ^ 2 ≤ ⟪w, x⟫ ^ 2} := by
    intro x hx
    by_cases hzero : x = 0
    · subst x
      simp [direction] at hx
      linarith
    have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzero)
    change t ≤ ⟪w, direction x⟫ ^ 2 at hx
    rw [direction, real_inner_smul_right, mul_pow, inv_pow] at hx
    have he : (‖x‖ ^ 2)⁻¹ * ⟪w, x⟫ ^ 2 = ⟪w, x⟫ ^ 2 / ‖x‖ ^ 2 := by ring
    rw [he] at hx
    exact (le_div_iff₀ hn).mp hx
  exact (measureReal_mono hsub).trans (directional_tail n t ht.le ht2 w hw)

end Bilevel.SphericalGaussian
