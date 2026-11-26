import Geode.Hyperbolic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Compactness of finite-dimensional hyperbolic metric balls in the actual
hyperboloid metric. The spatial-coordinate parametrization supplies compact
sets, and the distance-to-origin formula identifies the metric balls. -/
namespace Geode.Lorentz

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_ofSpace : Continuous (Point.ofSpace : E → Point E) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc : Continuous (fun w : E =>
      Geode.arcosh (-form E (Point.ofSpace w).val (Point.ofSpace z).val)) := by
    apply Geode.continuous_arcosh.comp
    dsimp [form, Point.ofSpace]
    fun_prop
  have ht := hc.continuousAt (x := z)
  simpa only [ContinuousAt, ← dist_eq_arcosh, dist_self] using ht

@[simp] theorem cosh_dist_origin (x : Point E) :
    Real.cosh (dist (origin : Point E) x) = x.val.1 := by
  rw [cosh_dist]
  simp [form, origin]

theorem dist_origin_eq_arsinh (x : Point E) :
    dist (origin : Point E) x = Real.arsinh ‖x.val.2‖ := by
  have hpos : 0 ≤ Real.arsinh ‖x.val.2‖ := Real.arsinh_nonneg_iff.mpr (norm_nonneg _)
  apply Real.cosh_strictMonoOn.injOn (dist_nonneg : 0 ≤ dist (origin : Point E) x) hpos
  rw [cosh_dist_origin, Real.cosh_arsinh, x.time_eq_sqrt]

theorem mem_closedBall_origin_iff {x : Point E} {R : ℝ} (_hR : 0 ≤ R) :
    x ∈ Metric.closedBall (origin : Point E) R ↔ ‖x.val.2‖ ≤ Real.sinh R := by
  rw [Metric.mem_closedBall, dist_comm, dist_origin_eq_arsinh]
  simpa only [Real.arsinh_sinh] using
    (Real.arsinh_le_arsinh (x := ‖x.val.2‖) (y := Real.sinh R))

theorem closedBall_origin_eq_image {R : ℝ} (hR : 0 ≤ R) :
    Metric.closedBall (origin : Point E) R =
      Point.ofSpace '' Metric.closedBall (0 : E) (Real.sinh R) := by
  ext x
  rw [mem_closedBall_origin_iff hR]
  constructor
  · intro hx
    refine ⟨x.val.2, ?_, Point.ofSpace_spatial_eq x⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  · rintro ⟨z, hz, rfl⟩
    simpa only [Point.ofSpace_spatial, Metric.mem_closedBall, dist_zero_right] using hz

theorem isCompact_closedBall_origin [FiniteDimensional ℝ E] (R : ℝ) :
    IsCompact (Metric.closedBall (origin : Point E) R) := by
  by_cases hR : 0 ≤ R
  · rw [closedBall_origin_eq_image hR]
    exact (isCompact_closedBall (0 : E) (Real.sinh R)).image continuous_ofSpace
  · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hR)]
    exact isCompact_empty

noncomputable instance [FiniteDimensional ℝ E] : ProperSpace (Point E) where
  isCompact_closedBall x R := by
    apply (isCompact_closedBall_origin (E := E) (R + dist x (origin : Point E))).of_isClosed_subset
      Metric.isClosed_closedBall
    intro y hy
    simp only [Metric.mem_closedBall] at hy ⊢
    exact (dist_triangle y x origin).trans (add_le_add_right hy _)

theorem tangent_spatial_sq_le (x : Point E) {v : Ambient E}
    (hv : form E x.val v = 0) : ‖v.2‖ ^ 2 ≤ x.val.1 ^ 2 * form E v v := by
  have hi : @inner ℝ E _ x.val.2 v.2 = x.val.1 * v.1 := by
    unfold form at hv
    linarith
  have hcs := inner_sq_le x.val.2 v.2
  rw [hi, mul_pow, x.time_sq] at hcs
  rw [form_self, x.time_sq]
  nlinarith only [hcs]

/-- Spatial displacement is locally controlled by the actual hyperbolic distance. -/
theorem spatial_dist_le (x y : Point E) :
    ‖y.val.2 - x.val.2‖ ≤ x.val.1 * (Real.exp (dist x y) - 1) := by
  let v := tangentPart x y.val
  have hv := tangentPart_orthogonal x y.val
  have hcs := tangent_spatial_sq_le x hv
  have hform : form E v v = Real.sinh (dist x y) ^ 2 := by
    have hinner : form E x.val y.val = -Real.cosh (dist x y) := by
      rw [cosh_dist]
      ring
    calc
      form E v v = form E y.val y.val + form E x.val y.val * form E x.val y.val :=
        form_tangentPart x y.val y.val
      _ = -1 + (-Real.cosh (dist x y)) * (-Real.cosh (dist x y)) :=
        congrArg₂ (fun a b : ℝ => a + b * b) y.normalized hinner
      _ = Real.sinh (dist x y) ^ 2 := by
        nlinarith [Real.cosh_sq_sub_sinh_sq (dist x y)]
  have hsp : 0 ≤ Real.sinh (dist x y) := Real.sinh_nonneg_iff.mpr dist_nonneg
  have hnorm : ‖v.2‖ ≤ x.val.1 * Real.sinh (dist x y) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg x.future.le hsp)).mp
    change ‖v.2‖ ^ 2 ≤ _ at hcs
    rw [hform] at hcs
    simpa only [mul_pow] using hcs
  have hcoord : y.val.2 - x.val.2 = v.2 + (Real.cosh (dist x y) - 1) • x.val.2 := by
    change y.val.2 - x.val.2 =
      y.val.2 + form E x.val y.val • x.val.2 + (Real.cosh (dist x y) - 1) • x.val.2
    rw [cosh_dist]
    module
  have hxnorm : ‖x.val.2‖ ≤ x.val.1 := by nlinarith [x.time_sq, norm_nonneg x.val.2, x.future]
  have hc : 0 ≤ Real.cosh (dist x y) - 1 := sub_nonneg.mpr (Real.one_le_cosh _)
  calc
    ‖y.val.2 - x.val.2‖ = ‖v.2 + (Real.cosh (dist x y) - 1) • x.val.2‖ := by rw [hcoord]
    _ ≤ ‖v.2‖ + ‖(Real.cosh (dist x y) - 1) • x.val.2‖ := norm_add_le _ _
    _ = ‖v.2‖ + (Real.cosh (dist x y) - 1) * ‖x.val.2‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ x.val.1 * (Real.sinh (dist x y) + Real.cosh (dist x y) - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hxnorm hc]
    _ = x.val.1 * (Real.exp (dist x y) - 1) := by rw [Real.sinh_add_cosh]

theorem continuous_spatial : Continuous (fun x : Point E => x.val.2) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound : ∀ y : Point E, dist y.val.2 x.val.2 ≤
      x.val.1 * (Real.exp (dist x y) - 1) := by
    intro y
    simpa only [dist_eq_norm] using spatial_dist_le x y
  have hc : Continuous (fun y : Point E => x.val.1 * (Real.exp (dist x y) - 1)) := by
    fun_prop
  have ht : Tendsto (fun y : Point E => x.val.1 * (Real.exp (dist x y) - 1)) (𝓝 x) (𝓝 0) := by
    simpa only [ContinuousAt, dist_self, Real.exp_zero, sub_self, mul_zero]
      using hc.continuousAt (x := x)
  exact squeeze_zero (fun _ => dist_nonneg) hbound ht

noncomputable def spatialHomeomorph : Point E ≃ₜ E where
  toEquiv := spatialEquiv
  continuous_toFun := continuous_spatial
  continuous_invFun := continuous_ofSpace

theorem continuous_val : Continuous (fun x : Point E => x.val) := by
  have htime : Continuous (fun x : Point E => x.val.1) := by
    have heq : (fun x : Point E => x.val.1) = (fun x => Real.sqrt (1 + ‖x.val.2‖ ^ 2)) := by
      funext x
      exact x.time_eq_sqrt
    rw [heq]
    exact (continuous_const.add (continuous_spatial.norm.pow 2)).sqrt
  exact htime.prodMk continuous_spatial

end Geode.Lorentz
