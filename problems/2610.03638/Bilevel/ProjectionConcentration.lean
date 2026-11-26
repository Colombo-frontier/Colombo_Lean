import Bilevel.ProjectionPosterior
import Bilevel.ProjectionQuery
import Bilevel.InvariantTail

/-! Spherical concentration for actual projection-conditioned frame laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.ProjectionConcentration
open EuclideanGaussian OrthogonalAction ProjectionStabilizer ProjectionGeometry ProjectionPosterior
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

theorem orthonormal_measurable (d T : ℕ) : MeasurableSet {U : Frame d T | Orthonormal ℝ U} := by
  simp only [orthonormal_iff_ite, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i : Fin T => MeasurableSet.iInter (fun j : Fin T =>
    measurableSet_eq_fun ((continuous_apply i).inner (continuous_apply j)).measurable measurable_const))

theorem haar_orthonormal_ae (d T : ℕ) (hT : T ≤ d) :
    ∀ᵐ U ∂HaarFrame.frameLaw d T hT, Orthonormal ℝ U := by
  rw [HaarFrame.frameLaw]
  exact (ae_map_iff (HaarFrame.frame_measurable d T hT).aemeasurable
    (orthonormal_measurable d T)).2
    (Filter.Eventually.of_forall (HaarFrame.frame_orthonormal d T hT))

theorem conditioned_orthonormal {Y : Type*} [MeasurableSpace Y]
    (d T : ℕ) (μ : Measure (Frame d T)) [IsProbabilityMeasure μ]
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) (o : Frame d T → Y) (ho : Measurable o) :
    ∀ᵐ y ∂μ.map o, ∀ᵐ U ∂condDistrib id o μ y, Orthonormal ℝ U :=
  ConditionalSupport.support μ o ho _ (orthonormal_measurable d T) hU

theorem residual_inner (d : ℕ) (V : Submodule ℝ (Space d)) (w x : Space d)
    (hw : w ∈ Vᗮ) : ⟪w,ProjectionGeometry.residual V x⟫ = ⟪w,x⟫ := by
  rw [ProjectionGeometry.residual, inner_sub_right,
    Submodule.inner_left_of_mem_orthogonal (project_mem V x) hw, sub_zero]

theorem column_orbit_tail (d T : ℕ) (V : Submodule ℝ (Space d)) (n : ℕ)
    (hn : Module.finrank ℝ Vᗮ = n+1) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w : Space d) (hw : w ∈ Vᗮ) (hwn : ‖w‖ = 1) (U : Frame d T)
    (i : Fin T) (hU : ‖U i‖ ≤ 1) :
    (ProjectionStabilizer.law d V).real {A : subgroup d V | t ≤ ⟪w,(A • U) i⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) := by
  let w' : Vᗮ := ⟨w,hw⟩
  let x' : Vᗮ := ⟨ProjectionGeometry.residual V (U i),
    Submodule.sub_orthogonalProjection_mem_orthogonal (U i)⟩
  have hx : ‖x'‖ ≤ 1 := (ProjectionQuery.residual_norm_le V (U i)).trans hU
  have he : ∀ A : subgroup d V, ⟪w',(A • x' : Vᗮ)⟫ = ⟪w,(A • U) i⟫ := by
    intro A
    change ⟪w,A.val • ProjectionGeometry.residual V (U i)⟫ = ⟪w,A.val • U i⟫
    rw [← residual_equivariant d V A (U i), residual_inner d V w _ hw]
  have h := ResidualRotation.directional_tail_unit_ball d V n hn t ht ht2 w' x' hwn hx
  simpa only [he] using h

theorem column_tail (d T : ℕ) (V : Submodule ℝ (Space d)) (n : ℕ)
    (hn : Module.finrank ℝ Vᗮ = n+1) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T V μ)
    (w : Space d) (hw : w ∈ Vᗮ) (hwn : ‖w‖ = 1) (i : Fin T)
    (hU : ∀ᵐ U ∂μ, ‖U i‖ ≤ 1) :
    μ.real {U | t ≤ ⟪w,U i⟫ ^ 2} ≤ 2 * Real.exp (-(n : ℝ) * t / 8) := by
  apply InvariantTail.real_event_bound (ProjectionStabilizer.law d V) μ hμ
    {U | t ≤ ⟪w,U i⟫ ^ 2}
    (measurableSet_le measurable_const ((continuous_const.inner (continuous_apply i)).measurable.pow_const 2))
    _ (by positivity)
  filter_upwards [hU] with U hU
  exact column_orbit_tail d T V n hn t ht ht2 w hw hwn U i hU

theorem query_tail (d T : ℕ) (V : Submodule ℝ (Space d)) (n : ℕ)
    (hn : Module.finrank ℝ Vᗮ = n+1) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T V μ)
    (w : Space d) (hw : w ∈ Vᗮ) (hwn : ‖w‖ = 1)
    (hU : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1) :
    μ.real {U | ∃ i : Fin T, t ≤ ⟪w,U i⟫ ^ 2} ≤ (T : ℝ) * (2 * Real.exp (-(n : ℝ) * t / 8)) := by
  have he : {U : Frame d T | ∃ i : Fin T, t ≤ ⟪w,U i⟫ ^ 2} =
      ⋃ i : Fin T, {U | t ≤ ⟪w,U i⟫ ^ 2} := by ext U; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _i : Fin T, 2 * Real.exp (-(n : ℝ) * t / 8) := by
      apply Finset.sum_le_sum
      intro i _
      exact column_tail d T V n hn t ht ht2 μ hμ w hw hwn i (hU.mono (fun _ h => h i))
    _ = _ := by simp

theorem query_tail_dimension (d T : ℕ) (V : Submodule ℝ (Space d)) (n : ℕ)
    (hn : n+1 ≤ Module.finrank ℝ Vᗮ) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T V μ)
    (w : Space d) (hw : w ∈ Vᗮ) (hwn : ‖w‖ = 1)
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) :
    μ.real {U | ∃ i : Fin T, t ≤ ⟪w,U i⟫ ^ 2} ≤ (T : ℝ) * (2 * Real.exp (-(n : ℝ) * t / 8)) := by
  let k := Module.finrank ℝ Vᗮ - 1
  have hk : Module.finrank ℝ Vᗮ = k+1 := by dsimp [k]; omega
  have hnk : n ≤ k := by omega
  have h := query_tail d T V k hk t ht ht2 μ hμ w hw hwn
    (hU.mono (fun _ h i => (h.norm_eq_one i).le))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hc : (n : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hnk
  nlinarith

end Bilevel.ProjectionConcentration
