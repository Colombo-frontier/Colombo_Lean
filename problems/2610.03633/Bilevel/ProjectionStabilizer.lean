import Bilevel.OrthogonalAction
import Bilevel.ProjectionGeometry
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-! Actual compact symmetry groups fixing the observed projection subspace. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.ProjectionStabilizer
open EuclideanGaussian OrthogonalAction ProjectionGeometry
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000

def subgroup (d : ℕ) (V : Submodule ℝ (Space d)) : Subgroup (OrthogonalHaar.Group d) :=
  fixingSubgroup (OrthogonalHaar.Group d) (V : Set (Space d))

theorem membership (d : ℕ) (V : Submodule ℝ (Space d)) (A : OrthogonalHaar.Group d) :
    A ∈ subgroup d V ↔ ∀ y ∈ V, A • y = y := mem_fixingSubgroup_iff _

theorem carrier_closed (d : ℕ) (V : Submodule ℝ (Space d)) :
    IsClosed (subgroup d V : Set (OrthogonalHaar.Group d)) := by
  have he : (subgroup d V : Set (OrthogonalHaar.Group d)) =
      ⋂ y : V, {A | A • (y : Space d) = y} := by
    ext A
    change A ∈ subgroup d V ↔ _
    rw [membership]
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h y => h y y.property, fun h y hy => h ⟨y, hy⟩⟩
  rw [he]
  apply isClosed_iInter
  intro y
  have hm : Continuous (fun A : OrthogonalHaar.Group d => (A, (y : Space d))) :=
    continuous_id.prodMk continuous_const
  have hc := (action_continuous d).comp hm
  change Continuous (fun A : OrthogonalHaar.Group d => A • (y : Space d)) at hc
  exact isClosed_eq hc (continuous_const : Continuous (fun _ : OrthogonalHaar.Group d => (y : Space d)))

instance compact (d : ℕ) (V : Submodule ℝ (Space d)) : CompactSpace (subgroup d V) :=
  isCompact_iff_compactSpace.mp (carrier_closed d V).isCompact

instance measurableSpace (d : ℕ) (V : Submodule ℝ (Space d)) : MeasurableSpace (subgroup d V) :=
  borel (subgroup d V)

instance borelSpace (d : ℕ) (V : Submodule ℝ (Space d)) : BorelSpace (subgroup d V) := ⟨rfl⟩

instance secondCountable (d : ℕ) (V : Submodule ℝ (Space d)) : SecondCountableTopology (subgroup d V) :=
  TopologicalSpace.secondCountableTopology_induced _ _ (fun A : subgroup d V => A.val)

def law (d : ℕ) (V : Submodule ℝ (Space d)) : Measure (subgroup d V) :=
  Measure.haarMeasure ⊤

instance probability (d : ℕ) (V : Submodule ℝ (Space d)) : IsProbabilityMeasure (law d V) :=
  ⟨Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (subgroup d V)))⟩

instance leftInvariant (d : ℕ) (V : Submodule ℝ (Space d)) : Measure.IsMulLeftInvariant (law d V) :=
  Measure.isMulLeftInvariant_haarMeasure _

instance rightInvariant (d : ℕ) (V : Submodule ℝ (Space d)) : Measure.IsMulRightInvariant (law d V) := by
  refine ⟨fun A => ?_⟩
  have h := Measure.haarMeasure_unique ((law d V).map (fun B => B * A))
    (⊤ : TopologicalSpace.PositiveCompacts (subgroup d V))
  simpa only [TopologicalSpace.PositiveCompacts.coe_top, Measure.map_apply
    (measurable_mul_const A) MeasurableSet.univ, Set.preimage_univ, measure_univ,
    one_smul] using h

theorem fixed_inner (d : ℕ) (V : Submodule ℝ (Space d)) (A : subgroup d V)
    (x y : Space d) (hy : y ∈ V) : ⟪A.val • x, y⟫ = ⟪x, y⟫ := by
  have h := (isometry d A.val).inner_map_map x y
  have hf := (membership d V A.val).mp A.property y hy
  change ⟪A.val • x, A.val • y⟫ = _ at h
  rwa [hf] at h

theorem projection_invariant (d : ℕ) (V : Submodule ℝ (Space d)) (A : subgroup d V)
    (x : Space d) : project V (A.val • x) = project V x := by
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero (project_mem V x)
  intro y hy
  have h := Submodule.orthogonalProjection_inner_eq_zero x y hy
  change ⟪x - project V x, y⟫ = 0 at h
  rw [inner_sub_left] at h ⊢
  rw [fixed_inner d V A x y hy]
  exact h

theorem residual_equivariant (d : ℕ) (V : Submodule ℝ (Space d)) (A : subgroup d V)
    (x : Space d) : ProjectionGeometry.residual V (A.val • x) = A.val • ProjectionGeometry.residual V x := by
  have hf := (membership d V A.val).mp A.property (project V x) (project_mem V x)
  simp only [ProjectionGeometry.residual, projection_invariant]
  change A.val • x - project V x = isometry d A.val (x - project V x)
  rw [map_sub]
  exact congrArg (fun v => A.val • x - v) hf.symm

theorem projection_observation_invariant (d T : ℕ) (V : Submodule ℝ (Space d))
    (A : subgroup d V) (U : Fin T → Space d) :
    (fun i => project V (A.val • U i)) = (fun i => project V (U i)) := by
  funext i
  exact projection_invariant d V A (U i)

theorem orthogonal_mem_preserved (d : ℕ) (V : Submodule ℝ (Space d))
    (A : subgroup d V) (x : Space d) (hx : x ∈ Vᗮ) : A.val • x ∈ Vᗮ := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [fixed_inner d V A x y hy]
  exact hx y hy

theorem transitive_on_residual_sphere (d : ℕ) (V : Submodule ℝ (Space d))
    (x y : Space d) (hx : x ∈ Vᗮ) (hy : y ∈ Vᗮ) (hn : ‖x‖ = ‖y‖) :
    ∃ A : subgroup d V, A.val • x = y := by
  let U : Space d ≃ₗᵢ[ℝ] Space d := (Submodule.span ℝ {x-y})ᗮ.reflection
  have hfix : matrixOfIsometry d U ∈ subgroup d V := by
    rw [membership]
    intro z hz
    rw [action_apply, isometry_matrixOfIsometry]
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact Submodule.inner_right_of_mem_orthogonal hz (Vᗮ.sub_mem hx hy)
  refine ⟨⟨matrixOfIsometry d U, hfix⟩, ?_⟩
  rw [action_apply, isometry_matrixOfIsometry]
  exact Submodule.reflection_sub hn

end Bilevel.ProjectionStabilizer
