import Bilevel.ProjectionStabilizer
import Bilevel.HomogeneousSphere

/-! The projection stabilizer rotates the true orthogonal residual space transitively. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.ResidualRotation
open EuclideanGaussian OrthogonalAction ProjectionStabilizer
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

instance residualMeasurableSpace (d : ℕ) (V : Submodule ℝ (Space d)) : MeasurableSpace Vᗮ := borel Vᗮ
instance residualBorelSpace (d : ℕ) (V : Submodule ℝ (Space d)) : BorelSpace Vᗮ := ⟨rfl⟩

def rotation (d : ℕ) (V : Submodule ℝ (Space d)) (A : subgroup d V) : Vᗮ ≃ₗᵢ[ℝ] Vᗮ :=
  (show Vᗮ →ₗᵢ[ℝ] Vᗮ from
    { toFun := fun x => ⟨A.val • (x : Space d), orthogonal_mem_preserved d V A x x.property⟩
      map_add' := by intro x y; apply Subtype.ext; exact (isometry d A.val).map_add x y
      map_smul' := by intro c x; apply Subtype.ext; exact (isometry d A.val).map_smul c x
      norm_map' := by intro x; exact (isometry d A.val).norm_map x }).toLinearIsometryEquiv rfl

@[simp] theorem rotation_coe (d : ℕ) (V : Submodule ℝ (Space d)) (A : subgroup d V) (x : Vᗮ) :
    (rotation d V A x : Space d) = A.val • (x : Space d) := rfl

instance action (d : ℕ) (V : Submodule ℝ (Space d)) : MulAction (subgroup d V) Vᗮ where
  smul A x := rotation d V A x
  one_smul x := by
    apply Subtype.ext
    change (1 : OrthogonalHaar.Group d) • (x : Space d) = x
    exact one_smul _ _
  mul_smul A B x := by
    apply Subtype.ext
    change ((A.val * B.val) • (x : Space d)) = A.val • (B.val • (x : Space d))
    exact mul_smul _ _ _

@[simp] theorem action_coe (d : ℕ) (V : Submodule ℝ (Space d)) (A : subgroup d V) (x : Vᗮ) :
    ((A • x : Vᗮ) : Space d) = A.val • (x : Space d) := rfl

theorem action_continuous (d : ℕ) (V : Submodule ℝ (Space d)) :
    Continuous (fun p : subgroup d V × Vᗮ => p.1 • p.2) := by
  have hm : Continuous (fun p : subgroup d V × Vᗮ => (p.1.val, (p.2 : Space d))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hc := (OrthogonalAction.action_continuous d).comp hm
  change Continuous (fun p : subgroup d V × Vᗮ => p.1.val • (p.2 : Space d)) at hc
  change Continuous (fun p : subgroup d V × Vᗮ =>
    (⟨p.1.val • (p.2 : Space d), orthogonal_mem_preserved d V p.1 p.2 p.2.property⟩ : Vᗮ))
  exact hc.subtype_mk _

instance measurableAction (d : ℕ) (V : Submodule ℝ (Space d)) : MeasurableSMul₂ (subgroup d V) Vᗮ :=
  ⟨(action_continuous d V).measurable⟩

theorem transitive (d : ℕ) (V : Submodule ℝ (Space d)) (x y : Vᗮ) (hn : ‖x‖ = ‖y‖) :
    ∃ A : subgroup d V, A • x = y := by
  obtain ⟨A, hA⟩ := transitive_on_residual_sphere d V x y x.property y.property hn
  exact ⟨A, Subtype.ext hA⟩

def coordinates (d : ℕ) (V : Submodule ℝ (Space d)) (n : ℕ)
    (hn : Module.finrank ℝ Vᗮ = n+1) : Vᗮ ≃ₗᵢ[ℝ] Space (n+1) :=
  ((stdOrthonormalBasis ℝ Vᗮ).reindex (finCongr hn)).repr

theorem directional_tail (d : ℕ) (V : Submodule ℝ (Space d)) (n : ℕ)
    (hn : Module.finrank ℝ Vᗮ = n+1) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w x : Vᗮ) (hw : ‖w‖ = 1) (hx : ‖x‖ = 1) :
    (ProjectionStabilizer.law d V).real {A : subgroup d V | t ≤ ⟪w, (A • x : Vᗮ)⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) :=
  HomogeneousSphere.directional_tail (ProjectionStabilizer.law d V) (coordinates d V n hn)
    (rotation d V) (fun _ _ => rfl) (transitive d V) t ht ht2 w x hw hx

theorem directional_tail_unit_ball (d : ℕ) (V : Submodule ℝ (Space d)) (n : ℕ)
    (hn : Module.finrank ℝ Vᗮ = n+1) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w x : Vᗮ) (hw : ‖w‖ = 1) (hx : ‖x‖ ≤ 1) :
    (ProjectionStabilizer.law d V).real {A : subgroup d V | t ≤ ⟪w, (A • x : Vᗮ)⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) :=
  HomogeneousSphere.directional_tail_unit_ball (ProjectionStabilizer.law d V) (coordinates d V n hn)
    (rotation d V) (fun _ _ => rfl) (transitive d V) t ht ht2 w x hw hx

end Bilevel.ResidualRotation
