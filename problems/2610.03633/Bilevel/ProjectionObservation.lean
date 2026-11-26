import Bilevel.ProjectionQuery
import Bilevel.ProjectionPosterior

/-! Reconstruction of every full projection from the scalar-query and column-revelation observations. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ProjectionObservation
open EuclideanGaussian ProjectionGeometry ProjectionPosterior

theorem nested_projection (d : ℕ) (V W : Submodule ℝ (Space d)) (hVW : V ≤ W) (x : Space d) :
    project V (project W x) = project V x := by
  exact congrArg Subtype.val (Submodule.orthogonalProjection_orthogonalProjection_of_le hVW x)

theorem query_projection (d : ℕ) (V : Submodule ℝ (Space d)) (w x : Space d)
    (hw : w ∈ Vᗮ) (hn : ‖w‖ = 1) :
    project (V ⊔ Submodule.span ℝ {w}) x = project V x + ⟪w,x⟫ • w := by
  have hp := ProjectionQuery.project_zero_of_orthogonal V w hw
  have he : energy V w = 0 := by simp [energy,hp]
  have hd : revelationDirection V w = w := by
    simp [revelationDirection,ProjectionGeometry.residual,hp,hn]
  rw [revealedProject_eq_projection_sup V w x hn (by rw [he]; norm_num), revealedProject, hd,
    real_inner_comm x w]

def queryUpdate (d T : ℕ) (Z : Frame d T) (w : Space d) (y : Fin T → ℝ) : Frame d T :=
  fun i => Z i + y i • w

theorem query_update_correct (d T : ℕ) (V : Submodule ℝ (Space d)) (w : Space d)
    (hw : w ∈ Vᗮ) (hn : ‖w‖ = 1) (U : Frame d T) :
    queryUpdate d T (fun i => project V (U i)) w (queryObservation d T w U) =
      fun i => project (V ⊔ Submodule.span ℝ {w}) (U i) := by
  funext i
  exact (query_projection d V w (U i) hw hn).symm

def revealUpdate (d T : ℕ) (Z : Frame d T) (j : Fin T) (y : Space d) : Frame d T :=
  fun i => Z i + (((if i=j then 1 else 0)-⟪Z i,Z j⟫) / ‖y-Z j‖^2) • (y-Z j)

theorem reveal_update_correct (d T : ℕ) (V : Submodule ℝ (Space d))
    (U : Frame d T) (hU : Orthonormal ℝ U) (j : Fin T) :
    revealUpdate d T (fun i => project V (U i)) j (U j) =
      fun i => project (V ⊔ Submodule.span ℝ {U j}) (U i) := by
  funext i
  have hnorm := hU.norm_eq_one j
  by_cases hz : ProjectionGeometry.residual V (U j) = 0
  · have hmem : U j ∈ V := by
      have he : U j = project V (U j) := sub_eq_zero.mp hz
      rw [he]
      exact project_mem V (U j)
    have hspan : Submodule.span ℝ {U j} ≤ V := Submodule.span_le.mpr (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hmem)
    have hz' : U j-project V (U j) = 0 := hz
    simp [revealUpdate,hz',sup_eq_left.mpr hspan]
  · have hn : 0 < ‖ProjectionGeometry.residual V (U j)‖ := norm_pos_iff.mpr hz
    have hs := residual_norm_square V (U j)
    have he : energy V (U j) < 1 := by rw [hnorm] at hs; nlinarith [sq_pos_of_pos hn]
    have hi : ⟪U i,ProjectionGeometry.residual V (U j)⟫ =
        (if i=j then 1 else 0)-⟪project V (U i),project V (U j)⟫ := by
      rw [ProjectionGeometry.residual,inner_sub_right,inner_project,orthonormal_iff_ite.mp hU i j]
    rw [revealedProject_eq_projection_sup V (U j) (U i) hnorm he]
    unfold revealUpdate revealedProject revelationDirection
    rw [real_inner_smul_right,smul_smul,hi]
    change project V (U i) + _ • ProjectionGeometry.residual V (U j) = _
    congr 2
    dsimp only [ProjectionGeometry.residual]
    ring

end Bilevel.ProjectionObservation
