import Bilevel.MeasurableReflection

/-! Query insertion and dimension accounting for the projection genie. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ProjectionQuery
open EuclideanGaussian ProjectionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem project_zero_of_orthogonal (V : Submodule ℝ E) (w : E) (hw : w ∈ Vᗮ) :
    project V w = 0 := by
  exact congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hw)

theorem query_energy (V : Submodule ℝ E) (w u : E) (hw : w ∈ Vᗮ) (hn : ‖w‖ = 1) :
    energy (V ⊔ Submodule.span ℝ {w}) u = energy V u + ⟪u,w⟫ ^ 2 := by
  have hp := project_zero_of_orthogonal V w hw
  have he : energy V w = 0 := by simp [energy, hp]
  have hd : revelationDirection V w = w := by simp [revelationDirection, ProjectionGeometry.residual, hp, hn]
  rw [energy, revealedProject_eq_projection_sup V w u hn (by rw [he]; norm_num)]
  rw [revealed_energy V u w hn (by rw [he]; norm_num), hd]

theorem query_energy_le (V : Submodule ℝ E) (w u : E) (hw : w ∈ Vᗮ) (hn : ‖w‖ = 1)
    (b : ℝ) (hb : ⟪u,w⟫ ^ 2 ≤ b) :
    energy (V ⊔ Submodule.span ℝ {w}) u ≤ energy V u + b := by
  rw [query_energy V w u hw hn]
  exact add_le_add_left hb _

theorem finrank_insert_le (V : Submodule ℝ E) (w : E) :
    Module.finrank ℝ (V ⊔ Submodule.span ℝ {w} : Submodule ℝ E) ≤ Module.finrank ℝ V + 1 := by
  by_cases hw : w = 0
  · subst w
    rw [Submodule.span_zero_singleton, sup_bot_eq]
    omega
  · have h := Submodule.finrank_add_le_finrank_add_finrank V (Submodule.span ℝ {w})
    rwa [finrank_span_singleton hw] at h

theorem residual_dimension (V : Submodule ℝ E) (k n : ℕ)
    (hV : Module.finrank ℝ V ≤ k) (hE : k+n ≤ Module.finrank ℝ E) :
    n ≤ Module.finrank ℝ Vᗮ := by
  have h := V.finrank_add_finrank_orthogonal
  omega

theorem residual_norm_le (V : Submodule ℝ E) (u : E) : ‖residual V u‖ ≤ ‖u‖ := by
  have h := residual_norm_square V u
  have he : 0 ≤ energy V u := sq_nonneg _
  nlinarith [norm_nonneg (ProjectionGeometry.residual V u), norm_nonneg u]

theorem query_in_padded_span (d : ℕ) (V : Submodule ℝ (Space d))
    (anchor q : Space d) :
    q ∈ V ⊔ Submodule.span ℝ {MeasurableReflection.direction d anchor (residual V q)} := by
  let W := V ⊔ Submodule.span ℝ {MeasurableReflection.direction d anchor (residual V q)}
  have hp : project V q ∈ W := (show V ≤ W from le_sup_left) (project_mem V q)
  have hr : residual V q ∈ W := by
    by_cases hz : residual V q = 0
    · rw [hz]; exact W.zero_mem
    · have hdir : MeasurableReflection.direction d anchor (residual V q) ∈ W :=
        (show Submodule.span ℝ {_} ≤ W from le_sup_right) (Submodule.mem_span_singleton_self _)
      have hmul := W.smul_mem ‖residual V q‖ hdir
      simpa [MeasurableReflection.direction, hz, smul_smul, norm_ne_zero_iff.mpr hz] using hmul
  have h := W.add_mem hp hr
  simpa [ProjectionGeometry.residual] using h

end Bilevel.ProjectionQuery

