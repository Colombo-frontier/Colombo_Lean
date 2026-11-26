import Bilevel.ProjectionObservation

/-! Arbitrary query vectors and their normalized residual have exactly the same enlarged span. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ProjectionNormalization
open EuclideanGaussian ProjectionGeometry

theorem direction_mem (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d) :
    revelationDirection V q ∈ Vᗮ :=
  Vᗮ.smul_mem _ (Submodule.sub_orthogonalProjection_mem_orthogonal q)

theorem direction_norm (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d)
    (hq : ProjectionGeometry.residual V q ≠ 0) : ‖revelationDirection V q‖ = 1 := by
  have hn : ‖ProjectionGeometry.residual V q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp [revelationDirection,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hn]

theorem unchanged (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d)
    (hq : ProjectionGeometry.residual V q = 0) : V ⊔ Submodule.span ℝ {q} = V := by
  apply sup_eq_left.mpr
  apply Submodule.span_le.mpr
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  rw [show q = project V q from sub_eq_zero.mp hq]
  exact project_mem V q

theorem span_eq (d : ℕ) (V : Submodule ℝ (Space d)) (q : Space d)
    (hq : ProjectionGeometry.residual V q ≠ 0) :
    V ⊔ Submodule.span ℝ {q} = V ⊔ Submodule.span ℝ {revelationDirection V q} := by
  let W := V ⊔ Submodule.span ℝ {revelationDirection V q}
  have hdir : revelationDirection V q ∈ W :=
    (show Submodule.span ℝ {revelationDirection V q} ≤ W from le_sup_right)
      (Submodule.mem_span_singleton_self _)
  have hnorm : ‖ProjectionGeometry.residual V q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hres : ProjectionGeometry.residual V q ∈ W := by
    have h := W.smul_mem ‖ProjectionGeometry.residual V q‖ hdir
    simpa only [revelationDirection,smul_smul,mul_inv_cancel₀ hnorm,one_smul] using h
  have hqW : q ∈ W := by
    have h := W.add_mem ((show V ≤ W from le_sup_left) (project_mem V q)) hres
    simpa [ProjectionGeometry.residual] using h
  apply le_antisymm
  · exact sup_le le_sup_left (Submodule.span_le.mpr (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hqW))
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    apply (V ⊔ Submodule.span ℝ {q}).smul_mem
    exact (V ⊔ Submodule.span ℝ {q}).sub_mem
      ((show Submodule.span ℝ {q} ≤ V ⊔ Submodule.span ℝ {q} from le_sup_right)
        (Submodule.mem_span_singleton_self q))
      ((show V ≤ V ⊔ Submodule.span ℝ {q} from le_sup_left) (project_mem V q))

end Bilevel.ProjectionNormalization
