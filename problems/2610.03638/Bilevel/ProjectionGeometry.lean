import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Deterministic geometry of the projection genie. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ProjectionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def project (V : Submodule ℝ E) (u : E) : E := V.orthogonalProjection u
def residual (V : Submodule ℝ E) (u : E) : E := u - project V u
def energy (V : Submodule ℝ E) (u : E) : ℝ := ‖project V u‖ ^ 2

theorem project_mem (V : Submodule ℝ E) (u : E) : project V u ∈ V :=
  (V.orthogonalProjection u).property

theorem residual_project_inner (V : Submodule ℝ E) (u v : E) :
    ⟪residual V u, project V v⟫ = 0 :=
  Submodule.orthogonalProjection_inner_eq_zero u (project V v) (project_mem V v)

theorem inner_project (V : Submodule ℝ E) (u v : E) :
    ⟪u, project V v⟫ = ⟪project V u, project V v⟫ := by
  have h := residual_project_inner V u v
  simp only [residual, inner_sub_left] at h
  linarith

theorem project_inner (V : Submodule ℝ E) (u v : E) :
    ⟪project V u, v⟫ = ⟪project V u, project V v⟫ := by
  rw [real_inner_comm, inner_project, real_inner_comm]

theorem residual_inner (V : Submodule ℝ E) (u v : E) :
    ⟪residual V u, residual V v⟫ = ⟪u, v⟫ - ⟪project V u, project V v⟫ := by
  simp only [residual, inner_sub_left, inner_sub_right]
  rw [inner_project V u v, project_inner V u v]
  ring

theorem residual_norm_square (V : Submodule ℝ E) (u : E) :
    ‖residual V u‖ ^ 2 = ‖u‖ ^ 2 - energy V u := by
  simpa only [real_inner_self_eq_norm_sq, energy] using residual_inner V u u

theorem residual_pair_orthogonal (V : Submodule ℝ E) (u v : E) (huv : ⟪u, v⟫ = 0) :
    ⟪residual V u, residual V v⟫ = -⟪project V u, project V v⟫ := by
  rw [residual_inner, huv, zero_sub]

def revelationDirection (V : Submodule ℝ E) (v : E) : E := ‖residual V v‖⁻¹ • residual V v
def revealedProject (V : Submodule ℝ E) (v u : E) : E :=
  project V u + ⟪u, revelationDirection V v⟫ • revelationDirection V v

theorem revelation_direction_norm (V : Submodule ℝ E) (v : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) : ‖revelationDirection V v‖ = 1 := by
  have hsq := residual_norm_square V v
  rw [hv] at hsq
  have hn : 0 < ‖residual V v‖ := by nlinarith [norm_nonneg (residual V v)]
  simp [revelationDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hn, hn.ne']

theorem project_revelation_inner (V : Submodule ℝ E) (u v : E) :
    ⟪project V u, revelationDirection V v⟫ = 0 := by
  simp only [revelationDirection, real_inner_smul_right]
  rw [real_inner_comm, residual_project_inner, mul_zero]

theorem revealed_energy (V : Submodule ℝ E) (u v : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) :
    ‖revealedProject V v u‖ ^ 2 = energy V u + ⟪u, revelationDirection V v⟫ ^ 2 := by
  rw [revealedProject, norm_add_sq_real, real_inner_smul_right, project_revelation_inner]
  simp only [mul_zero, norm_smul, Real.norm_eq_abs, revelation_direction_norm V v hv he,
    mul_one, sq_abs, energy]
  ring

theorem revelation_signal_square (V : Submodule ℝ E) (u v : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) (huv : ⟪u, v⟫ = 0) :
    ⟪u, revelationDirection V v⟫ ^ 2 = ⟪project V u, project V v⟫ ^ 2 / (1 - energy V v) := by
  have hinner : ⟪u, residual V v⟫ = -⟪project V u, project V v⟫ := by
    rw [residual, inner_sub_right, huv, inner_project, zero_sub]
  have hsq := residual_norm_square V v
  rw [hv, one_pow] at hsq
  have hn : ‖residual V v‖ ≠ 0 := by nlinarith
  simp only [revelationDirection, real_inner_smul_right, hinner, mul_pow, inv_pow, neg_sq]
  rw [hsq]
  ring

theorem revelation_energy_bound (V : Submodule ℝ E) (u v : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) (huv : ⟪u, v⟫ = 0) :
    ‖revealedProject V v u‖ ^ 2 ≤ energy V u / (1 - energy V v) := by
  have hc := abs_real_inner_le_norm (project V u) (project V v)
  have hc2 : ⟪project V u, project V v⟫ ^ 2 ≤ energy V u * energy V v := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) hc 2
    simpa only [sq_abs, mul_pow, energy] using hp
  rw [revealed_energy V u v hv he, revelation_signal_square V u v hv he huv]
  have hden : 0 < 1 - energy V v := by linarith
  apply (le_div_iff₀ hden).mpr
  have hcancel : (⟪project V u, project V v⟫ ^ 2 / (1 - energy V v)) * (1 - energy V v) =
      ⟪project V u, project V v⟫ ^ 2 := div_mul_cancel₀ _ hden.ne'
  rw [add_mul, hcancel]
  nlinarith

theorem revelation_inner_mem (V : Submodule ℝ E) (v y : E) (hy : y ∈ V) :
    ⟪revelationDirection V v, y⟫ = 0 := by
  simp only [revelationDirection, real_inner_smul_left]
  rw [show ⟪residual V v, y⟫ = 0 from Submodule.orthogonalProjection_inner_eq_zero v y hy, mul_zero]

theorem new_residual_inner_mem (V : Submodule ℝ E) (v u y : E) (hy : y ∈ V) :
    ⟪u - revealedProject V v u, y⟫ = 0 := by
  have h0 : ⟪u - project V u, y⟫ = 0 := Submodule.orthogonalProjection_inner_eq_zero u y hy
  simp only [inner_sub_left] at h0
  simp only [revealedProject, inner_sub_left, inner_add_left, real_inner_smul_left,
    revelation_inner_mem V v y hy, mul_zero, add_zero]
  exact h0

theorem new_residual_inner_direction (V : Submodule ℝ E) (v u : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) :
    ⟪u - revealedProject V v u, revelationDirection V v⟫ = 0 := by
  simp only [revealedProject, inner_sub_left, inner_add_left, real_inner_smul_left,
    project_revelation_inner, real_inner_self_eq_norm_sq, revelation_direction_norm V v hv he]
  ring

theorem revelation_reconstruct (V : Submodule ℝ E) (v : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) :
    v = project V v + ‖residual V v‖ • revelationDirection V v := by
  have hsq := residual_norm_square V v
  rw [hv, one_pow] at hsq
  have hn : ‖residual V v‖ ≠ 0 := by nlinarith
  simp only [revelationDirection, smul_smul]
  rw [mul_inv_cancel₀ hn, one_smul]
  unfold residual
  abel

theorem revealedProject_eq_projection_sup (V : Submodule ℝ E) (v u : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) :
    project (V ⊔ Submodule.span ℝ {v}) u = revealedProject V v u := by
  let W := V ⊔ Submodule.span ℝ {v}
  have hvW : v ∈ W := (show Submodule.span ℝ {v} ≤ W from le_sup_right) (Submodule.mem_span_singleton_self v)
  have hpW : project V u ∈ W := (show V ≤ W from le_sup_left) (project_mem V u)
  have hvpW : project V v ∈ W := (show V ≤ W from le_sup_left) (project_mem V v)
  have hdirW : revelationDirection V v ∈ W :=
    W.smul_mem _ (W.sub_mem hvW hvpW)
  have hcW : revealedProject V v u ∈ W := W.add_mem hpW (W.smul_mem _ hdirW)
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero hcW
  intro y hy
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
  have h0 := new_residual_inner_mem V v u y₀ hy₀
  have h1 : ⟪u - revealedProject V v u, v⟫ = 0 := by
    have hvdecomp := revelation_reconstruct V v hv he
    nth_rw 2 [hvdecomp]
    rw [inner_add_right, real_inner_smul_right, new_residual_inner_mem V v u _ (project_mem V v),
      new_residual_inner_direction V v u hv he, mul_zero, add_zero]
  rw [inner_add_right, real_inner_smul_right, h0, h1, mul_zero, add_zero]

theorem projection_revelation_bound (V : Submodule ℝ E) (u v : E)
    (hv : ‖v‖ = 1) (he : energy V v < 1) (huv : ⟪u, v⟫ = 0) :
    energy (V ⊔ Submodule.span ℝ {v}) u ≤ energy V u / (1 - energy V v) := by
  rw [energy, revealedProject_eq_projection_sup V v u hv he]
  exact revelation_energy_bound V u v hv he huv

end Bilevel.ProjectionGeometry
