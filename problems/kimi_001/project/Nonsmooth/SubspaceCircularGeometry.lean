import Nonsmooth.CircularNeighborLiftGeometry
import Nonsmooth.OrthogonalPlaneBounds
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem circleArc_mem_submodule (K : Submodule ℝ E) {u v : E}
    (hu : u ∈ K) (hv : v ∈ K) (t : ℝ) : circleArc u v t ∈ K :=
  K.add_mem (K.smul_mem _ hu) (K.smul_mem _ hv)

theorem circleTangent_mem_submodule (K : Submodule ℝ E) {u v : E}
    (hu : u ∈ K) (hv : v ∈ K) (t : ℝ) : circleTangent u v t ∈ K :=
  K.add_mem (K.smul_mem _ hu) (K.smul_mem _ hv)

theorem circularQueryPoint_anchor_mem_plane (K : Submodule ℝ E) (y : E) {u v : E}
    (hu : u ∈ K) (hv : v ∈ K) (r : ℝ) (N : ℕ) (j : ℤ) :
    circularQueryPoint (y - r • u) u v r N j - y ∈ K := by
  have heq : circularQueryPoint (y - r • u) u v r N j - y =
      r • (circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) - u) := by
    dsimp only [circularQueryPoint]
    module
  rw [heq]
  exact K.smul_mem _ (K.sub_mem (circleArc_mem_submodule K hu hv _) hu)

theorem circleArc_mem_next_section (K : Submodule ℝ E) {u v : E}
    (huK : u ∈ K) (hvK : v ∈ K) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (t : ℝ) :
    circleArc u v t ∈ K ⊓ (ℝ ∙ circleTangent u v t)ᗮ :=
  ⟨circleArc_mem_submodule K huK hvK t,
    Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (circleArc_inner_circleTangent hu hv huv t)⟩

variable [FiniteDimensional ℝ E]

theorem subspace_unit_section_dimension (K : Submodule ℝ E) {n : E}
    (hnK : n ∈ K) (hn : ‖n‖ = 1) :
    Module.finrank ℝ (K ⊓ (ℝ ∙ n)ᗮ : Submodule ℝ E) + 1 = Module.finrank ℝ K := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have hspan : (ℝ ∙ n : Submodule ℝ E) ≤ K := (Submodule.span_singleton_le_iff_mem n K).mpr hnK
  have hd := Submodule.finrank_add_inf_finrank_orthogonal hspan
  rw [finrank_span_singleton hn0] at hd
  rw [inf_comm] at hd
  omega

theorem exists_orthonormal_pair_in_subspace (K : Submodule ℝ E)
    (hd : 2 ≤ Module.finrank ℝ K) :
    ∃ u v : E, u ∈ K ∧ v ∈ K ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫_ℝ = 0 := by
  let i : Fin (Module.finrank ℝ K) := ⟨0, by omega⟩
  let u : K := stdOrthonormalBasis ℝ K i
  have hu : ‖u‖ = 1 := (stdOrthonormalBasis ℝ K).orthonormal.1 i
  obtain ⟨v, hv, huv⟩ := exists_unit_orthogonal_direction hu hd
  exact ⟨u, v, u.property, v.property, hu, hv, huv⟩

end
end Nonsmooth
