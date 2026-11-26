import Nonsmooth.GaussianPlaneCoordinates
import Nonsmooth.OrthogonalPlaneBounds

open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem finrank_two_le_of_orthonormal_pair {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) :
    2 ≤ Module.finrank ℝ E := by
  let K : Submodule ℝ E := (ℝ ∙ u)ᗮ
  let vK : K := ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ho⟩
  have hvK : ‖vK‖ = 1 := hv
  have hn : vK ≠ 0 := by intro h; simp [h] at hvK
  letI : Nontrivial K := nontrivial_of_ne vK 0 hn
  have hp : 0 < Module.finrank ℝ K := Module.finrank_pos
  have hd := unit_complement_finrank_drop hu
  dsimp only [K] at hp
  omega

theorem exists_unit_orthogonal_to_pair {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0)
    (hd : 3 ≤ Module.finrank ℝ E) :
    ∃ w : E, ‖w‖ = 1 ∧ ⟪u, w⟫_ℝ = 0 ∧ ⟪v, w⟫_ℝ = 0 := by
  let K : Submodule ℝ E := (ℝ ∙ u)ᗮ
  let vK : K := ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ho⟩
  have hvK : ‖vK‖ = 1 := hv
  have hdim : 2 ≤ Module.finrank ℝ K := by
    have h := unit_complement_finrank_drop hu
    dsimp only [K]
    omega
  obtain ⟨w, hw, hvw⟩ := exists_unit_orthogonal_direction hvK hdim
  refine ⟨(w : E), hw, ?_, hvw⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property

end
end Nonsmooth
