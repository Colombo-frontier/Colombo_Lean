import Nonsmooth.SubspaceCircularFrame

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def subspaceCircularNormal (K : Submodule ℝ E) (N : ℕ) (j : ℤ) : E :=
  circleTangent (subspaceCircularFrame K).1 (subspaceCircularFrame K).2
    (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))

def subspaceCircularSection (K : Submodule ℝ E) (N : ℕ) (j : ℤ) : Submodule ℝ E :=
  K ⊓ (ℝ ∙ subspaceCircularNormal K N j)ᗮ

theorem subspaceCircularSection_le (K : Submodule ℝ E) (N : ℕ) (j : ℤ) :
    subspaceCircularSection K N j ≤ K := inf_le_left

theorem subspaceCircularNormal_mem (K : Submodule ℝ E) (N : ℕ) (j : ℤ) :
    subspaceCircularNormal K N j ∈ K :=
  circleTangent_mem_submodule K (subspaceCircularFrame_mem K).1 (subspaceCircularFrame_mem K).2 _

theorem subspaceCircularSection_terminal (K : Submodule ℝ E) (N : ℕ) (j : ℤ)
    (hd : Module.finrank ℝ K < 2) : subspaceCircularSection K N j = K := by
  simp [subspaceCircularSection, subspaceCircularNormal, subspaceCircularFrame_eq_zero K hd, circleTangent]

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem subspaceCircularNormal_unit (K : Submodule ℝ E) (N : ℕ) (j : ℤ)
    (hd : 2 ≤ Module.finrank ℝ K) : ‖subspaceCircularNormal K N j‖ = 1 := by
  obtain ⟨_, _, hu, hv, huv⟩ := subspaceCircularFrame_spec K hd
  exact circleTangent_norm hu hv huv _

theorem subspaceCircularSection_dimension (K : Submodule ℝ E) (N : ℕ) (j : ℤ)
    (hd : 2 ≤ Module.finrank ℝ K) :
    Module.finrank ℝ (subspaceCircularSection K N j) + 1 = Module.finrank ℝ K :=
  subspace_unit_section_dimension K (subspaceCircularNormal_mem K N j) (subspaceCircularNormal_unit K N j hd)

end
end Nonsmooth
