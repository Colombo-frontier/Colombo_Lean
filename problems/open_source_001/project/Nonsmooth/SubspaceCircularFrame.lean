import Nonsmooth.SubspaceCircularGeometry
import Nonsmooth.AnchoredCircularPeak

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def subspaceCircularFrame (K : Submodule ℝ E) : E × E :=
  if h : 2 ≤ Module.finrank ℝ K then
    let hex := exists_orthonormal_pair_in_subspace K h
    (Classical.choose hex, Classical.choose (Classical.choose_spec hex))
  else (0, 0)

theorem subspaceCircularFrame_spec (K : Submodule ℝ E) (hd : 2 ≤ Module.finrank ℝ K) :
    (subspaceCircularFrame K).1 ∈ K ∧ (subspaceCircularFrame K).2 ∈ K ∧
      ‖(subspaceCircularFrame K).1‖ = 1 ∧ ‖(subspaceCircularFrame K).2‖ = 1 ∧
      ⟪(subspaceCircularFrame K).1, (subspaceCircularFrame K).2⟫_ℝ = 0 := by
  simp only [subspaceCircularFrame, dif_pos hd]
  exact Classical.choose_spec (Classical.choose_spec (exists_orthonormal_pair_in_subspace K hd))

theorem subspaceCircularFrame_eq_zero (K : Submodule ℝ E) (hd : Module.finrank ℝ K < 2) :
    subspaceCircularFrame K = (0, 0) := by simp only [subspaceCircularFrame, dif_neg (not_le.mpr hd)]

theorem subspaceCircularFrame_mem (K : Submodule ℝ E) :
    (subspaceCircularFrame K).1 ∈ K ∧ (subspaceCircularFrame K).2 ∈ K := by
  by_cases hd : 2 ≤ Module.finrank ℝ K
  · exact ⟨(subspaceCircularFrame_spec K hd).1, (subspaceCircularFrame_spec K hd).2.1⟩
  · rw [subspaceCircularFrame_eq_zero K (lt_of_not_ge hd)]
    exact ⟨K.zero_mem, K.zero_mem⟩

def subspaceCircularPoint (K : Submodule ℝ E) (y : E) (r : ℝ) (N : ℕ) (j : ℤ) : E :=
  circularQueryPoint (y - r • (subspaceCircularFrame K).1)
    (subspaceCircularFrame K).1 (subspaceCircularFrame K).2 r N j

theorem subspaceCircularPoint_anchor (K : Submodule ℝ E) (y : E) (r : ℝ) (N : ℕ) :
    subspaceCircularPoint K y r N 0 = y := circularQueryPoint_anchor y _ _ r N

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem subspaceCircularPoint_periodic (K : Submodule ℝ E) (y : E) (r : ℝ) (N : ℕ) :
    Function.Periodic (subspaceCircularPoint K y r N) (4 * 2 ^ N) :=
  circularQueryPoint_periodic _ _ _ r N

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem subspaceCircularPoint_mem_plane (K : Submodule ℝ E) (y : E) (r : ℝ) (N : ℕ) (j : ℤ) :
    subspaceCircularPoint K y r N j - y ∈ K :=
  circularQueryPoint_anchor_mem_plane K y (subspaceCircularFrame_mem K).1 (subspaceCircularFrame_mem K).2 r N j

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem subspaceCircularPoint_terminal (K : Submodule ℝ E) (y : E) (r : ℝ) (N : ℕ) (j : ℤ)
    (hd : Module.finrank ℝ K < 2) : subspaceCircularPoint K y r N j = y := by
  simp only [subspaceCircularPoint, subspaceCircularFrame_eq_zero K hd, circularQueryPoint,
    circleArc, smul_zero, add_zero, sub_zero]

theorem subspaceCircularPoint_displacement (K : Submodule ℝ E) (y : E) {r : ℝ}
    (hr : 0 ≤ r) (N : ℕ) (j : ℤ) : ‖subspaceCircularPoint K y r N j - y‖ ≤ 2 * r := by
  by_cases hd : 2 ≤ Module.finrank ℝ K
  · obtain ⟨_, _, hu, hv, huv⟩ := subspaceCircularFrame_spec K hd
    exact circularQueryPoint_anchor_displacement hu hv huv hr N j
  · rw [subspaceCircularPoint_terminal K y r N j (lt_of_not_ge hd), sub_self, norm_zero]
    positivity

end
end Nonsmooth
