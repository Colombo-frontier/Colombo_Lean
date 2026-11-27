import Nonsmooth.NestedCircularPath

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) (f : E → ℝ)

def nestedCircularNormal (i : ℕ) : E :=
  subspaceCircularNormal (nestedCircularSpace R ε N hR hε hε1 f i) N
    (nestedCircularIndex R ε N hR hε hε1 f i)

def nestedCircularRadial (i : ℕ) : E :=
  let K := nestedCircularSpace R ε N hR hε hε1 f i
  circleArc (subspaceCircularFrame K).1 (subspaceCircularFrame K).2
    (2 * Real.pi * (nestedCircularIndex R ε N hR hε hε1 f i : ℝ) / (4 * 2 ^ N))

def nestedCircularOffset (D i : ℕ) : E :=
  (nestedCircularApex R ε N hR hε hε1 f (i + 1) - nestedCircularApex R ε N hR hε hε1 f D) -
    (shrinkingCircularRadius R ε N i * (1 - Real.cos (circularGridAngle N))) •
      nestedCircularRadial R ε N hR hε hε1 f i

theorem nestedCircularSpace_at_least_two (i : ℕ) (hi : i < Module.finrank ℝ E - 1) :
    2 ≤ Module.finrank ℝ (nestedCircularSpace R ε N hR hε hε1 f i) := by
  rw [nestedCircularSpace_dimension]
  omega

theorem nestedCircularNormal_unit (i : ℕ) (hi : i < Module.finrank ℝ E - 1) :
    ‖nestedCircularNormal R ε N hR hε hε1 f i‖ = 1 :=
  subspaceCircularNormal_unit _ _ _ (nestedCircularSpace_at_least_two R ε N hR hε hε1 f i hi)

theorem nestedCircularNormal_mem (i : ℕ) :
    nestedCircularNormal R ε N hR hε hε1 f i ∈ nestedCircularSpace R ε N hR hε hε1 f i :=
  subspaceCircularNormal_mem _ _ _

theorem nestedCircularRadial_unit (i : ℕ) (hi : i < Module.finrank ℝ E - 1) :
    ‖nestedCircularRadial R ε N hR hε hε1 f i‖ = 1 := by
  obtain ⟨_, _, hu, hv, huv⟩ := subspaceCircularFrame_spec _
    (nestedCircularSpace_at_least_two R ε N hR hε hε1 f i hi)
  exact circleArc_norm hu hv huv _

theorem nestedCircularRadial_mem_next (i : ℕ) (hi : i < Module.finrank ℝ E - 1) :
    nestedCircularRadial R ε N hR hε hε1 f i ∈ nestedCircularSpace R ε N hR hε hε1 f (i + 1) := by
  obtain ⟨huK, hvK, hu, hv, huv⟩ := subspaceCircularFrame_spec _
    (nestedCircularSpace_at_least_two R ε N hR hε hε1 f i hi)
  rw [nestedCircularSpace_succ]
  exact circleArc_mem_next_section _ huK hvK hu hv huv _

theorem nestedCircularSpace_orthogonal_flag (i : ℕ) :
    nestedCircularSpace R ε N hR hε hε1 f (i + 1) =
      nestedCircularSpace R ε N hR hε hε1 f i ⊓ (ℝ ∙ nestedCircularNormal R ε N hR hε hε1 f i)ᗮ := rfl

theorem nestedCircularOffset_eq_grid_offset (D i : ℕ) :
    nestedCircularOffset R ε N hR hε hε1 f D i =
      let K := nestedCircularSpace R ε N hR hε hε1 f i
      let y := nestedCircularApex R ε N hR hε hε1 f i
      let r := shrinkingCircularRadius R ε N i
      circularNeighborOffset (y - r • (subspaceCircularFrame K).1)
        (subspaceCircularFrame K).1 (subspaceCircularFrame K).2 r N
        (nestedCircularIndex R ε N hR hε hε1 f i) (nestedCircularApex R ε N hR hε hε1 f D) := by
  dsimp only [nestedCircularOffset, nestedCircularRadial]
  rw [nestedCircularApex_succ]
  rfl

theorem nestedCircular_neighbors_representation (D i : ℕ) :
    let K := nestedCircularSpace R ε N hR hε hε1 f i
    let y := nestedCircularApex R ε N hR hε hε1 f i
    let r := shrinkingCircularRadius R ε N i
    let j := nestedCircularIndex R ε N hR hε hε1 f i
    let x := nestedCircularApex R ε N hR hε hε1 f D
    let w := nestedCircularOffset R ε N hR hε hε1 f D i
    let n := nestedCircularNormal R ε N hR hε hε1 f i
    subspaceCircularPoint K y r N (j - 1) = x + w - (r * Real.sin (circularGridAngle N)) • n ∧
    subspaceCircularPoint K y r N (j + 1) = x + w + (r * Real.sin (circularGridAngle N)) • n := by
  dsimp only
  rw [nestedCircularOffset_eq_grid_offset]
  exact circular_neighbors_offset_representation _ _ _ _ _ _ _

end
end Nonsmooth
