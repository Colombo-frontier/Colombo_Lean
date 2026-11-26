import Smoothness2601.CoordinateAlgorithm
import Smoothness2601.Minimax

/-! The actual scalar-lower hard class is covered by the Euclidean-dimension
minimax quantifiers. No algorithm, population or oracle is restricted. -/
noncomputable section
open MeasureTheory
namespace Smoothness2601.CoordinateMinimax

def scalarEquiv : Euclidean 1 ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv :=
    { toFun := fun v => v 0
      invFun := fun y => (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)
      left_inv := by
        intro v
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := by intro y; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  norm_map' v := by
    symm
    simp [EuclideanSpace.norm_eq,Real.sqrt_sq_eq_abs]

/-- Consequence of the exact original BudgetWorks quantifiers, with the lower
coordinate represented by ℝ instead of the isometric EuclideanSpace (Fin 1). -/
theorem budgetWorks_scalar {b : Budgets} {p : WithTop ℕ} {L : ℕ → ℝ} {ε : ℝ} {N : ℕ}
    (hN : BudgetWorks b p L ε N) :
    ∀ dx : ℕ, ∃ A : Adaptive.Algorithm (Euclidean dx) ℝ,
      ∀ P : Population (X := Euclidean dx) (Y := ℝ) b,
      P.HigherRegularity p L → ∀ x₀ y₀, P.Initialized x₀ y₀ →
      ∀ (H : Type) (inst : MeasurableSpace H), letI := inst
        ∀ (O : Adaptive.Oracle P H) (h : H), Adaptive.Succeeds A O N ε h x₀ y₀ := by
  intro dx
  obtain ⟨A,hA⟩ := hN dx 1
  refine ⟨CoordinateAlgorithm.pull A scalarEquiv,?_⟩
  intro P hreg x₀ y₀ hi H inst O h
  apply CoordinateAlgorithm.succeeds A scalarEquiv P O N ε h x₀ y₀
  exact hA (CoordinatePopulation.transport P scalarEquiv)
    (CoordinatePopulation.higherRegularity P scalarEquiv hreg)
    x₀ (scalarEquiv.symm y₀) (CoordinatePopulation.initialized P scalarEquiv hi)
    H inst (CoordinateOracle.transport P scalarEquiv O) h

end Smoothness2601.CoordinateMinimax
