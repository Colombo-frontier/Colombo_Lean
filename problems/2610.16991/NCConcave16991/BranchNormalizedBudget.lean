import NCConcave16991.LowerFromNormalizedBranch
import NCConcave16991.BranchOracleBudget
import NCConcave16991.BranchOracleFlat

/-! # Converting the actual inclusive floor cutoff into the normalized lower rate -/

noncomputable section

namespace NCConcave16991.BranchNormalizedBudget

def lowerConstant (ρ : ℝ) : ℝ := ρ ^ 2 / (4 * Real.exp 1)

theorem lowerConstant_pos (ρ : ℝ) (hρ : 0 < ρ) : 0 < lowerConstant ρ := by
  unfold lowerConstant
  positivity

theorem lower_bound_of_floor_cutoff (ρ : ℝ) (hρ : 0 < ρ)
    (hRawBudget : ∀ (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m K : ℕ),
      K ≤ BranchOracleBudget.budget (n : ℝ) ρ (M * (m + 1)) →
        ¬ ValidBudget (GlobalHardEuclidean.paperParameters n hn M hM m) .individual K)
    (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m : ℕ) :
    LowerBudgetBound (GlobalHardEuclidean.paperParameters n hn M hM m) .individual
      (lowerConstant ρ * (n : ℝ) * (M : ℝ) * (m + 1 : ℕ)) := by
  intro K hvalid
  have hnot : ¬ K ≤ BranchOracleBudget.budget (n : ℝ) ρ (M * (m + 1)) :=
    fun h ↦ hRawBudget n hn M hM m K h hvalid
  have hnext : BranchOracleBudget.budget (n : ℝ) ρ (M * (m + 1)) + 1 ≤ K := by omega
  have hnextR : (BranchOracleBudget.budget (n : ℝ) ρ (M * (m + 1)) : ℝ) + 1 ≤ K := by
    exact_mod_cast hnext
  have hfloor : ρ ^ 2 * (n : ℝ) * (M * (m + 1) : ℕ) / (4 * Real.exp 1) <
      (BranchOracleBudget.budget (n : ℝ) ρ (M * (m + 1)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  calc
    lowerConstant ρ * (n : ℝ) * (M : ℝ) * (m + 1 : ℕ) =
        ρ ^ 2 * (n : ℝ) * (M * (m + 1) : ℕ) / (4 * Real.exp 1) := by
      unfold lowerConstant
      push_cast
      ring
    _ ≤ (BranchOracleBudget.budget (n : ℝ) ρ (M * (m + 1)) : ℝ) + 1 := hfloor.le
    _ ≤ (K : ℝ) := hnextR

theorem normalized_specification_of_floor_cutoff (ρ : ℝ) (hρ : 0 < ρ)
    (hRawBudget : ∀ (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m K : ℕ),
      K ≤ BranchOracleBudget.budget (n : ℝ) ρ (M * (m + 1)) →
        ¬ ValidBudget (GlobalHardEuclidean.paperParameters n hn M hM m) .individual K) :
    NormalizedBranchLowerSpecification :=
  ⟨lowerConstant ρ,lowerConstant_pos ρ hρ,lower_bound_of_floor_cutoff ρ hρ hRawBudget⟩

theorem normalized_specification_of_raw_budget
    (hRawBudget : ∀ (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m K : ℕ),
      K ≤ BranchOracleBudget.budget (n : ℝ) BranchOracle.releaseThreshold (M * (m + 1)) →
        ¬ ValidBudget (GlobalHardEuclidean.paperParameters n hn M hM m) .individual K) :
    NormalizedBranchLowerSpecification :=
  normalized_specification_of_floor_cutoff BranchOracle.releaseThreshold BranchOracle.releaseThreshold_pos hRawBudget

end NCConcave16991.BranchNormalizedBudget
