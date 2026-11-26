import Smoothness2601.PublicBoundary
import Smoothness2601.Minimax

/-! Boundary-rate upper theorem with the full original minimax quantifiers.
No higher-order regularity is used by this two-batch public algorithm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601

theorem boundary_budgetWorks (b : Budgets) (heq : b.L₁ = b.μ)
    (p : WithTop ℕ) (L : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    BudgetWorks b p L ε (BoundaryCost.count b ε) := by
  intro dx dy
  refine ⟨PublicBoundary.algorithm b hε,?_⟩
  intro P _hreg x₀ y₀ hinit H inst O history
  have hs := BoundaryOuter.expected_stationarity P O heq hε (x₀,y₀) history hinit
  have hLip : LipschitzWith
      ⟨HypergradientGeometry.outerSmoothness b,(HypergradientGeometry.outerSmoothness_pos b).le⟩
      (gradient P.objective) :=
    LipschitzWith.of_dist_le_mul (fun x z => by
      simpa only [dist_eq_norm,NNReal.coe_mk] using HypergradientGeometry.outer_smoothness P x z)
  have hm := hLip.continuous.measurable.nnnorm.coe_nnreal_ennreal
  unfold Adaptive.Succeeds Adaptive.expectedNorm
  rw [PublicBoundary.algorithm_output,MeasureTheory.lintegral_map hm
    (NormalizedExecution.selected_measurable (OuterSchedule.iterations b ε))]
  rw [lintegral_coe_eq_integral _ hs.1]
  apply ENNReal.ofReal_le_ofReal
  exact hs.2.trans (by linarith)

/-- The upper half of Proposition prop:boundary-rate. Its constant is uniform
in the complete finite/infinite smoothness cap and derivative envelope. -/
theorem boundary_minimax_upper (b : Budgets) (heq : b.L₁ = b.μ) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ), 0 < ε → ε < ε₀ →
        minimaxComplexity b p L ε ≤ ENNReal.ofReal (C*ε ^ (-4:ℝ)) := by
  refine ⟨BoundaryCost.constant b,1,BoundaryCost.constant_pos b,by norm_num,?_⟩
  intro p L ε hε hε1
  refine (minimax_le_budget (boundary_budgetWorks b heq p L hε)).trans ?_
  exact_mod_cast ENNReal.ofReal_le_ofReal (BoundaryCost.total b hε hε1.le)

end Smoothness2601
