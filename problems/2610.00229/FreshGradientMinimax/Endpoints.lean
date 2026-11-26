import FreshGradientMinimax.Minimax

/-! The zero-primal-gap endpoint discussed in Appendix H, proved for the
actual unrestricted algorithm and fresh-kernel complexity definitions. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def originPolicy (dx dy : ℕ) : Algorithm dx dy Unit where
  query := fun _ _ => 0
  output := fun _ _ => 0
  query_measurable := fun _ => measurable_const
  output_measurable := fun _ => measurable_const

def originAlgorithm (dx dy : ℕ) : RandomizedAlgorithm dx dy where
  Seed := Unit
  seedLaw := Measure.dirac ()
  policy := originPolicy dx dy

theorem origin_zero_query_law (dx dy : ℕ) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (originAlgorithm dx dy).outputLaw K 0 = Measure.dirac (0 : Euclid dx) := by
  unfold RandomizedAlgorithm.outputLaw Algorithm.outputLaw Algorithm.outputKernel
  simp only [originAlgorithm, originPolicy, Algorithm.historyKernel]
  rw [Kernel.deterministic_map _ measurable_const, Measure.deterministic_comp_eq_map,
    Measure.map_dirac]
  · rfl
  · exact measurable_const

theorem zero_gap_budget (p : Parameters) (hp : p.gap = 0) (loc : Option ℝ) :
    BudgetSuffices p loc 0 := by
  intro dx dy
  refine ⟨originAlgorithm dx dy, fun O K hclass => ?_⟩
  rw [origin_zero_query_law]
  have hgap : O.PrimalGapAtMost 0 := by simpa only [hp] using hclass.1
  have hz : (0 : Euclid dx) ∈ O.successSet p.ε := by
    change ‖gradient O.value 0‖ ≤ p.ε
    rw [O.zero_gap_stationary hgap, norm_zero]
    exact p.ε_pos.le
  simp only [Measure.real, Measure.dirac_apply' _ (O.successSet_measurable p.ε),
    Set.indicator_of_mem hz, ENNReal.toReal_one]
  norm_num

theorem zero_gap_complexity (p : Parameters) (hp : p.gap = 0) (loc : Option ℝ) :
    oracleComplexity p loc = 0 := by
  apply le_antisymm _ bot_le
  simpa using complexity_le_of_budget (zero_gap_budget p hp loc)

end FreshGradientMinimax
