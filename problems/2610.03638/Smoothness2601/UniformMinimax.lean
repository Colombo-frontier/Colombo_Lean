import Smoothness2601.LowerMinimax
import Smoothness2601.UpperMinimax

/-! The article's uniform-order minimax theorem, for every finite cap and
infinite cap simultaneously, proved from the actual adaptive oracle model. -/
noncomputable section
namespace Smoothness2601

theorem uniform_minimax (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) :
    UniformMinimaxClaim b M Λ β := by
  obtain ⟨c,δ,hc,hδ,hl⟩ := uniform_minimax_lower b hgap hM hΛ hβ
  obtain ⟨C,η,hC,hη,hu⟩ := uniform_minimax_upper b hgap hM hΛ hβ
  refine ⟨c,C,min δ η,hc,hC,lt_min hδ hη,?_⟩
  intro p hp ε hε hs
  exact ⟨hl p hp ε hε (hs.trans_le (min_le_left _ _)),
    hu p hp ε hε (hs.trans_le (min_le_right _ _))⟩

end Smoothness2601
