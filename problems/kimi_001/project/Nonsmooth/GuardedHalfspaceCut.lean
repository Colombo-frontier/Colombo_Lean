import Nonsmooth.HalfspaceCutBody

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Invalid direction readouts leave the body unchanged, including on unreachable histories. -/
def guardedHalfspaceCut (G : Set E) (e : E) (τ : ℝ) : Set E :=
  if ‖e‖ = 1 then halfspaceCutBody G e τ else G

theorem guardedHalfspaceCut_of_unit (G : Set E) {e : E} (he : ‖e‖ = 1) (τ : ℝ) :
    guardedHalfspaceCut G e τ = halfspaceCutBody G e τ := by simp only [guardedHalfspaceCut, if_pos he]

theorem guardedHalfspaceCut_subset (G : Set E) (e : E) (τ : ℝ) :
    guardedHalfspaceCut G e τ ⊆ G := by
  unfold guardedHalfspaceCut
  split_ifs
  · exact halfspaceCutBody_subset G e τ
  · exact Subset.rfl

theorem guardedHalfspaceCut_convex {G : Set E} (hG : Convex ℝ G) (e : E) (τ : ℝ) :
    Convex ℝ (guardedHalfspaceCut G e τ) := by
  unfold guardedHalfspaceCut
  split_ifs
  · exact halfspaceCutBody_convex hG e τ
  · exact hG

theorem guardedHalfspaceCut_compact {G : Set E} (hG : IsCompact G) (e : E) (τ : ℝ) :
    IsCompact (guardedHalfspaceCut G e τ) := by
  unfold guardedHalfspaceCut
  split_ifs
  · exact halfspaceCutBody_compact hG e τ
  · exact hG

theorem guardedHalfspaceCut_contains_ball {G : Set E} {r τ : ℝ}
    (hinner : closedBall (0 : E) r ⊆ G) (hτr : τ ≤ r) (e : E) :
    closedBall (0 : E) τ ⊆ guardedHalfspaceCut G e τ := by
  unfold guardedHalfspaceCut
  split_ifs with he
  · exact halfspaceCutBody_contains_ball hinner hτr he
  · exact (closedBall_subset_closedBall hτr).trans hinner

end
end Nonsmooth
