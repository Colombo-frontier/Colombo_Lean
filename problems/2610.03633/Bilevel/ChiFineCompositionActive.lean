import Bilevel.ChiLiftedSelectionSupport
import Bilevel.ChiSplitFineData

/-! Active mixed jets cannot be created from flat outer jets by a smooth
change of variables. The count includes derivative orders zero through three. -/
noncomputable section
namespace Bilevel.ChiLiftedCarrier
open ChiBoundedChain
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem active_composition_subset (L : ℕ) (f : ℕ → E → ℝ)
    (hf : ∀ p,ContDiff ℝ 3 (f p)) (H : X → E) (hH : ContDiff ℝ 3 H) (x : X) :
    activeLeaves L (fun p => f p ∘ H) x ⊆ activeLeaves L f (H x) := by
  classical
  intro p hp
  obtain ⟨hp,q,hq⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp,?_⟩
  by_contra hn
  push_neg at hn
  apply hq
  apply flat_jet_comp hH (hf p) x q.val (by omega)
  intro k hk
  rw [hn ⟨k,by omega⟩,norm_zero]

theorem split_composed_overlap (n : ℕ) (P : ChiFine.Parameters)
    (H : X → ChiSplitFine.Latent n) (hH : ContDiff ℝ 3 H) (x : X) :
    (activeLeaves (ZeroChainSchedule.levels P.θ) (fun p => ChiSplitFine.pieces P n p ∘ H) x).card≤3 :=
  (Finset.card_le_card (active_composition_subset _ _ (ChiSplitFine.pieces_contDiff P n) H hH x)).trans
    (ChiSplitFine.actual_overlap P n (H x))

end Bilevel.ChiLiftedCarrier
