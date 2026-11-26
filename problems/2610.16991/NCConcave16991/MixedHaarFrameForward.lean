import NCConcave16991.MixedHaarFrameSymmetry
import NCConcave16991.MixedHaarFrameUpdateGeometry
import NCConcave16991.MixedHaarFrameGrowth

/-! # The deterministic forward-reveal adapter for public full-frame states -/

noncomputable section

namespace NCConcave16991.MixedHaar

open MeasureTheory

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal householderOrthogonal frameHead frameTail
  Haar.orthogonalLinearIsometryEquiv

def frameForwardUpdate {k : ℕ} (s : FrameState k) (x g : Space k) : FrameState k :=
  frameSwap (frameUpdate (frameSwap s) x g)

def frameForwardCandidate {k : ℕ} (s : FrameState k) (x g : Space k) : Space k :=
  frameCandidate (frameSwap s) x g

theorem frameForwardUpdate_measurable {k : ℕ} :
    Measurable (fun p : FrameState k × (Space k × Space k) ↦ frameForwardUpdate p.1 p.2.1 p.2.2) :=
  frameSwap_measurable.comp (frameUpdate_measurable.comp
    ((frameSwap_measurable.comp measurable_fst).prodMk measurable_snd))

theorem frameForwardCandidate_measurable {k : ℕ} :
    Measurable (fun p : FrameState k × (Space k × Space k) ↦ frameForwardCandidate p.1 p.2.1 p.2.2) :=
  frameCandidate_measurable.comp ((frameSwap_measurable.comp measurable_fst).prodMk measurable_snd)

theorem frameForwardCandidate_mem_old_sup_gaussian {k : ℕ} (s : FrameState k) (x g : Space k) :
    frameForwardCandidate s x g ∈ frameRange s ⊔ Submodule.span ℝ ({g} : Set (Space k)) :=
  frameCandidate_mem_old_sup_gaussian (frameSwap s) x g

theorem frameForwardUpdate_answer {k : ℕ} (s : FrameState k) (x g : Space k) (z : FrameTape k)
    (hr : s.1.val < k) (hq : frameTail s.1 s.2.1 x ≠ 0) (hh : frameTail s.1 s.2.2 g ≠ 0) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete (frameForwardUpdate s x g) z) x = frameForwardCandidate s x g := by
  have he := frameUpdate_inverse (frameSwap s) x g (frameTapeInv z) hr hq hh
  have hs : frameComplete (frameUpdate (frameSwap s) x g) (frameTapeInv z) =
      (frameComplete (frameForwardUpdate s x g) z)⁻¹ :=
    frameComplete_swap_inv (frameForwardUpdate s x g) z
  rw [hs,inv_inv] at he
  exact he

theorem frameForwardComplete_answer_of_tail_zero {k : ℕ} (s : FrameState k) (x g : Space k) (z : FrameTape k)
    (hq : frameTail s.1 s.2.1 x = 0) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete s z) x = frameForwardCandidate s x g := by
  have he := frameComplete_inverse_of_tail_zero (frameSwap s) x g (frameTapeInv z) hq
  rw [frameComplete_swap_inv,inv_inv] at he
  exact he

theorem frameForwardUpdate_candidate_invariant {k : ℕ} (s : FrameState k) (x g : Space k) :
    frameForwardUpdate s x (frameForwardCandidate s x g) = frameForwardUpdate s x g := by
  exact congrArg frameSwap (frameUpdate_candidate_invariant (frameSwap s) x g)

theorem frameForwardUpdate_range_mono {k : ℕ} (s : FrameState k) (x g : Space k) :
    frameRange s ≤ frameRange (frameForwardUpdate s x g) :=
  frameUpdate_domain_mono (frameSwap s) x g

end NCConcave16991.MixedHaar
