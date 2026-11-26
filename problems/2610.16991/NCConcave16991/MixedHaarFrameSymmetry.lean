import NCConcave16991.MixedHaarFrameProbability

/-! # Swapping the formal and physical frames inverts the actual completion law -/

noncomputable section

open MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 100000

attribute [local irreducible] frameComplete tailOrthogonal Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

def frameSwap (s : FrameState k) : FrameState k := (s.1,s.2.2,s.2.1)

theorem frameSwap_involutive (s : FrameState k) : frameSwap (frameSwap s) = s := rfl

theorem frameSwap_measurable : Measurable (frameSwap (k := k)) :=
  measurable_fst.prodMk ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))

def frameTapeInv (z : FrameTape k) : FrameTape k := fun r ↦ (z r)⁻¹

theorem frameTapeInv_preserving (k : ℕ) :
    MeasurePreserving (frameTapeInv (k := k)) (frameTapeLaw k) (frameTapeLaw k) :=
  measurePreserving_pi (fun r : Fin (k + 1) ↦ Haar.haarLaw (k - r.val))
    (fun r : Fin (k + 1) ↦ Haar.haarLaw (k - r.val))
    (fun r ↦ compact_haar_inverse_preserving (Haar.haarLaw (k - r.val)))

theorem frameComplete_swap_inv (s : FrameState k) (z : FrameTape k) :
    frameComplete (frameSwap s) (frameTapeInv z) = (frameComplete s z)⁻¹ := by
  have hi (Q : Haar.OrthogonalGroup (k - s.1.val)) : tailOrthogonal s.1 Q⁻¹ = (tailOrthogonal s.1 Q)⁻¹ :=
    (tailOrthogonalHom s.1).map_inv Q
  simp only [frameComplete,frameSwap,frameTapeInv,hi,mul_inv_rev,inv_inv,mul_assoc]

theorem frameCompletionLaw_swap_inverse (s : FrameState k) :
    MeasurePreserving (Inv.inv : Haar.OrthogonalGroup k → Haar.OrthogonalGroup k)
      (frameCompletionLaw (frameSwap s)) (frameCompletionLaw s) := by
  have hs := frameComplete_preserving (frameSwap s)
  have ht := frameTapeInv_preserving k
  have hc := frameComplete_preserving s
  refine ⟨measurable_inv,?_⟩
  rw [← hs.map_eq,Measure.map_map measurable_inv hs.measurable]
  have he : Inv.inv ∘ frameComplete (frameSwap s) = frameComplete s ∘ frameTapeInv := by
    funext z
    exact (frameComplete_swap_inv (frameSwap s) z).symm
  rw [he,← Measure.map_map hc.measurable ht.measurable,ht.map_eq,hc.map_eq]

end NCConcave16991.MixedHaar
