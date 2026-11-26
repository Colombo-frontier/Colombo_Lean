import NCConcave16991.MixedHaarFrameState
import NCConcave16991.MixedHaarCanonicalCoordinates

/-! # The rank-zero full-frame completion is the original actual Haar draw -/

noncomputable section

open MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 20000

attribute [local irreducible] tailIsometry tailOrthogonal Haar.orthogonalLinearIsometryEquiv

theorem tailIsometry_zero_coe {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) :
    (tailIsometry (⟨0,Nat.zero_lt_succ k⟩ : Fin (k + 1)) v : EuclideanSpace ℝ (Fin k)) = v := by
  ext i
  have he : tailIndex (⟨0,Nat.zero_lt_succ k⟩ : Fin (k + 1)) i = i := Fin.ext (Nat.zero_add _)
  simpa only [he] using tailIsometry_tailIndex (⟨0,Nat.zero_lt_succ k⟩ : Fin (k + 1)) v i

theorem tailOrthogonal_zero {k : ℕ} (Q : Haar.OrthogonalGroup k) :
    tailOrthogonal (⟨0,Nat.zero_lt_succ k⟩ : Fin (k + 1)) Q = Q := by
  apply orthogonal_eq_of_action_eq
  intro x
  have h := tailOrthogonal_on_tail (⟨0,Nat.zero_lt_succ k⟩ : Fin (k + 1)) Q x
  rw [tailIsometry_zero_coe x,
    tailIsometry_zero_coe (Haar.orthogonalLinearIsometryEquiv Q x)] at h
  convert h using 1

def initialFrameState (k : ℕ) : FrameState k := (⟨0,Nat.zero_lt_succ k⟩,(1,1))

theorem frameComplete_initial {k : ℕ} (z : FrameTape k) :
    frameComplete (initialFrameState k) z = z ⟨0,Nat.zero_lt_succ k⟩ := by
  simp only [initialFrameState,frameComplete,tailOrthogonal_zero,inv_one,one_mul,mul_one]

theorem initial_frameComplete_preserving (k : ℕ) :
    MeasurePreserving (frameComplete (initialFrameState k)) (frameTapeLaw k) (Haar.haarLaw k) := by
  rw [show frameComplete (initialFrameState k) = (fun z : FrameTape k ↦ z ⟨0,Nat.zero_lt_succ k⟩) from
    funext frameComplete_initial]
  exact measurePreserving_eval (fun r : Fin (k + 1) ↦ Haar.haarLaw (k - r.val)) ⟨0,Nat.zero_lt_succ k⟩

end NCConcave16991.MixedHaar
