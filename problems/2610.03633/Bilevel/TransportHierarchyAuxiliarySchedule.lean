import Bilevel.ChiCanonicalHierarchy
import Bilevel.TransportAuxiliaryFrameSchedule

/-! The actual hierarchy counters give a public auxiliary-frame release
schedule. Unused terminal auxiliary frames may be included in this finite
index set; physical terminal frames come from the network, not these draws.
Every auxiliary release is delayed until the completed transport stage. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress TransportAuxiliaryFrame
set_option maxHeartbeats 500000

def auxiliaryCapacity (counts : ℕ → ℕ) (J : ℕ) : ℕ :=
  Finset.univ.sum (fun i : FrameIndex counts J => chainSize i+1)

theorem chainSize_le_auxiliaryCapacity (counts : ℕ → ℕ) (J : ℕ)
    (i : FrameIndex counts J) : chainSize i≤auxiliaryCapacity counts J := by
  apply le_trans (Nat.le_succ _)
  change chainSize i+1≤Finset.univ.sum (fun j : FrameIndex counts J => chainSize j+1)
  exact Finset.single_le_sum (f:=fun j : FrameIndex counts J => chainSize j+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

def auxiliaryStageSchedule (counts : ℕ → ℕ) (J : ℕ) :
    Schedule (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) where
  count q i := retained counts J q ((enumerate counts J).symm i)
  zero i := retained_zero counts J ((enumerate counts J).symm i)
  mono q i := (retained_success_bounds counts J q ((enumerate counts J).symm i)).1
  step q i := (retained_success_bounds counts J q ((enumerate counts J).symm i)).2
  bound q i := (retained_le counts J q ((enumerate counts J).symm i)).trans
    (Nat.add_le_add_right (chainSize_le_auxiliaryCapacity counts J ((enumerate counts J).symm i)) 1)

def auxiliaryRoundSchedule (counts : ℕ → ℕ) (J length : ℕ) (hL : 0<length) :
    Schedule (Fintype.card (FrameIndex counts J)) (auxiliaryCapacity counts J) :=
  (auxiliaryStageSchedule counts J).rounds length hL

theorem auxiliaryRoundSchedule_count (counts : ℕ → ℕ) (J length : ℕ) (hL : 0<length)
    (t : ℕ) (i : FrameIndex counts J) :
    (auxiliaryRoundSchedule counts J length hL).count t (enumerate counts J i)=
      retained counts J (t/length) i := by
  simp only [auxiliaryRoundSchedule,Schedule.rounds,auxiliaryStageSchedule,Equiv.symm_apply_apply]

theorem auxiliaryRoundSchedule_macro (counts : ℕ → ℕ) (J length : ℕ) (hL : 0<length)
    (t : ℕ) :
    (auxiliaryRoundSchedule counts J length hL).count t (enumerate counts J (Sum.inl ()))=
      counter counts (J+1) (t/length) 0 [] := by
  rw [auxiliaryRoundSchedule_count]
  rfl

theorem auxiliaryRoundSchedule_node (counts : ℕ → ℕ) (J length : ℕ) (hL : 0<length)
    (t : ℕ) (j : Fin (J+1)) (I : List ℕ) :
    (auxiliaryRoundSchedule counts J length hL).count t
      (enumerate counts J (Sum.inr (canonicalNode counts J j I)))=
      canonicalCounter counts J (t/length) j.val I := by
  rw [auxiliaryRoundSchedule_count,canonicalCounter,dif_pos (Nat.le_of_lt_succ j.isLt)]

theorem auxiliaryRoundSchedule_no_early (counts : ℕ → ℕ) (J length : ℕ) (hL : 0<length)
    (t : ℕ) (i : Fin (Fintype.card (FrameIndex counts J)))
    (h : (t+1)/length=t/length) :
    request (auxiliaryRoundSchedule counts J length hL) t i=false :=
  rounds_no_early_release (auxiliaryStageSchedule counts J) length hL t i h

end Bilevel.TransportHierarchy
