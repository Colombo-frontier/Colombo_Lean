import Bilevel.ChiHierarchyStore

/-! The actual success-driven finite reveal channel: at each frame it
returns precisely the next requested column, or zero when no disclosure
was requested. Ancestor frames have their own bounded reveal counters. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyIndex
open ChiPrefixEvaluation

abbrev requested (counts : ℕ → ℕ) (J q : ℕ) (i : FrameIndex counts J) : Prop :=
  retained counts J q i < retained counts J (q+1) i

def columnIndex (counts : ℕ → ℕ) (J q : ℕ) (i : FrameIndex counts J) : Fin (chainSize i+1) :=
  ⟨min (retained counts J q i) (chainSize i),Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem columnIndex_of_requested (counts : ℕ → ℕ) (J q : ℕ) (i : FrameIndex counts J)
    (hi : requested counts J q i) : (columnIndex counts J q i).val = retained counts J q i := by
  have hb := retained_le counts J (q+1) i
  exact Nat.min_eq_left (by unfold requested at hi; omega)

theorem per_frame_reveal_budget (counts : ℕ → ℕ) (J q : ℕ) (i : FrameIndex counts J) :
    FramePrefixDisclosure.count (fun s => retained counts J s i) q ≤ chainSize i+1 := by
  rw [FramePrefixDisclosure.count_eq _ (retained_zero counts J i)
    (fun s => retained_success_bounds counts J s i)]
  exact retained_le counts J q i

variable {E : Type*} [NormedAddCommGroup E]

theorem revealReply_eq (counts : ℕ → ℕ) (J q : ℕ) (success : Bool)
    (U : FiniteColumns counts J E) (i : FrameIndex counts J) :
    revealReply counts J q success U i =
      if success=true ∧ requested counts J q i then U i (columnIndex counts J q i) else 0 := by
  by_cases hi : success=true ∧ requested counts J q i
  · have hb := retained_le counts J (q+1) i
    have hr : retained counts J q i < chainSize i+1 := by unfold requested at hi; omega
    have he : (⟨retained counts J q i,hr⟩ : Fin (chainSize i+1)) = columnIndex counts J q i :=
      Fin.ext (columnIndex_of_requested counts J q i hi.2).symm
    simp only [revealReply,if_pos hi,actualNextColumn,dif_pos hr,he]
  · simp only [revealReply,if_neg hi]

variable [MeasurableSpace E]

theorem revealReply_measurable (counts : ℕ → ℕ) (J q : ℕ) (success : Bool) :
    Measurable (revealReply (E:=E) counts J q success) := by
  apply measurable_pi_lambda
  intro i
  simp only [revealReply_eq]
  split_ifs
  · exact (measurable_pi_apply (columnIndex counts J q i)).comp (measurable_pi_apply i)
  · exact measurable_const

theorem revealReply_joint_measurable (counts : ℕ → ℕ) (J : ℕ) :
    Measurable (fun p : FiniteColumns counts J E × (ℕ × Bool) => revealReply counts J p.2.1 p.2.2 p.1) :=
  measurable_from_prod_countable (fun p : ℕ × Bool => revealReply_measurable counts J p.1 p.2)

end Bilevel.ChiHierarchyIndex
