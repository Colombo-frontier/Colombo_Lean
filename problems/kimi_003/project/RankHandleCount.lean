import AdaptiveSphereState
import InformativeHandleCount
import HandleLedger

open MeasureTheory

namespace Task006.RankHandleCount

open Task006.Full Task006.Full.OracleAlgorithm Task006.AdaptiveSphereState
open Task006.AdaptiveSphereTranscript

noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem cutoff_card_succ (p : Fin N → Prop) [DecidablePred p]
    (t : ℕ) (ht : t < N) :
    (Finset.univ.filter (fun i : Fin N => i.val < t+1 ∧ p i)).card =
      (Finset.univ.filter (fun i : Fin N => i.val < t ∧ p i)).card +
        if p ⟨t,ht⟩ then 1 else 0 := by
  classical
  by_cases hp : p ⟨t,ht⟩
  · have he : Finset.univ.filter (fun i : Fin N => i.val < t+1 ∧ p i) =
        insert ⟨t,ht⟩ (Finset.univ.filter (fun i : Fin N => i.val < t ∧ p i)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hpi⟩
        by_cases hit : i.val < t
        · exact Or.inr ⟨hit,hpi⟩
        · left; apply Fin.ext; change i.val = t; omega
      · rintro (rfl | ⟨hi,hpi⟩)
        · exact ⟨by simp,hp⟩
        · exact ⟨by omega,hpi⟩
    rw [he,Finset.card_insert_of_notMem (by simp),if_pos hp]
  · have he : Finset.univ.filter (fun i : Fin N => i.val < t+1 ∧ p i) =
        Finset.univ.filter (fun i : Fin N => i.val < t ∧ p i) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hi,hpi⟩
        have hit : i.val ≠ t := by
          intro hiEq
          have he : i = ⟨t,ht⟩ := Fin.ext hiEq
          exact hp (he ▸ hpi)
        exact ⟨by omega,hpi⟩
      · rintro ⟨hi,hpi⟩; exact ⟨by omega,hpi⟩
    rw [he,if_neg hp,Nat.add_zero]

theorem frame_rank_le_nonzero_replies (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (h : Transcript N) (t : ℕ) (ht : t ≤ N) :
    (frameFromTranscript A weight tape seed k hkd t h).1.val ≤
      (Finset.univ.filter (fun i : Fin N => i.val < t ∧
        effectiveVector weight tape (A.action i seed h) ≠ 0)).card := by
  classical
  induction t with
  | zero => simp [frameFromTranscript,initialState]
  | succ t ih =>
    have ht' : t < N := by omega
    have hi := ih (by omega)
    simp only [ne_eq] at hi
    have hs := stateStep_rank_indicator k hkd
      (frameFromTranscript A weight tape seed k hkd t h)
      (effectiveVector weight tape (A.action ⟨t,ht'⟩ seed h))
      (frameFromTranscript_rank_cap A weight tape seed k hkd t h)
    rw [frameFromTranscript,dif_pos ht']
    rw [cutoff_card_succ _ t ht']
    by_cases hq : effectiveVector weight tape (A.action ⟨t,ht'⟩ seed h) = 0
    · simp only [hq,if_pos,ne_eq,not_true_eq_false,if_false] at hs ⊢
      omega
    · simp only [hq,if_neg,ne_eq,not_false_eq_true,if_true] at hs ⊢
      omega

theorem action_finalTranscript_eq (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (i : Fin N) :
    A.action i seed (A.finalTranscript F tape seed) = A.executedAction F tape seed i := by
  apply A.past_only
  intro j hj
  exact runPrefix_coordinate_stable A F tape seed i.val N (Nat.le_of_lt i.isLt) j hj

def informativeReplies (A : OracleAlgorithm d N S) (F : Space d → ℝ → ℝ)
    (tape : ℕ → ℝ) (seed : S) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => ∃ h x,
    A.executedAction F tape seed i = some (h,x) ∧ tape h ≠ 0)

def actionHandle (a : QueryAction d) : ℕ := (a.map Prod.fst).getD 0

theorem informativeReplies_card_le (A : OracleAlgorithm d N S) (F : Space d → ℝ → ℝ)
    (tape : ℕ → ℝ) (seed : S)
    (hcap : ∀ h, (A.handleSlots F tape seed h).card ≤ 2) :
    (informativeReplies A F tape seed).card ≤ 2 * (A.informativeHandles F tape seed).card := by
  classical
  let hlabel : Fin N → ℕ := fun i => actionHandle (A.executedAction F tape seed i)
  have hsub (h : ℕ) :
      (informativeReplies A F tape seed).filter (fun i => hlabel i = h) ⊆
        A.handleSlots F tape seed h := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi,hh⟩
    rcases (Finset.mem_filter.mp hi).2 with ⟨j,x,hj,hz⟩
    have he : j = h := by simpa [hlabel,actionHandle,hj] using hh
    subst j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hj⟩
  have himage : (informativeReplies A F tape seed).image hlabel ⊆ A.informativeHandles F tape seed := by
    intro h hh
    rcases Finset.mem_image.mp hh with ⟨i,hi,rfl⟩
    rcases (Finset.mem_filter.mp hi).2 with ⟨j,x,hj,hz⟩
    have he : hlabel i = j := by simp [hlabel,actionHandle,hj]
    rw [he]
    apply Finset.mem_filter.mpr
    refine ⟨(A.mem_queriedHandles F tape seed j).mpr ⟨i,i.isLt,?_⟩,hz⟩
    simp [hj]
  exact (Task006HandleLedger.replies_le_twice_handles _ hlabel (fun h =>
    (Finset.card_le_card (hsub h)).trans (hcap h))).trans
      (Nat.mul_le_mul_left 2 (Finset.card_le_card himage))

theorem actual_frame_rank_le_twice_informative_handles (A : OracleAlgorithm d N S)
    (tape : ℕ → ℝ) (seed : S) (θ : Space d) (k : ℕ) (hkd : k ≤ d)
    (hcap : ∀ h, (A.handleSlots (linearSample id θ) tape seed h).card ≤ 2) :
    (frameFromTranscript A id tape seed k hkd N
      (A.finalTranscript (linearSample id θ) tape seed)).1.val ≤
        2 * (A.informativeHandles (linearSample id θ) tape seed).card := by
  classical
  have hr := frame_rank_le_nonzero_replies A id tape seed k hkd
    (A.finalTranscript (linearSample id θ) tape seed) N le_rfl
  have hs : Finset.univ.filter (fun i : Fin N => i.val < N ∧
        effectiveVector id tape (A.action i seed (A.finalTranscript (linearSample id θ) tape seed)) ≠ 0) ⊆
      informativeReplies A (linearSample id θ) tape seed := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2.2
    rw [action_finalTranscript_eq] at hn
    cases he : A.executedAction (linearSample id θ) tape seed i with
    | none => simp [he,effectiveVector] at hn
    | some a =>
      rcases a with ⟨h,x⟩
      have hz : tape h ≠ 0 := by
        intro hz
        simp [he,effectiveVector,hz] at hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,x,he,hz⟩
  exact hr.trans ((Finset.card_le_card hs).trans
    (informativeReplies_card_le A (linearSample id θ) tape seed hcap))

end
end Task006.RankHandleCount
