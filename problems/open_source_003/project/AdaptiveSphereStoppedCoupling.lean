import AdaptiveSphereStopped
import RankHandleCount

open MeasureTheory

namespace Task006.AdaptiveSphereStoppedCoupling

open Task006.Full Task006.Full.OracleAlgorithm Task006.AdaptiveSphereTranscript
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped

noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem frame_rank_mono (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (h : Transcript N)
    {t u : ℕ} (htu : t ≤ u) :
    (frameFromTranscript A weight tape seed k hkd t h).1.val ≤
      (frameFromTranscript A weight tape seed k hkd u h).1.val := by
  induction u with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    exact le_rfl
  | succ u ih =>
    by_cases htu' : t ≤ u
    · have hp := ih htu'
      apply hp.trans
      rw [frameFromTranscript]
      split_ifs with hu
      · exact (stateStep_rank_bounds k hkd _ _
          (frameFromTranscript_rank_cap A weight tape seed k hkd u h)).1
      · exact le_rfl
    · have ht : t = u+1 := by omega
      subst t
      exact le_rfl

theorem runPrefix_eq_of_action_eq_left {S' : Type*} [MeasurableSpace S']
    (A : OracleAlgorithm d N S) (B : OracleAlgorithm d N S')
    (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (s : S) (s' : S')
    (ha : ∀ i : Fin N, B.action i s' (A.runPrefix F tape s i.val) =
      A.action i s (A.runPrefix F tape s i.val)) (t : ℕ) :
    A.runPrefix F tape s t = B.runPrefix F tape s' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runPrefix,runPrefix]
    split_ifs with ht
    · rw [← ih,ha ⟨t,ht⟩]
    · exact ih

theorem frame_stop_prefix_eq_final (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (t : ℕ) (ht : t ≤ N) :
    frameFromTranscript A weight tape seed k hkd t
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t) =
    frameFromTranscript A weight tape seed k hkd t
      ((stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape ()) := by
  apply frameFromTranscript_past_only
  intro i hi
  exact (runPrefix_coordinate_stable (stoppedObserver A weight tape seed k hkd)
    (linearSample weight θ) tape () t N ht i hi).symm

theorem finalTranscript_eq_of_rank_lt (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hr : (frameFromTranscript A weight tape seed k hkd N
      ((stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape ())).1.val < k) :
    A.finalTranscript (linearSample weight θ) tape seed =
      (stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape () := by
  apply Eq.symm
  apply runPrefix_eq_of_action_eq_left
  intro i
  change A.action i seed _ = stopAction A weight tape seed k hkd i _
  have hri : (frameFromTranscript A weight tape seed k hkd i.val
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () i.val)).1.val < k := by
    rw [frame_stop_prefix_eq_final A weight tape seed k hkd θ i.val (Nat.le_of_lt i.isLt)]
    exact (frame_rank_mono A weight tape seed k hkd _ (Nat.le_of_lt i.isLt)).trans_lt hr
  simp only [stopAction,if_pos hri]

theorem output_eq_of_rank_lt (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hr : (frameFromTranscript A weight tape seed k hkd N
      ((stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape ())).1.val < k) :
    A.output seed (A.finalTranscript (linearSample weight θ) tape seed) =
      (stoppedObserver A weight tape seed k hkd).output ()
        ((stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape ()) := by
  rw [finalTranscript_eq_of_rank_lt A weight tape seed k hkd θ hr]
  rfl

theorem frame_stop_prefix_rank_mono (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    {t u : ℕ} (htu : t ≤ u) :
    (frameFromTranscript A weight tape seed k hkd t
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t)).1.val ≤
    (frameFromTranscript A weight tape seed k hkd u
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () u)).1.val := by
  have he : frameFromTranscript A weight tape seed k hkd t
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t) =
      frameFromTranscript A weight tape seed k hkd t
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () u) := by
    apply frameFromTranscript_past_only
    intro i hi
    exact (runPrefix_coordinate_stable (stoppedObserver A weight tape seed k hkd)
      (linearSample weight θ) tape () t u htu i hi).symm
  rw [he]
  exact frame_rank_mono A weight tape seed k hkd _ htu

theorem prefix_eq_of_current_rank_lt (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d) (t : ℕ)
    (hr : (frameFromTranscript A weight tape seed k hkd t
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t)).1.val < k) :
    A.runPrefix (linearSample weight θ) tape seed t =
      (stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev := (frame_stop_prefix_rank_mono A weight tape seed k hkd θ (Nat.le_succ t)).trans_lt hr
    have he := ih hprev
    rw [runPrefix,runPrefix]
    split_ifs with ht
    · rw [he]
      change Function.update
          ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t)
          (⟨t,ht⟩ : Fin N)
          (scalarReply (linearSample weight θ) tape (A.action ⟨t,ht⟩ seed
            ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t))) =
        Function.update
          ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t)
          (⟨t,ht⟩ : Fin N)
          (scalarReply (linearSample weight θ) tape (stopAction A weight tape seed k hkd ⟨t,ht⟩
            ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () t)))
      simp only [stopAction,if_pos hprev]
    · exact he

theorem stopped_nonempty_action_eq_original (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d) (i : Fin N)
    (ha : (stoppedObserver A weight tape seed k hkd).executedAction (linearSample weight θ) tape () i ≠ none) :
    A.executedAction (linearSample weight θ) tape seed i =
      (stoppedObserver A weight tape seed k hkd).executedAction (linearSample weight θ) tape () i := by
  have hr : (frameFromTranscript A weight tape seed k hkd i.val
      ((stoppedObserver A weight tape seed k hkd).runPrefix (linearSample weight θ) tape () i.val)).1.val < k := by
    by_contra hn
    apply ha
    change stopAction A weight tape seed k hkd i _ = none
    simp only [stopAction,if_neg hn]
  have he := prefix_eq_of_current_rank_lt A weight tape seed k hkd θ i.val hr
  change A.action i seed (A.runPrefix (linearSample weight θ) tape seed i.val) = stopAction A weight tape seed k hkd i _
  rw [he]
  simp only [stopAction,if_pos hr]

theorem stopped_queriedHandles_subset [MeasurableSpace Ω] (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d) :
    (stoppedObserver A weight tape seed k hkd).queriedHandles (linearSample weight θ) tape () ⊆
      A.queriedHandles (linearSample weight θ) tape seed := by
  classical
  intro h hh
  rcases ((stoppedObserver A weight tape seed k hkd).mem_queriedHandles (linearSample weight θ) tape () h).mp hh with ⟨i,hi,hq⟩
  have hn : (stoppedObserver A weight tape seed k hkd).executedAction (linearSample weight θ) tape () i ≠ none := by
    intro he
    simp [he] at hq
  have he := stopped_nonempty_action_eq_original A weight tape seed k hkd θ i hn
  apply (A.mem_queriedHandles (linearSample weight θ) tape seed h).mpr
  exact ⟨i,hi,by rw [he]; exact hq⟩

theorem stopped_informativeHandles_subset (A : OracleAlgorithm d N S)
    (tape : ℕ → ℝ) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d) :
    (stoppedObserver A id tape seed k hkd).informativeHandles (linearSample id θ) tape () ⊆
      A.informativeHandles (linearSample id θ) tape seed := by
  intro h hh
  rcases Finset.mem_filter.mp hh with ⟨hh,hz⟩
  exact Finset.mem_filter.mpr ⟨stopped_queriedHandles_subset A id tape seed k hkd θ hh,hz⟩

theorem stopped_handleSlots_subset (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d) (h : ℕ) :
    (stoppedObserver A weight tape seed k hkd).handleSlots (linearSample weight θ) tape () h ⊆
      A.handleSlots (linearSample weight θ) tape seed h := by
  classical
  intro i hi
  rcases (Finset.mem_filter.mp hi).2 with ⟨x,hx⟩
  have hn : (stoppedObserver A weight tape seed k hkd).executedAction (linearSample weight θ) tape () i ≠ none := by
    rw [hx]
    simp
  have he := stopped_nonempty_action_eq_original A weight tape seed k hkd θ i hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,by rw [he]; exact hx⟩

theorem stopped_frame_rank_le_twice_original_informative (A : OracleAlgorithm d N S)
    (tape : ℕ → ℝ) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hcap : ∀ h, (A.handleSlots (linearSample id θ) tape seed h).card ≤ 2) :
    (frameFromTranscript A id tape seed k hkd N
      ((stoppedObserver A id tape seed k hkd).finalTranscript (linearSample id θ) tape ())).1.val ≤
        2 * (A.informativeHandles (linearSample id θ) tape seed).card := by
  have hstopcap (h : ℕ) :
      ((stoppedObserver A id tape seed k hkd).handleSlots (linearSample id θ) tape () h).card ≤ 2 :=
    (Finset.card_le_card (stopped_handleSlots_subset A id tape seed k hkd θ h)).trans (hcap h)
  have hr := Task006.RankHandleCount.actual_frame_rank_le_twice_informative_handles
    (stoppedObserver A id tape seed k hkd) tape () θ k hkd hstopcap
  rw [stoppedObserver_frame_eq] at hr
  exact hr.trans (Nat.mul_le_mul_left 2
    (Finset.card_le_card (stopped_informativeHandles_subset A tape seed k hkd θ)))

end
end Task006.AdaptiveSphereStoppedCoupling
