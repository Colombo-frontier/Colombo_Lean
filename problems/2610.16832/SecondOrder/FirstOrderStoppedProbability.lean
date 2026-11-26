import SecondOrder.FirstOrderStoppedTransition

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderRestartFastEvent (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (s₀ : S) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) : Prop :=
  ∃ t, t≤n ∧ firstOrderRestartFast P Θ A β start p i cap s₀ t (finiteHistoryTape a₀ n h)

/-- A fast activation can be replaced by the first activation: the response
count cannot have reached the cap earlier, because it is nondecreasing. -/
theorem firstOrderRestartFastEvent_marked (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (s₀ : S) {R : ℝ} (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) :
    firstOrderRestartFastEvent P Θ A β start p i cap s₀ a₀ n h ↔
      finiteHistoryMarked
        (fun t h => firstOrderRestartExit P Θ A β start p i cap s₀ t (finiteHistoryTape a₀ t h))
        (fun t h => firstOrderRestartFast P Θ A β start p i cap s₀ t (finiteHistoryTape a₀ t h)) n h := by
  rw [finiteHistoryMarked_tape_iff a₀ _ _
    (firstOrderRestartExit_tape_congr P Θ A β start p i cap s₀)
    (firstOrderRestartFast_tape_congr P Θ A β start p i cap s₀)]
  constructor
  · rintro ⟨t,ht,hactive,hcount⟩
    have hex : ∃ u, firstOrderRestartActive P Θ A β start p i s₀ u (finiteHistoryTape a₀ n h) := ⟨t,hactive⟩
    have hmin : Nat.find hex≤t := Nat.find_min' hex hactive
    have hc : ∀ u, u≤t → firstOrderRestartCount P Θ A β start p i.val s₀ (finiteHistoryTape a₀ n h) u<cap :=
      fun u hu => lt_of_le_of_lt (firstOrderRestartCount_mono P Θ A β start p i.val s₀ _ hu) hcount
    refine ⟨Nat.find hex,le_trans hmin ht,?_,Nat.find_spec hex,hc _ hmin⟩
    intro u hu he
    rcases he with he | he
    · exact Nat.find_min hex hu he
    · exact (not_le_of_gt (hc u (by omega))) he
  · rintro ⟨t,ht,_,hf⟩
    exact ⟨t,ht,hf⟩

theorem firstOrderRestartFastEvent_activation (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start p : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (hf : firstOrderRestartFastEvent P Θ A β start p i cap s₀ a₀ n h) :
    ∃ t, 0<firstOrderBlockCompletion (Θ i) (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t h) := by
  have hd := (firstOrderRestartFastEvent_marked P Θ A β start p i cap s₀ a₀ n h).mp hf
  obtain ⟨t,ht,hbefore,hactive,hcount⟩ :=
    (finiteHistoryMarked_tape_iff a₀ _ _
      (firstOrderRestartExit_tape_congr P Θ A β start p i cap s₀)
      (firstOrderRestartFast_tape_congr P Θ A β start p i cap s₀) n h).mp hd
  exact ⟨⟨t,by omega⟩,firstOrderContinuation_activation_transfer P Θ A β start p i cap dummy s₀
    (finiteHistoryTape a₀ n h) hp t (fun u hu hh => hbefore u hu (Or.inl hh)) hcount hactive⟩

/-- The genuine restart and the capped continuation have exactly the same
fast-activation probability, despite using different kernels after stopping. -/
theorem firstOrderRestart_fast_mean_transport (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ) :
    pmfMean (firstOrderRestartSamplingLaw P Θ A β R hR start p s₀ n)
      (fun h => if firstOrderRestartFastEvent P Θ A β start p i cap s₀ a₀ n h then (1:ℝ) else 0)=
    pmfMean (finiteAdaptiveLaw (PMF.pure ())
      (firstOrderContinuationKernel P Θ A β R hR start i.val cap dummy s₀) n)
      (fun h => if firstOrderRestartFastEvent P Θ A β start p i cap s₀ a₀ n h then (1:ℝ) else 0) := by
  rw [firstOrderRestartSamplingLaw_adaptive P Θ A β R hR start p s₀ a₀]
  simp_rw [firstOrderRestartFastEvent_marked P Θ A β start p i cap s₀ a₀ n]
  exact finiteAdaptiveLaw_stopped_mean _ _ _ _ _ (fun _ _ hh => Or.inl hh.1)
    (firstOrderRestartTransition_before_exit P Θ A β R hR start p i cap dummy s₀ a₀ hp) n

theorem firstOrderRestart_fast_le_activation (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ) :
    pmfMean (firstOrderRestartSamplingLaw P Θ A β R hR start p s₀ n)
      (fun h => if firstOrderRestartFastEvent P Θ A β start p i cap s₀ a₀ n h then (1:ℝ) else 0)≤
    pmfMean (finiteAdaptiveLaw (PMF.pure ())
      (firstOrderContinuationKernel P Θ A β R hR start i.val cap dummy s₀) n)
      (fun h => if ∃ t, 0<firstOrderBlockCompletion (Θ i)
        (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t h) then (1:ℝ) else 0) := by
  rw [firstOrderRestart_fast_mean_transport P Θ A β R hR start p i cap dummy s₀ a₀ hp]
  apply pmfMean_mono
  intro h
  have hh := firstOrderRestartFastEvent_activation P Θ A β start p i cap dummy s₀ a₀ hp n h
  split_ifs <;> norm_num <;> tauto

end
end SecondOrder
