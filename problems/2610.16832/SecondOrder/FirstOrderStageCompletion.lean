import SecondOrder.FirstOrderStageResponseCount

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderStageEntry_exists (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (stage : ℕ) (hstage : 0<stage) :
    ∀ N, stage≤(firstOrderComparisonRun P Θ A β z (N+1)).1 →
      ∃ n, n≤N ∧ firstOrderStageEntry P Θ A β z stage n := by
  intro N
  induction N with
  | zero =>
    intro hh
    have hstep := firstOrderComparisonRun_progress_step P Θ A β z 0
    have hr := firstOrderComparisonRun_progress_succ P Θ A β z 0
    have hzero : (firstOrderComparisonRun P Θ A β z 0).1=0 := rfl
    refine ⟨0,le_rfl,?_,?_⟩
    · exact hstage
    · omega
  | succ N ih =>
    intro hh
    by_cases hp : stage≤(firstOrderComparisonRun P Θ A β z (N+1)).1
    · obtain ⟨n,hn,he⟩ := ih hp
      exact ⟨n,by omega,he⟩
    · have hstep := firstOrderComparisonRun_progress_step P Θ A β z (N+1)
      have hr := firstOrderComparisonRun_progress_succ P Θ A β z (N+1)
      refine ⟨N+1,le_rfl,?_,?_⟩ <;> omega

theorem firstOrderStageEntry_exists_before (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (stage : ℕ) (hstage : 0<stage) (N : ℕ)
    (hh : stage≤(firstOrderComparisonRun P Θ A β z N).1) :
    ∃ n, n<N ∧ firstOrderStageEntry P Θ A β z stage n := by
  cases N with
  | zero => change stage≤0 at hh; omega
  | succ N =>
    obtain ⟨n,hn,he⟩ := firstOrderStageEntry_exists P Θ A β z stage hstage N hh
    exact ⟨n,by omega,he⟩

theorem firstOrderStageEntry_target_active (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (i : Fin (T+1)) (n : ℕ)
    (he : firstOrderStageEntry P Θ A β z (i.val+1) n) :
    0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β (firstOrderComparisonQuery P Θ A β z n) i) := by
  have hp := (firstOrderStageEntry_progress P Θ A β z he).1
  have hidx := he.2
  by_contra hn
  have hc := firstOrderLimitedProgress_next_inactive Θ β (firstOrderComparisonQuery P Θ A β z n) i hn
  have hle := (firstOrderLimitedProgress_le Θ β (firstOrderComparisonQuery P Θ A β z n) i.val).2
  unfold firstOrderComparisonIndex at hidx
  rw [hp, hc] at hidx
  omega

def firstOrderStageReached (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (i : Fin (T+1)) (N : ℕ) : Prop :=
  ∃ n, n≤N ∧ firstOrderStageEntry P Θ A β z (i.val+1) n

theorem firstOrderComparison_complete_reached (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (N : ℕ)
    (hc : firstOrderComparisonOutputProgress P Θ A β z N=T+1) (i : Fin (T+1)) :
    firstOrderStageReached P Θ A β z i N := by
  apply firstOrderStageEntry_exists P Θ A β z (i.val+1) (by omega) N
  change i.val+1≤firstOrderComparisonOutputProgress P Θ A β z N
  rw [hc]
  omega

/-- Completing a positive stage with too few total responses assigned to
it forces the fast event at its unique actual entrance time. -/
theorem firstOrderStageReached_fast (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (i : Fin (T+1)) (hi : 0 < i.val) (cap N : ℕ)
    (hr : firstOrderStageReached P Θ A β z i N)
    (hcount : firstOrderStageResponseCount P Θ A β z i.val N<cap) :
    firstOrderStageFast P Θ A β z i cap N := by
  obtain ⟨q,hq,heq⟩ := hr
  have hp := (firstOrderStageEntry_progress P Θ A β z heq).1
  have hpq : (firstOrderComparisonRun P Θ A β z q).1=i.val := by omega
  obtain ⟨n,hnq,hen⟩ := firstOrderStageEntry_exists_before P Θ A β z i.val hi q (by omega)
  have hnq' : n≤q := by omega
  have hadd : n+(q-n)=q := Nat.add_sub_of_le hnq'
  have hs := firstOrderComparisonRun_restart P Θ A β z n (q-n)
  have hcs := firstOrderStageResponseCount_restart P Θ A β z i.val n (q-n)
  have hcq : firstOrderStageResponseCount P Θ A β z i.val q≤firstOrderStageResponseCount P Θ A β z i.val N :=
    firstOrderStageResponseCount_mono P Θ A β z i.val hq
  rw [hadd] at hcs
  refine ⟨⟨n,by omega⟩,hen,?_⟩
  change ∃ t, t≤N-n ∧ firstOrderRestartFast P Θ A β n
    (firstOrderComparisonRun P Θ A β z n).1 i cap (firstOrderComparisonRun P Θ A β z n).2 t (fun u => z (n+u))
  refine ⟨q-n,by omega,?_,?_⟩
  · unfold firstOrderRestartActive
    rw [←hs, hadd]
    exact firstOrderStageEntry_target_active P Θ A β z i q heq
  · omega

end
end SecondOrder
