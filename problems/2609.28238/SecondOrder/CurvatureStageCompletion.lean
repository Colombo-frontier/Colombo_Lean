import SecondOrder.CurvatureStageResponseCount

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvatureStageEntry_exists (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (stage : ℕ) (hstage : 0<stage) :
    ∀ N, stage≤(curvatureComparisonRun P Θ A β z (N+1)).1 →
      ∃ n, n≤N ∧ curvatureStageEntry P Θ A β z stage n := by
  intro N
  induction N with
  | zero =>
    intro hh
    have hstep := curvatureComparisonRun_progress_step P Θ A β z 0
    have hr := curvatureComparisonRun_progress_succ P Θ A β z 0
    have hzero : (curvatureComparisonRun P Θ A β z 0).1=0 := rfl
    refine ⟨0,le_rfl,?_,?_⟩
    · exact hstage
    · omega
  | succ N ih =>
    intro hh
    by_cases hp : stage≤(curvatureComparisonRun P Θ A β z (N+1)).1
    · obtain ⟨n,hn,he⟩ := ih hp
      exact ⟨n,by omega,he⟩
    · have hstep := curvatureComparisonRun_progress_step P Θ A β z (N+1)
      have hr := curvatureComparisonRun_progress_succ P Θ A β z (N+1)
      refine ⟨N+1,le_rfl,?_,?_⟩ <;> omega

theorem curvatureStageEntry_exists_before (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (stage : ℕ) (hstage : 0<stage) (N : ℕ)
    (hh : stage≤(curvatureComparisonRun P Θ A β z N).1) :
    ∃ n, n<N ∧ curvatureStageEntry P Θ A β z stage n := by
  cases N with
  | zero => change stage≤0 at hh; omega
  | succ N =>
    obtain ⟨n,hn,he⟩ := curvatureStageEntry_exists P Θ A β z stage hstage N hh
    exact ⟨n,by omega,he⟩

theorem curvatureStageEntry_target_active (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (i : Fin (T+1)) (n : ℕ)
    (he : curvatureStageEntry P Θ A β z (i.val+1) n) :
    0<periodicCompletion (Θ i) (curvatureDilation m T β (curvatureComparisonQuery P Θ A β z n) i) := by
  have hp := (curvatureStageEntry_progress P Θ A β z he).1
  have hidx := he.2
  by_contra hn
  have hc := curvatureLimitedProgress_next_inactive Θ β (curvatureComparisonQuery P Θ A β z n) i hn
  have hle := (curvatureLimitedProgress_le Θ β (curvatureComparisonQuery P Θ A β z n) i.val).2
  unfold curvatureComparisonIndex at hidx
  rw [hp, hc] at hidx
  omega

def curvatureStageReached (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (i : Fin (T+1)) (N : ℕ) : Prop :=
  ∃ n, n≤N ∧ curvatureStageEntry P Θ A β z (i.val+1) n

theorem curvatureComparison_complete_reached (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (N : ℕ)
    (hc : curvatureComparisonOutputProgress P Θ A β z N=T+1) (i : Fin (T+1)) :
    curvatureStageReached P Θ A β z i N := by
  apply curvatureStageEntry_exists P Θ A β z (i.val+1) (by omega) N
  change i.val+1≤curvatureComparisonOutputProgress P Θ A β z N
  rw [hc]
  omega

/-- Completing a positive stage with too few total responses assigned to
it forces the fast event at its unique actual entrance time. -/
theorem curvatureStageReached_fast (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (i : Fin (T+1)) (hi : 0 < i.val) (cap N : ℕ)
    (hr : curvatureStageReached P Θ A β z i N)
    (hcount : curvatureStageResponseCount P Θ A β z i.val N<cap) :
    curvatureStageFast P Θ A β z i cap N := by
  obtain ⟨q,hq,heq⟩ := hr
  have hp := (curvatureStageEntry_progress P Θ A β z heq).1
  have hpq : (curvatureComparisonRun P Θ A β z q).1=i.val := by omega
  obtain ⟨n,hnq,hen⟩ := curvatureStageEntry_exists_before P Θ A β z i.val hi q (by omega)
  have hnq' : n≤q := by omega
  have hadd : n+(q-n)=q := Nat.add_sub_of_le hnq'
  have hs := curvatureComparisonRun_restart P Θ A β z n (q-n)
  have hcs := curvatureStageResponseCount_restart P Θ A β z i.val n (q-n)
  have hcq : curvatureStageResponseCount P Θ A β z i.val q≤curvatureStageResponseCount P Θ A β z i.val N :=
    curvatureStageResponseCount_mono P Θ A β z i.val hq
  rw [hadd] at hcs
  refine ⟨⟨n,by omega⟩,hen,?_⟩
  change ∃ t, t≤N-n ∧ curvatureRestartFast P Θ A β n
    (curvatureComparisonRun P Θ A β z n).1 i cap (curvatureComparisonRun P Θ A β z n).2 t (fun u => z (n+u))
  refine ⟨q-n,by omega,?_,?_⟩
  · unfold curvatureRestartActive
    rw [←hs, hadd]
    exact curvatureStageEntry_target_active P Θ A β z i q heq
  · omega

end
end SecondOrder
