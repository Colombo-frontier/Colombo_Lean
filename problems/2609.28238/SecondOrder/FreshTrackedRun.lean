import SecondOrder.FiniteSampledSource

open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ω Ψ : Type*} {d L : ℕ}

/-- Execution on the actual recursive product history. The old state is
formed before the new curvature and post-move samples are exposed. -/
def freshTrackedRun (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) :
    (N : ℕ) → Draws (TrackingStepTape Ω Ψ P L τ δ) N → TrackedState d L
  | 0, _ => trackedInitial g
  | N+1, w =>
      let z := freshTrackedRun P f q Lip s τ ρ δ routine g β N w.1
      sampledPostStep P f q Lip s τ ρ δ z (sampledCurvature τ routine z w.2.1) (β N) w.2.2

def freshTrackedRequests (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) :
    (N : ℕ) → Draws (TrackingStepTape Ω Ψ P L τ δ) N → List (TrackingRequest d)
  | 0, _ => [.anchor 0]
  | N+1, w =>
      let z := freshTrackedRun P f q Lip s τ ρ δ routine g β N w.1
      freshTrackedRequests P f q Lip s τ ρ δ routine g β N w.1 ++
        trackedStepRequests q Lip s τ z (sampledCurvature τ routine z w.2.1) (β N)

def freshTrackedCalls (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) :
    (N : ℕ) → Draws (TrackingStepTape Ω Ψ P L τ δ) N → ℕ
  | 0, _ => 0
  | N+1, w =>
      freshTrackedCalls P f q Lip s τ ρ δ routine g β N w.1+
        sampledStepCallCount q Lip s τ routine (freshTrackedRun P f q Lip s τ ρ δ routine g β N w.1) (β N) w.2.1

def freshTrackedFailure (F : Point d → ℝ) (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ)
    (Lip s τ γ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) :
    FreshCallFailure (TrackingStepTape Ω Ψ P L τ δ) := fun N w v =>
  sampledStepFailure F P f q Lip s τ γ ρ δ routine (freshTrackedRun P f q Lip s τ ρ δ routine g β N w) (β N) v

theorem freshTrackedRun_eq (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    freshTrackedRun P f q Lip s τ ρ δ routine g β N w =
      trackedRun q Lip s τ (finiteSampledSource P f q Lip s τ ρ δ routine g N w) N (fun i => β i.val) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [freshTrackedRun,trackedRun,
      trackedRun_prefix_congr q Lip s τ (finiteSampledSource_extend P f q Lip s τ ρ δ routine g N w) N le_rfl]
    simp only [Fin.init_def,Fin.coe_castSucc,Fin.val_last]
    change _ = trackedStep q Lip s τ
      (trackedRun q Lip s τ (finiteSampledSource P f q Lip s τ ρ δ routine g N w.1) N (fun i => β i.val)) _ _ _ _
    rw [← ih w.1]
    simp only [finiteSampledSource,Nat.lt_succ_self,↓reduceDIte,drawsVector_last,Fin.val_last]
    rfl

theorem freshTrackedRequests_eq (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    freshTrackedRequests P f q Lip s τ ρ δ routine g β N w =
      trackedRequestTrace q Lip s τ (finiteSampledSource P f q Lip s τ ρ δ routine g N w) N (fun i => β i.val) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [freshTrackedRequests,trackedRequestTrace,
      trackedRequestTrace_prefix_congr q Lip s τ (finiteSampledSource_extend P f q Lip s τ ρ δ routine g N w) N le_rfl,
      trackedRun_prefix_congr q Lip s τ (finiteSampledSource_extend P f q Lip s τ ρ δ routine g N w) N le_rfl]
    simp only [Fin.init_def,Fin.coe_castSucc,Fin.val_last]
    change _ = trackedRequestTrace q Lip s τ (finiteSampledSource P f q Lip s τ ρ δ routine g N w.1) N (fun i => β i.val) ++ _
    rw [← ih w.1,← freshTrackedRun_eq P f q Lip s τ ρ δ routine g β N w.1]
    simp only [finiteSampledSource,Nat.lt_succ_self,↓reduceDIte,drawsVector_last,Fin.val_last]

theorem freshTrackedRequests_length (P : Parameters) (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    (freshTrackedRequests P f q Lip s τ ρ δ routine g β N w).length =
      1+freshTrackedCalls P f q Lip s τ ρ δ routine g β N w := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [freshTrackedRequests,List.length_append,ih,freshTrackedCalls,
      sampledStepCallCount_eq_requests,Nat.add_assoc]

theorem freshTrackedCalls_le (P : Parameters) (f : Ω → Point d → ℝ) {q : ℕ} (hq : 0 < q)
    (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    freshTrackedCalls P f q Lip s τ ρ δ routine g β N w ≤ 4*N+1 := by
  have hh := trackedRequestTrace_length_le hq Lip s τ
    (finiteSampledSource P f q Lip s τ ρ δ routine g N w) (fun i : Fin N => β i.val)
  rw [← freshTrackedRequests_eq P f q Lip s τ ρ δ routine g β N w,freshTrackedRequests_length] at hh
  omega

theorem freshTrackedHistoryGood_iff (F : Point d → ℝ) (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ γ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d) (g : Point d)
    (β : ℕ → Bool) (N : ℕ) (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    trackedHistoryGood F q Lip s τ γ ρ (finiteSampledSource P f q Lip s τ ρ δ routine g N w) N (fun i => β i.val) ↔
      ‖g-gradient F 0‖ ≤ τ/4 ∧ freshHistoryGood (freshTrackedFailure F P f q Lip s τ γ ρ δ routine g β) N w := by
  induction N with
  | zero => simp [trackedHistoryGood,finiteSampledSource,freshHistoryGood]
  | succ N ih =>
    rw [trackedHistoryGood,
      trackedHistoryGood_prefix_congr F q Lip s τ γ ρ
        (finiteSampledSource_extend P f q Lip s τ ρ δ routine g N w) N le_rfl,
      trackedRun_prefix_congr q Lip s τ (finiteSampledSource_extend P f q Lip s τ ρ δ routine g N w) N le_rfl]
    simp only [Fin.init_def,Fin.coe_castSucc,Fin.val_last]
    change (trackedHistoryGood F q Lip s τ γ ρ
      (finiteSampledSource P f q Lip s τ ρ δ routine g N w.1) N (fun i => β i.val) ∧ _) ↔ _
    rw [ih w.1,← freshTrackedRun_eq P f q Lip s τ ρ δ routine g β N w.1]
    simp only [finiteSampledSource,Nat.lt_succ_self,↓reduceDIte,drawsVector_last,Fin.val_last]
    rw [← sampledStepFailure_iff F P f q Lip s τ γ ρ δ routine _ (β N) w.2]
    simp only [freshHistoryGood,freshTrackedFailure,and_assoc]

end
end SecondOrder
