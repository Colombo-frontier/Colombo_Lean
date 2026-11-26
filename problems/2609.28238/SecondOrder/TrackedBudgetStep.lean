import SecondOrder.SampledCaps

open scoped Classical

namespace SecondOrder
noncomputable section

def curvatureRequestPrice {d L : ℕ} (τ : ℝ) (κ : ℕ) (z : TrackedState d L) : ℕ :=
  if trackedCurvatureNeeded τ z then κ else 0

/-- All post-move prices are fixed by the old state, curvature reply and
new sign, before any chord or refresh sample is read. -/
def postRequestPrice {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) : ℕ :=
  requestCharge (requestOracleCost P τ ρ δ (fun _ => 0)) (trackedStepRequests q Lip s τ z r b)

theorem trackedStepRequestPrice_split {d L : ℕ} (P : Parameters) (q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    requestCharge (requestOracleCost P τ ρ δ (fun _ => κ)) (trackedStepRequests q Lip s τ z r b) =
      curvatureRequestPrice τ κ z+postRequestPrice P q Lip s τ ρ δ z r b := by
  simp only [postRequestPrice,requestOracleCost_decomposition,trackedStepRequests_curvature,
    Nat.mul_zero,Nat.add_zero,curvatureRequestPrice]
  split_ifs <;> simp only [Nat.one_mul,Nat.zero_mul,Nat.zero_add,Nat.add_zero] <;> omega

/-- Two causal preflight checks. The curvature price is checked before
reading its tape. The entire known post-move block is reserved before
reading any of its fresh samples; rejecting that reservation reads none
of them. The curvature routine's per-call price κ is an explicit input. -/
def budgetedTrackedStep {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (z : QueryBudgetState (TrackedState d L)) (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ) :
    QueryBudgetState (TrackedState d L) :=
  if z.2.2 then z else
    let c := curvatureRequestPrice τ κ z.1
    if z.2.1+c ≤ Q then
      let r := sampledCurvature τ routine z.1 w.1
      let p := postRequestPrice P q Lip s τ ρ δ z.1 r b
      if z.2.1+c+p ≤ Q then
        (sampledPostStep P f q Lip s τ ρ δ z.1 r b w.2,z.2.1+c+p,false)
      else (z.1,z.2.1+c,true)
    else (z.1,z.2.1,true)

theorem budgetedTrackedStep_frozen {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (z : QueryBudgetState (TrackedState d L)) (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ)
    (hz : z.2.2 = true) : budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine z b w = z := by
  simp only [budgetedTrackedStep,hz,↓reduceIte]

theorem budgetedTrackedStep_spent_le {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (z : QueryBudgetState (TrackedState d L)) (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ)
    (hz : z.2.1 ≤ Q) : (budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine z b w).2.1 ≤ Q := by
  dsimp only [budgetedTrackedStep]
  split_ifs <;> assumption

theorem budgetedTrackedStep_agrees {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (z : TrackedState d L) (spent : ℕ) (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ)
    (hc : spent+requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
      (trackedStepRequests q Lip s τ z (sampledCurvature τ routine z w.1) b) ≤ Q) :
    budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine (z,spent,false) b w =
      (sampledPostStep P f q Lip s τ ρ δ z (sampledCurvature τ routine z w.1) b w.2,
        spent+requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
          (trackedStepRequests q Lip s τ z (sampledCurvature τ routine z w.1) b),false) := by
  rw [trackedStepRequestPrice_split] at hc ⊢
  have he : spent+curvatureRequestPrice τ κ z ≤ Q := by omega
  have hp : spent+curvatureRequestPrice τ κ z+
      postRequestPrice P q Lip s τ ρ δ z (sampledCurvature τ routine z w.1) b ≤ Q := by omega
  simp only [budgetedTrackedStep,Bool.false_eq_true,↓reduceIte,he,hp,Nat.add_assoc,hc]

theorem budgetedTrackedStep_rejected_iff {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (z : TrackedState d L) (spent : ℕ) (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ) :
    (budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine (z,spent,false) b w).2.2 = true ↔
      Q < spent+requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
        (trackedStepRequests q Lip s τ z (sampledCurvature τ routine z w.1) b) := by
  rw [trackedStepRequestPrice_split]
  dsimp only [budgetedTrackedStep]
  simp only [Bool.false_eq_true,↓reduceIte]
  split_ifs <;> simp_all only [Bool.false_eq_true,true_iff,false_iff] <;> omega

/-- The preflight price is exactly the number of gradient/HVP slots
used by the post-move estimators, including old-tree nodes before refresh. -/
theorem postRequestPrice_eq_oracle_slots {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    postRequestPrice P q Lip s τ ρ δ z r b = Fintype.card (PostChordSlot P Lip s τ ρ δ z r b)+
      Fintype.card (PostRefreshSlot P q Lip s τ δ z r b) :=
  (postMove_oracle_slot_count P q Lip s τ ρ δ z r b).symm

/-- Rejection before the curvature call is independent of its reply,
the new sign and every post-move sample. -/
theorem budgetedTrackedStep_curvature_reject {Ω Ψ : Type*} {d L : ℕ}
    (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (z : TrackedState d L) (spent : ℕ)
    (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ) (hc : Q < spent+curvatureRequestPrice τ κ z) :
    budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine (z,spent,false) b w = (z,spent,true) := by
  simp only [budgetedTrackedStep,Bool.false_eq_true,↓reduceIte,Nat.not_le.mpr hc]

/-- Once the curvature reply fixes the endpoint and whole post-move
price, rejection is independent of every post-move sample. -/
theorem budgetedTrackedStep_post_reject {Ω Ψ : Type*} {d L : ℕ}
    (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (z : TrackedState d L) (spent : ℕ)
    (b : Bool) (a : Ψ) (w : PostMoveTape Ω P L τ δ)
    (hc : spent+curvatureRequestPrice τ κ z ≤ Q)
    (hp : Q < spent+curvatureRequestPrice τ κ z+
      postRequestPrice P q Lip s τ ρ δ z (sampledCurvature τ routine z a) b) :
    budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine (z,spent,false) b (a,w) =
      (z,spent+curvatureRequestPrice τ κ z,true) := by
  simp only [budgetedTrackedStep,Bool.false_eq_true,↓reduceIte,hc,Nat.not_le.mpr hp]

end
end SecondOrder
