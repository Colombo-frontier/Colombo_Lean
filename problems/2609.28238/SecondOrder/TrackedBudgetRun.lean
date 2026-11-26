import SecondOrder.TrackedBudgetStep

open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ω Ψ : Type*} {d L : ℕ}

def freshTrackedPrice (P : Parameters) (f : Ω → Point d → ℝ) (q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) : ℕ :=
  requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
    (freshTrackedRequests P f q Lip s τ ρ δ routine g β N w)

theorem freshTrackedPrice_zero (P : Parameters) (f : Ω → Point d → ℝ) (q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) 0) :
    freshTrackedPrice P f q κ Lip s τ ρ δ routine g β 0 w = localQueryCount (P.gradientNoise^2) (τ/4) δ := by
  simp [freshTrackedPrice,freshTrackedRequests,requestCharge,requestOracleCost]

theorem freshTrackedPrice_succ (P : Parameters) (f : Ω → Point d → ℝ) (q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (g : Point d) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) (N+1)) :
    freshTrackedPrice P f q κ Lip s τ ρ δ routine g β (N+1) w =
      freshTrackedPrice P f q κ Lip s τ ρ δ routine g β N w.1+
        requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
          (trackedStepRequests q Lip s τ (freshTrackedRun P f q Lip s τ ρ δ routine g β N w.1)
            (sampledCurvature τ routine (freshTrackedRun P f q Lip s τ ρ δ routine g β N w.1) w.2.1) (β N)) := by
  simp only [freshTrackedPrice,freshTrackedRequests,requestCharge_append]

/-- If the initial price cannot be reserved, the anchor batch is never
read. The zero tracker is only a rejected-output placeholder. -/
def budgetedTrackedInitial (P : Parameters) (f : Ω → Point d → ℝ) (Q : ℕ) (τ δ : ℝ)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) : QueryBudgetState (TrackedState d L) :=
  if localQueryCount (P.gradientNoise^2) (τ/4) δ ≤ Q then
    (sampledInitial P f τ δ a,localQueryCount (P.gradientNoise^2) (τ/4) δ,false)
  else (trackedInitial 0,0,true)

def budgetedTrackedRun (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool) :
    (N : ℕ) → Draws (TrackingStepTape Ω Ψ P L τ δ) N → QueryBudgetState (TrackedState d L)
  | 0, _ => budgetedTrackedInitial P f Q τ δ a
  | N+1, w => budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine
      (budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w.1) (β N) w.2

/-- A deterministic bound on every path, including arbitrary failed
local replies and an initial rejection. -/
theorem budgetedTrackedRun_spent_le (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    (budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w).2.1 ≤ Q := by
  induction N with
  | zero => dsimp only [budgetedTrackedRun,budgetedTrackedInitial]; split_ifs <;> simp_all
  | succ N ih => exact budgetedTrackedStep_spent_le P f q Q κ Lip s τ ρ δ routine _ _ _ (ih w.1)

/-- The capped process either exactly realizes the entire uncapped
history at its recorded price, or rejects because that complete history
would exceed Q. This includes both the initial and two-stage checks. -/
theorem budgetedTrackedRun_dichotomy (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    let g := gradientAnchor P f 0 (τ/4) δ a
    (freshTrackedPrice P f q κ Lip s τ ρ δ routine g β N w ≤ Q ∧
      budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w =
        (freshTrackedRun P f q Lip s τ ρ δ routine g β N w,
          freshTrackedPrice P f q κ Lip s τ ρ δ routine g β N w,false)) ∨
    (Q < freshTrackedPrice P f q κ Lip s τ ρ δ routine g β N w ∧
      (budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w).2.2 = true) := by
  dsimp only
  induction N with
  | zero =>
    rw [freshTrackedPrice_zero]
    by_cases hc : localQueryCount (P.gradientNoise^2) (τ/4) δ ≤ Q
    · exact Or.inl ⟨hc,by simp [budgetedTrackedRun,budgetedTrackedInitial,hc,freshTrackedRun,sampledInitial]⟩
    · exact Or.inr ⟨Nat.lt_of_not_le hc,by simp [budgetedTrackedRun,budgetedTrackedInitial,hc]⟩
  | succ N ih =>
    rcases ih w.1 with ⟨hc,he⟩ | ⟨hc,he⟩
    · by_cases hn : freshTrackedPrice P f q κ Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ a) β (N+1) w ≤ Q
      · refine Or.inl ⟨hn,?_⟩
        rw [budgetedTrackedRun,he]
        rw [freshTrackedPrice_succ] at hn
        rw [budgetedTrackedStep_agrees P f q Q κ Lip s τ ρ δ routine _ _ _ _ hn]
        rw [freshTrackedRun,freshTrackedPrice_succ]
      · refine Or.inr ⟨Nat.lt_of_not_le hn,?_⟩
        rw [budgetedTrackedRun,he,budgetedTrackedStep_rejected_iff]
        rw [freshTrackedPrice_succ] at hn
        exact Nat.lt_of_not_le hn
    · refine Or.inr ⟨?_,?_⟩
      · rw [freshTrackedPrice_succ]
        omega
      · rw [budgetedTrackedRun,budgetedTrackedStep_frozen P f q Q κ Lip s τ ρ δ routine _ _ _ he]
        exact he

theorem budgetedTrackedRun_agrees (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N)
    (hc : freshTrackedPrice P f q κ Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ a) β N w ≤ Q) :
    budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w =
      (freshTrackedRun P f q Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ a) β N w,
        freshTrackedPrice P f q κ Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ a) β N w,false) := by
  rcases budgetedTrackedRun_dichotomy P f q Q κ Lip s τ ρ δ routine a β N w with ⟨_,he⟩ | ⟨hn,_⟩
  · exact he
  · omega

theorem budgetedTrackedRun_rejected_iff (P : Parameters) (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    (budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w).2.2 = true ↔
      Q < freshTrackedPrice P f q κ Lip s τ ρ δ routine (gradientAnchor P f 0 (τ/4) δ a) β N w := by
  rcases budgetedTrackedRun_dichotomy P f q Q κ Lip s τ ρ δ routine a β N w with ⟨hc,he⟩ | ⟨hc,he⟩
  · simp [he,Nat.not_lt.mpr hc]
  · simp [he,hc]

/-- When the anchor cannot be afforded, the whole run is independent
of its initial batch, every later tape and all signs. -/
theorem budgetedTrackedRun_initial_reject (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool) (N : ℕ)
    (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N)
    (hc : Q < localQueryCount (P.gradientNoise^2) (τ/4) δ) :
    budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w = (trackedInitial 0,0,true) := by
  induction N with
  | zero => simp only [budgetedTrackedRun,budgetedTrackedInitial,Nat.not_le.mpr hc,↓reduceIte]
  | succ N ih =>
    rw [budgetedTrackedRun,ih w.1]
    exact budgetedTrackedStep_frozen P f q Q κ Lip s τ ρ δ routine _ _ _ rfl

end
end SecondOrder
