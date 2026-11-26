import SecondOrder.BudgetStepOutputLaw
import SecondOrder.SampledRunLaw

open MeasureTheory ProbabilityTheory

namespace SecondOrder
noncomputable section

def orderedBudgetStep {Ω : Type} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) (z : BudgetTracker d L)
    (w : OrderedStepTape Ω d L P γ τ δ) : BudgetTracker d L :=
  budgetedTrackedStep P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ
    (fun x a => branchedOjaReply P f x γ δ a) z w.2.1 (w.1,w.2.2)

def orderedBudgetRun {Ω : Type} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) (N : ℕ) :
    LocalDraws Ω (P.gradientNoise^2) (τ/4) δ × Draws (OrderedStepTape Ω d L P γ τ δ) N →
      BudgetTracker d L :=
  sampledIterate (budgetedTrackedInitial P f Q τ δ) (orderedBudgetStep P f q Q Lip s τ ρ γ δ) N

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.orderedBudgetStep_measurable (h : CommonLoss μ P ν F f)
    (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) :
    Measurable (fun w : BudgetTracker d L × OrderedStepTape Ω d L P γ τ δ =>
      orderedBudgetStep P f q Q Lip s τ ρ γ δ w.1 w.2) :=
  h.budgetedTrackedStep_measurable q Q _ Lip s τ ρ δ (h.branchedOjaReply_measurable γ δ)
    measurable_fst measurable_snd.snd.fst (measurable_snd.fst.prodMk measurable_snd.snd.snd)

theorem CommonLoss.orderedBudgetRun_measurable (h : CommonLoss μ P ν F f)
    (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) (N : ℕ) :
    Measurable (@orderedBudgetRun Ω d L P f q Q Lip s τ ρ γ δ N) :=
  sampledIterate_measurable _ (h.budgetedTrackedInitial_measurable Q τ δ) _
    (h.orderedBudgetStep_measurable q Q Lip s τ ρ γ δ) N

/-- Equality of the full budget state law for every physical horizon.
The old samples and signs are bundled into an independent tape per step. -/
theorem CommonLoss.budgetRunProgram_ordered_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (q Q : ℕ) (Lip s τ ρ : ℝ) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (N : ℕ) :
    budgetRunOutputLaw μ P q Q Lip s τ ρ γ δ (trackingProgramSeedLaw P d L hγ δ)
      (fun q a => hvpReply f a q) N=
      Measure.map (orderedBudgetRun P f q Q Lip s τ ρ γ δ N)
        ((localLaw μ (P.gradientNoise^2) (τ/4) δ).prod (drawsLaw (orderedStepLaw μ P d L hγ τ δ) N)) := by
  let initial := @budgetedTrackedInitial Ω d L P f Q τ δ
  let step := @orderedBudgetStep Ω d L P f q Q Lip s τ ρ γ δ
  have hi : Measurable initial := h.budgetedTrackedInitial_measurable Q τ δ
  have hs : Measurable (fun w : BudgetTracker d L × OrderedStepTape Ω d L P γ τ δ => step w.1 w.2) :=
    h.orderedBudgetStep_measurable q Q Lip s τ ρ γ δ
  induction N with
  | zero =>
    rw [budgetRunOutputLaw_zero μ P q Q Lip s τ ρ γ δ _ a₀ _ h.hvpReply_joint_measurable,
      orderedBudgetRun,sampledIterate_map_zero _ _ _ hi]
    exact h.budgetInitialProgram_outputLaw a₀ Q τ δ
  | succ N ih =>
    have hh := sampledIterate_map_succ (localLaw μ (P.gradientNoise^2) (τ/4) δ)
      (orderedStepLaw μ P d L hγ τ δ) initial hi step hs N
    change Measure.map (orderedBudgetRun P f q Q Lip s τ ρ γ δ (N+1)) _=
      (Measure.map (orderedBudgetRun P f q Q Lip s τ ρ γ δ N) _).bind
        (sampledResponseKernel (orderedStepLaw μ P d L hγ τ δ) step hs) at hh
    rw [budgetRunOutputLaw_succ μ P q Q Lip s τ ρ γ δ _ a₀ _ h.hvpReply_joint_measurable,hh,ih]
    apply congrArg (fun k : BudgetTracker d L → Measure (BudgetTracker d L) =>
      (Measure.map (orderedBudgetRun P f q Q Lip s τ ρ γ δ N)
        ((localLaw μ (P.gradientNoise^2) (τ/4) δ).prod
          (drawsLaw (orderedStepLaw μ P d L hγ τ δ) N))).bind k)
    funext z
    exact h.budgetStepProgram_outputLaw a₀ q Q Lip s τ ρ hγ δ z

end
end SecondOrder
