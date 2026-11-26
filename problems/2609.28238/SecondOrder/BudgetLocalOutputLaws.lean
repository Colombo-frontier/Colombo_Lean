import SecondOrder.BudgetProgramOutputLaw
import SecondOrder.BranchedOjaOutputLaw

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.budgetInitialProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (Q : ℕ) (τ δ : ℝ) :
    OracleProgram.outputLaw μ (.grad 0) ((trackedInitial 0,0,true) : BudgetTracker d L)
      (fun q z => hvpReply f z q) (budgetInitialProgram P Q τ δ) Q=
      Measure.map (budgetedTrackedInitial P f Q τ δ)
        (localLaw μ (P.gradientNoise^2) (τ/4) δ) := by
  by_cases hc : localQueryCount (P.gradientNoise^2) (τ/4) δ≤Q
  · have hp := (gradientAnchorProgram_measurable (d := d) P (τ/4) δ).comp
      (fun _ : Unit => (0 : Point d)) measurable_const
    have hN := (localReplyProgram_usesExactly (P.gradientNoise^2) (τ/4) δ
      (fun _ => HvpQuery.grad (0 : Point d))).usesAtMost
    let g := fun a : Point d =>
      ((trackedInitial a,localQueryCount (P.gradientNoise^2) (τ/4) δ,false) : BudgetTracker d L)
    have hg : Measurable g := (trackedInitial_measurable measurable_id).prodMk measurable_const
    rw [budgetInitialProgram,if_pos hc]
    have hm := OracleProgram.outputLaw_bind_done μ (.grad 0) 0 (0 : Point d)
        ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ (fun q z => hvpReply f z q)
        h.hvpReply_joint_measurable (gradientAnchorProgram P 0 (τ/4) δ) hp Q
        (OracleProgram.usesAtMost_mono hN hc) g hg
    refine hm.trans ?_
    rw [OracleProgram.outputLaw_of_budget_le μ (.grad 0) 0 (0 : Point d) a₀
        (fun q z => hvpReply f z q) h.hvpReply_joint_measurable
        (gradientAnchorProgram P 0 (τ/4) δ) hp _ hN Q hc,
      h.gradientAnchorProgram_outputLaw a₀ 0 (τ/4) δ,
      Measure.map_map hg (h.anchor_measurable 0 (τ/4) δ)]
    congr 1
    funext w
    simp only [Function.comp_apply,g,budgetedTrackedInitial,if_pos hc,sampledInitial]
  · rw [budgetInitialProgram,if_neg hc,OracleProgram.outputLaw_done]
    have he : (@budgetedTrackedInitial Ω d L P f Q τ δ)=
        (fun _ => ((trackedInitial 0,0,true) : BudgetTracker d L)) := by
      funext w
      exact if_neg hc
    rw [he]
    simp

theorem CommonLoss.requestedOjaProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (τ : ℝ) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (z : TrackedState d L) :
    OracleProgram.seededOutputLaw μ (branchedOjaSeedLaw P d hγ δ) (.grad 0) .certificate
      (fun q a => hvpReply f a q) (fun seed => requestedOjaProgram P τ γ δ (z,seed))
      (curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) z)=
      Measure.map (fun w : (BranchedOjaDraws Ω d P γ δ : Type) =>
        sampledCurvature τ (fun x w => branchedOjaReply P f x γ δ w) z w)
        (branchedOjaLaw μ P d hγ δ) := by
  by_cases hc : trackedCurvatureNeeded τ z
  · simp only [requestedOjaProgram,curvatureRequestPrice,sampledCurvature,if_pos hc]
    exact h.branchedOjaProgram_outputLaw a₀ hγ δ z.physical.point
  · simp only [requestedOjaProgram,curvatureRequestPrice,sampledCurvature,if_neg hc]
    rw [OracleProgram.seededOutputLaw_done]
    simp

theorem CommonLoss.postRefreshProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (q : ℕ) (Lip s τ δ : ℝ) (w : PostProgramInput d L δ) :
    OracleProgram.outputLaw μ (.grad 0) 0 (fun q z => hvpReply f z q)
      (postRefreshProgram P q Lip s τ δ w)
      (Fintype.card (PostRefreshSlot P q Lip s τ δ w.1 w.2.1 w.2.2.1))=
      Measure.map (fun a => sampledRefreshAnchor P f q Lip s τ δ w.1 w.2.1 w.2.2.1 a)
        (localLaw μ (P.gradientNoise^2) (τ/4) δ) := by
  rw [postRefreshCall_count,trackedStepRequests_anchor]
  by_cases hc : (trackedNext Lip s τ w.1 w.2.1 w.2.2.1).running=true ∧
    trackedRestart q τ w.1 w.2.1
  · simp only [postRefreshProgram,sampledRefreshAnchor,if_pos hc,Nat.one_mul]
    exact h.gradientAnchorProgram_outputLaw a₀ _ (τ/4) δ
  · simp only [postRefreshProgram,sampledRefreshAnchor,if_neg hc,Nat.zero_mul]
    rw [OracleProgram.outputLaw_done]
    simp

end
end SecondOrder
