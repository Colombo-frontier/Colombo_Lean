import SampleReuse.CurvatureFirstStoppedTrajectory

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def stoppedTrajectoryPoint {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (w : Fin M → Bool) (t : ℕ) : Point d :=
  (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).2.1

def stoppedTrajectoryAction {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (i : Fin M) (w : Fin M → Bool) : CurvatureFirstAction d :=
  stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape i.val
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ i.val)

theorem stoppedTrajectoryAction_predictable {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) : SignPredictable (stoppedTrajectoryAction (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀) := by
  intro i w w' he
  exact congrArg (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape i.val)
    (curvatureStoppedRun_signPredictable hBg hBH P ε γ scaleG scaleH f F tape x₀ i w w' he)

theorem stoppedTrajectory_increment {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (w : Fin M → Bool) (i : Fin M) :
    stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w (i.val+1) -
      stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w i.val =
      actionDrift P ε (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w) +
      predictableSignInnovation (fun i w => actionInnovationVector P γ
        (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)) i w := by
  have hi := curvatureStoppedStep_increment hBg hBH P ε γ scaleG scaleH f F tape i.val
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ i.val)
    (extendFiniteSigns w i.val)
  unfold stoppedTrajectoryPoint
  rw [curvatureStoppedRun,hi]
  simp only [predictableSignInnovation,stoppedTrajectoryAction,extendFiniteSigns,dif_pos i.isLt]

/-- Stopped dyadic charging for the actual optimization shadow trajectory.
The sole remaining checkpoint hypotheses concern its chosen stopping times;
actual increment identities, predictability and orthogonality are derived. -/
theorem curvatureFirst_stopped_charging {Ω ι : Type*} [Fintype ι] {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (s t : ι → (Fin M → Bool) → ℕ)
    (hs : ∀ i, SignStoppingTime (s i)) (ht : ∀ i, SignStoppingTime (t i))
    (hst : ∀ i w, s i w ≤ t i w) (hcap : ∀ i w, t i w ≤ M)
    (depth : ℕ) (hdepth : ∀ w (k : Fin M),
      (Finset.univ.filter (fun i => s i w ≤ k.val ∧ k.val < t i w)).card ≤ depth)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    uniformMean (fun w => ∑ i, min (σ^2) (L^2*‖
      stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w (t i w) -
        stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w (s i w)‖^2)) ≤
      2*(depth:ℝ)*(σ*L*uniformMean (fun w : Fin M → Bool => ∑ k : Fin M, ‖actionDrift P ε
        (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ k w)‖) +
        L^2*uniformMean (fun w : Fin M → Bool => ∑ k : Fin M, ‖predictableSignInnovation (fun k w => actionInnovationVector P γ
          (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ k w)) k w‖^2)) := by
  apply finiteSign_stopped_overlap _ _ _ _
    (stoppedTrajectory_increment hBg hBH P ε γ scaleG scaleH f F tape x₀)
    s t hs ht hst hcap depth hdepth hσ hL
  intro i w w' he
  exact congrArg (actionInnovationVector P γ)
    (stoppedTrajectoryAction_predictable hBg hBH P ε γ scaleG scaleH f F tape x₀ i w w' he)

end
end SampleReuse
