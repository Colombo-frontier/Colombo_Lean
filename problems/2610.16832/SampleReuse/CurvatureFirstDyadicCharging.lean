import SampleReuse.CurvatureFirstStoppedCharging
import SampleReuse.FiniteSignCheckpointTime

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem curvatureFirst_gradient_dyadic_charging {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (K depth : ℕ) {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    let τ := stoppedGradientTime (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
    let x := stoppedTrajectoryPoint (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
    uniformMean (fun w => ∑ i : completedNodes depth K,
      min (σ^2) (L^2*‖x w (τ (nodeRight i.val) w)-x w (τ (nodeLeft i.val) w)‖^2)) ≤
      2*(depth:ℝ)*(σ*L*uniformMean (fun w : Fin M → Bool => ∑ k : Fin M, ‖actionDrift P ε
        (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ k w)‖) +
        L^2*uniformMean (fun w : Fin M → Bool => ∑ k : Fin M,
          ‖predictableSignInnovation (fun k w => actionInnovationVector P γ
            (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ k w)) k w‖^2)) := by
  let τ := stoppedGradientTime (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  have hmono (w : Fin M → Bool) : Monotone (fun k => τ k w) :=
    stoppedGradientTime_mono hBg hBH P ε γ scaleG scaleH f F tape x₀ w
  apply curvatureFirst_stopped_charging hBg hBH P ε γ scaleG scaleH f F tape x₀
    (fun i : completedNodes depth K => τ (nodeLeft i.val))
    (fun i : completedNodes depth K => τ (nodeRight i.val))
  · intro i
    exact stoppedGradientTime_stopping hBg hBH P ε γ scaleG scaleH f F tape x₀ _
  · intro i
    exact stoppedGradientTime_stopping hBg hBH P ε γ scaleG scaleH f F tape x₀ _
  · intro i w
    exact hmono w (nodeLeft_lt_right i.val).le
  · intro i w
    exact boundedSignEventTime_le _ w
  · intro w k
    exact stopped_dyadic_overlap K depth τ hmono w k.val
  · exact hσ
  · exact hL

end
end SampleReuse
