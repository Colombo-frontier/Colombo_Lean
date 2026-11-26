import SampleReuse.CurvatureFirstDyadicCharging
import SampleReuse.CurvatureFirstDriftVariance
import SampleReuse.CurvatureFirstStoppedCounts

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def stoppedAcceptedSteps {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (w : Fin M → Bool) : ℕ :=
  ∑ i : Fin M, actionStepCount (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)

theorem curvatureFirst_hessian_dyadic_charging {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (depth : ℕ) {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    let x := stoppedTrajectoryPoint (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
    uniformMean (fun w => ∑ i : completedNodes depth M,
      min (σ^2) (L^2*‖x w (nodeRight i.val)-x w (nodeLeft i.val)‖^2)) ≤
      2*(depth:ℝ)*(σ*L*uniformMean (fun w : Fin M → Bool => ∑ k : Fin M, ‖actionDrift P ε
        (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ k w)‖) +
        L^2*uniformMean (fun w : Fin M → Bool => ∑ k : Fin M,
          ‖predictableSignInnovation (fun k w => actionInnovationVector P γ
            (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ k w)) k w‖^2)) := by
  apply curvatureFirst_stopped_charging hBg hBH P ε γ scaleG scaleH f F tape x₀
    (fun i : completedNodes depth M => fun _ => nodeLeft i.val)
    (fun i : completedNodes depth M => fun _ => nodeRight i.val)
  · intro i j w w' _; rfl
  · intro i j w w' _; rfl
  · intro i _; exact (nodeLeft_lt_right i.val).le
  · intro i _; exact (mem_completedNodes i.val).mp i.property
  · intro w k
    exact stopped_dyadic_overlap M depth (fun n (_ : Fin M → Bool) => n) (fun _ => monotone_id) w k.val
  · exact hσ
  · exact hL

/-- The terminal inspection is charged at the last retained point, in
addition to every accepted move's Hessian checkpoint. -/
def stoppedHessianCost {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (depth : ℕ) (w : Fin M → Bool) : ℕ :=
  let x := stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀
  let n := stoppedAcceptedSteps hBg hBH P ε γ scaleG scaleH f F tape x₀ w
  treeQueryCost (Finset.univ.filter (fun i : completedNodes depth M => usefulNode i.val ∧ nodeRight i.val ≤ n))
    scaleH (P.hessianNoise^2) (fun i => min (P.hessianNoise^2)
      (P.hessianLip^2*‖x w (nodeRight i.val)-x w (nodeLeft i.val)‖^2))

theorem Admissible.stopped_hessian_cost_bound {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ) (hscale : 0 ≤ scaleH)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (depth : ℕ) :
    uniformMean (fun w : Fin M → Bool =>
      (stoppedHessianCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w:ℝ)) ≤
      1+2*((32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3)*P.gap) +
        scaleH*(P.hessianNoise^2+4*(depth:ℝ)*
          (P.hessianNoise*P.hessianLip*(8*P.gap/(3*ε)) + P.hessianLip^2*(12*P.gap/γ))) := by
  let x := stoppedTrajectoryPoint (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  let n := stoppedAcceptedSteps (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  let weight (i : completedNodes depth M) (w : Fin M → Bool) := min (P.hessianNoise^2)
    (P.hessianLip^2*‖x w (nodeRight i.val)-x w (nodeLeft i.val)‖^2)
  have hw (i : completedNodes depth M) (w : Fin M → Bool) : 0 ≤ weight i w := by dsimp [weight]; positivity
  have hp (w : Fin M → Bool) : (stoppedHessianCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w:ℝ) ≤
      1+2*(n w:ℝ)+scaleH*(P.hessianNoise^2+2*∑ i,weight i w) := by
    have hc := selected_ancestor_card_le depth M (n w)
      (fun i => usefulNode i.val ∧ nodeRight i.val ≤ n w) (fun _ hi => hi)
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun i => usefulNode i.val ∧ nodeRight i.val ≤ n w) Finset.univ)
      (fun i _ _ => hw i w)
    have hb := treeQueryCost_upper (Finset.univ.filter (fun i : completedNodes depth M => usefulNode i.val ∧ nodeRight i.val ≤ n w))
      (fun i => weight i w) hscale (sq_nonneg P.hessianNoise) (fun i _ => hw i w)
    change (stoppedHessianCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w:ℝ) ≤ _ at hb
    apply hb.trans
    gcongr
    convert hc using 1
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hb := uniformMean_mono hp
  simp only [uniformMean_add,uniformMean_const,uniformMean_mul] at hb
  have hc := h.stopped_step_count_bound (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hn : uniformMean (fun w : Fin M → Bool => (n w:ℝ)) ≤
      (32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3)*P.gap := by
    simpa only [n,stoppedAcceptedSteps,Nat.cast_sum] using hc
  have hcharge := curvatureFirst_hessian_dyadic_charging (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀ depth
    P.hessianNoise_pos.le P.hessianLip_pos.le
  have hd := h.stopped_drift_bound (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hv := h.stopped_variance_bound (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hL := P.hessianLip_pos
  have hσ := P.hessianNoise_pos
  have he : uniformMean (fun w => ∑ i,weight i w) ≤ 2*(depth:ℝ)*
      (P.hessianNoise*P.hessianLip*(8*P.gap/(3*ε))+P.hessianLip^2*(12*P.gap/γ)) := by
    apply hcharge.trans
    gcongr
  nlinarith [mul_le_mul_of_nonneg_left he hscale]

end
end SampleReuse
