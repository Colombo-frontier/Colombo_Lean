import SampleReuse.CurvatureFirstDyadicCharging
import SampleReuse.CurvatureFirstDriftVariance
import SampleReuse.CurvatureFirstStoppedCounts

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def stoppedGradientCost {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (depth : ℕ) (w : Fin M → Bool) : ℕ :=
  let τ := stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F tape x₀
  let x := stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀
  let n := (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ M).2.2.1
  treeQueryCost (Finset.univ.filter (fun i : completedNodes depth M => usefulNode i.val ∧ nodeRight i.val ≤ n))
    scaleG (P.gradientNoise^2) (fun i => min (P.gradientNoise^2)
      (P.gradientLip^2*‖x w (τ (nodeRight i.val) w)-x w (τ (nodeLeft i.val) w)‖^2))

theorem Admissible.stopped_gradient_cost_bound {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ) (hscale : 0 ≤ scaleG)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (depth : ℕ) :
    uniformMean (fun w : Fin M → Bool =>
      (stoppedGradientCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w:ℝ)) ≤
      1+2*(32*P.gradientLip*P.gap/(3*ε^2)) +
        scaleG*(P.gradientNoise^2+4*(depth:ℝ)*
          (P.gradientNoise*P.gradientLip*(8*P.gap/(3*ε)) + P.gradientLip^2*(12*P.gap/γ))) := by
  let τ := stoppedGradientTime (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  let x := stoppedTrajectoryPoint (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  let n (w : Fin M → Bool) := (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ M).2.2.1
  let weight (i : completedNodes depth M) (w : Fin M → Bool) := min (P.gradientNoise^2)
    (P.gradientLip^2*‖x w (τ (nodeRight i.val) w)-x w (τ (nodeLeft i.val) w)‖^2)
  have hw (i : completedNodes depth M) (w : Fin M → Bool) : 0 ≤ weight i w := by dsimp [weight]; positivity
  have hp (w : Fin M → Bool) : (stoppedGradientCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w:ℝ) ≤
      1+2*(n w:ℝ)+scaleG*(P.gradientNoise^2+2*∑ i,weight i w) := by
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun i => usefulNode i.val ∧ nodeRight i.val ≤ n w) Finset.univ)
      (fun i _ _ => hw i w)
    have hb := treeQueryCost_upper (Finset.univ.filter (fun i : completedNodes depth M => usefulNode i.val ∧ nodeRight i.val ≤ n w))
      (fun i => weight i w) hscale (sq_nonneg P.gradientNoise) (fun i _ => hw i w)
    change (stoppedGradientCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w:ℝ) ≤ _ at hb
    dsimp only at hb
    apply hb.trans
    gcongr
    have hc := selected_ancestor_card_le depth M (n w)
      (fun i => usefulNode i.val ∧ nodeRight i.val ≤ n w) (fun _ hi => hi)
    convert hc using 1
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hb := uniformMean_mono hp
  simp only [uniformMean_add,uniformMean_const,uniformMean_mul] at hb
  have hc := h.stopped_gradient_count_bound (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hcharge := curvatureFirst_gradient_dyadic_charging (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀ M depth
    P.gradientNoise_pos.le P.gradientLip_pos.le
  have hd := h.stopped_drift_bound (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hv := h.stopped_variance_bound (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hL := P.gradientLip_pos
  have hσ := P.gradientNoise_pos
  have he : uniformMean (fun w => ∑ i,weight i w) ≤ 2*(depth:ℝ)*
      (P.gradientNoise*P.gradientLip*(8*P.gap/(3*ε))+P.gradientLip^2*(12*P.gap/γ)) := by
    apply hcharge.trans
    gcongr
  change uniformMean (fun w => (n w:ℝ)) ≤ _ at hc
  apply hb.trans
  calc
    _ ≤ 1+2*(32*P.gradientLip*P.gap/(3*ε^2)) +
        scaleG*(P.gradientNoise^2+2*(2*(depth:ℝ)*
          (P.gradientNoise*P.gradientLip*(8*P.gap/(3*ε))+P.gradientLip^2*(12*P.gap/γ)))) := by gcongr
    _ = _ := by ring

end
end SampleReuse
