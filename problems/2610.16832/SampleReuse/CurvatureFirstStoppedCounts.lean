import SampleReuse.CurvatureFirstStoppedEnergy
import SampleReuse.FiniteSignCheckpointTime

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def actionGradientCount {d : ℕ} : CurvatureFirstAction d → ℕ
  | .gradient _ => 1
  | _ => 0

def actionStepCount {d : ℕ} : CurvatureFirstAction d → ℕ
  | .success => 0
  | _ => 1

theorem curvatureStoppedStep_gradientClock {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) (b : Bool) :
    (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b).2.2.1 =
      s.2.2.1 + actionGradientCount (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t s) := by
  simp only [curvatureStoppedStep,stoppedInspectionAction]
  split_ifs
  · simp only [curvatureFirstAdvance]
    cases ha : (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action with
    | success => simp only [actionGradientCount,Nat.add_zero]
    | gradient g =>
      simp only [actionGradientCount]
      simp only [curvatureFirstInspect] at ha ⊢
      split_ifs at ha ⊢; simp_all
    | curvature v =>
      simp only [actionGradientCount,Nat.add_zero]
      simp only [curvatureFirstInspect] at ha ⊢
      split_ifs at ha ⊢; simp_all
  · simp only [actionGradientCount,Nat.add_zero]
  · simp only [actionGradientCount,Nat.add_zero]

theorem actionGradientCount_charge {d : ℕ} (P : Parameters) {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ)
    (a : CurvatureFirstAction d) :
    (actionGradientCount a : ℝ) ≤ (32*P.gradientLip/(3*ε^2))*inspectionDecrease P ε γ a := by
  have hL1 := P.gradientLip_pos
  have hL2 := P.hessianLip_pos
  cases a with
  | success => simp only [actionGradientCount,inspectionDecrease,Nat.cast_zero,mul_zero,le_refl]
  | gradient g =>
    simp only [actionGradientCount,inspectionDecrease,Nat.cast_one]
    apply le_of_eq
    field_simp
  | curvature v =>
    simp only [actionGradientCount,inspectionDecrease,Nat.cast_zero]
    positivity

theorem actionStepCount_charge {d : ℕ} (P : Parameters) {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ)
    (a : CurvatureFirstAction d) :
    (actionStepCount a : ℝ) ≤ (32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3)*inspectionDecrease P ε γ a := by
  have hL1 := P.gradientLip_pos
  have hL2 := P.hessianLip_pos
  cases a with
  | success => simp only [actionStepCount,inspectionDecrease,Nat.cast_zero,mul_zero,le_refl]
  | gradient g =>
    simp only [actionStepCount,inspectionDecrease,Nat.cast_one]
    have he : (32*P.gradientLip/(3*ε^2))*(3*ε^2/(32*P.gradientLip)) = 1 := by field_simp
    have hp : 0 ≤ (12*P.hessianLip^2/γ^3)*(3*ε^2/(32*P.gradientLip)) := by positivity
    nlinarith
  | curvature v =>
    simp only [actionStepCount,inspectionDecrease,Nat.cast_one]
    have he : (12*P.hessianLip^2/γ^3)*(γ^3/(12*P.hessianLip^2)) = 1 := by field_simp
    have hp : 0 ≤ (32*P.gradientLip/(3*ε^2))*(γ^3/(12*P.hessianLip^2)) := by positivity
    nlinarith

theorem curvatureStoppedRun_gradientClock_sum {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (w : Fin M → Bool) :
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ M).2.2.1 =
      ∑ i : Fin M, actionGradientCount (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w) := by
  have hs (t : ℕ) :
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).2.2.1 =
        ∑ i ∈ Finset.range t, actionGradientCount (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape i
          (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ i)) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [curvatureStoppedRun,curvatureStoppedStep_gradientClock,ih,Finset.sum_range_succ]
  simpa only [Finset.sum_range,stoppedTrajectoryAction] using hs M

theorem Admissible.stopped_gradient_count_bound {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    uniformMean (fun w : Fin M → Bool =>
      ((curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ M).2.2.1:ℝ)) ≤
      32*P.gradientLip*P.gap/(3*ε^2) := by
  simp_rw [curvatureStoppedRun_gradientClock_sum,Nat.cast_sum]
  have hb := uniformMean_mono (fun w : Fin M → Bool => Finset.sum_le_sum (fun (i : Fin M) (_ : i ∈ Finset.univ) =>
    actionGradientCount_charge P hε hγ (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)))
  simp only [← Finset.mul_sum,uniformMean_mul] at hb
  have hL := P.gradientLip_pos
  have hm := mul_le_mul_of_nonneg_left (h.stopped_total_decrease (M := M) hBg hBH hε hγ scaleG scaleH tape)
    (by positivity : 0 ≤ 32*P.gradientLip/(3*ε^2))
  exact hb.trans (by convert hm using 1; ring)

theorem Admissible.stopped_step_count_bound {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    uniformMean (fun w : Fin M → Bool => ∑ i : Fin M,
      (actionStepCount (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w):ℝ)) ≤
      (32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3)*P.gap := by
  have hb := uniformMean_mono (fun w : Fin M → Bool => Finset.sum_le_sum (fun (i : Fin M) (_ : i ∈ Finset.univ) =>
    actionStepCount_charge P hε hγ (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)))
  simp only [← Finset.mul_sum,uniformMean_mul] at hb
  have hL1 := P.gradientLip_pos
  have hL2 := P.hessianLip_pos
  exact hb.trans (mul_le_mul_of_nonneg_left
    (h.stopped_total_decrease (M := M) hBg hBH hε hγ scaleG scaleH tape) (by positivity))

end
end SampleReuse
