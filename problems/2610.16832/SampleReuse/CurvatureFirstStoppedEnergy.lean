import SampleReuse.CurvatureFirstStoppedCharging

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem curvatureStoppedStep_point {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) (b : Bool) :
    (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b).2.1 =
      inspectionNextPoint P ε γ s.2.1 (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t s) b := by
  have hp := curvatureFirstInspect_point hBg hBH P ε γ scaleG scaleH F tape t s.2
  simp only [curvatureStoppedStep,stoppedInspectionAction]
  split_ifs
  · simp only [curvatureFirstAdvance]
    cases (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action <;>
      simp only [inspectionNextPoint,hp]
  · rfl
  · rfl

theorem stoppedInspectionAction_valid_or_success {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) :
    ValidInspection f ε γ s.2.1 (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t s) ∨
      stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t s = .success := by
  unfold stoppedInspectionAction
  by_cases ha : s.1 = true
  · simp only [if_pos ha]
    split_ifs with hv
    · exact Or.inl hv
    · exact Or.inr rfl
  · simp only [if_neg ha,or_true]

theorem Admissible.inspection_descent_pair {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ)
    (x : Point d) (a : CurvatureFirstAction d) (hv : ValidInspection f ε γ x a ∨ a = .success) (b : Bool) :
    (f (inspectionNextPoint P ε γ x a b)+f (inspectionNextPoint P ε γ x a (!b)))/2-f x ≤
      -inspectionDecrease P ε γ a := by
  have hh : (∫ b, f (inspectionNextPoint P ε γ x a b) ∂(PMF.uniformOfFintype Bool).toMeasure)-f x ≤
      -inspectionDecrease P ε γ a := by
    rcases hv with hv | rfl
    · exact h.inspection_descent hε hγ x a hv
    · simp only [inspectionNextPoint,inspectionDecrease,integral_const,measureReal_univ_eq_one,
        one_smul,sub_self,neg_zero,le_refl]
  rw [PMF.integral_eq_sum] at hh
  simp only [PMF.uniformOfFintype_apply,Fintype.card_bool,ENNReal.toReal_inv,
    ENNReal.toReal_ofNat,Fintype.sum_bool,smul_eq_mul] at hh
  norm_num only [ENNReal.toReal_natCast] at hh
  norm_num at hh
  cases b <;> simp only [Bool.not_false,Bool.not_true] <;> linarith

theorem Admissible.stopped_step_mean_descent {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (i : Fin M) :
    uniformMean (fun w : Fin M → Bool => f (stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w (i.val+1))) -
      uniformMean (fun w : Fin M → Bool => f (stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w i.val)) ≤
      -uniformMean (fun w => inspectionDecrease P ε γ
        (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)) := by
  let x := stoppedTrajectoryPoint (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  let a := stoppedTrajectoryAction (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  have hnext (w : Fin M → Bool) : x w (i.val+1) = inspectionNextPoint P ε γ (x w i.val) (a i w) (w i) := by
    dsimp only [x,stoppedTrajectoryPoint]
    rw [curvatureStoppedRun,curvatureStoppedStep_point]
    simp only [a,stoppedTrajectoryAction,extendFiniteSigns,dif_pos i.isLt]
  have hpair (w : Fin M → Bool) :
      (f (x w (i.val+1))+f (x (flipSign i w) (i.val+1)))/2-f (x w i.val) ≤
        -inspectionDecrease P ε γ (a i w) := by
    have hs := curvatureStoppedRun_signPredictable hBg hBH P ε γ scaleG scaleH f F tape x₀
      i (flipSign i w) w (signPastEq_flip i i le_rfl w)
    have ha := stoppedTrajectoryAction_predictable hBg hBH P ε γ scaleG scaleH f F tape x₀
      i (flipSign i w) w (signPastEq_flip i i le_rfl w)
    change a i (flipSign i w) = a i w at ha
    have hx : x (flipSign i w) i.val = x w i.val := congrArg (fun s : StoppedOptimizerCache d => s.2.1) hs
    rw [hnext,hnext,hx,ha]
    simp only [flipSign,Function.update_self]
    exact h.inspection_descent_pair hε hγ (x w i.val) (a i w)
      (stoppedInspectionAction_valid_or_success hBg hBH P ε γ scaleG scaleH f F tape i.val _) (w i)
  have hm := uniformMean_mono hpair
  have he := uniformMean_equiv (flipSignEquiv i) (fun w => f (x w (i.val+1)))
  change uniformMean (fun w => f (x (flipSign i w) (i.val+1))) = _ at he
  have hneg : uniformMean (fun w => -inspectionDecrease P ε γ (a i w)) =
      -uniformMean (fun w => inspectionDecrease P ε γ (a i w)) := by
    simp only [uniformMean,pmfMean,smul_neg,Finset.sum_neg_distrib]
  simp only [div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,uniformMean_sub,uniformMean_mul,uniformMean_add,he,hneg] at hm
  change uniformMean (fun w => f (x w (i.val+1))) - uniformMean (fun w => f (x w i.val)) ≤
    -uniformMean (fun w => inspectionDecrease P ε γ (a i w))
  linarith

theorem Admissible.stopped_total_decrease {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    uniformMean (fun w : Fin M → Bool => ∑ i : Fin M, inspectionDecrease P ε γ
      (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)) ≤ P.gap := by
  let x := stoppedTrajectoryPoint (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀
  let V (t : ℕ) := uniformMean (fun w : Fin M → Bool => f (x w t))
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    h.stopped_step_mean_descent hBg hBH hε hγ scaleG scaleH tape i)
  change (∑ i : Fin M, (V (i.val+1)-V i.val)) ≤ _ at hb
  have htel : (∑ i : Fin M, (V (i.val+1)-V i.val)) = V M-V 0 := by
    rw [← Finset.sum_range (n := M) (fun n => V (n+1)-V n)]
    exact Finset.sum_range_sub V M
  rw [htel,Finset.sum_neg_distrib] at hb
  have hzero : V 0 = f x₀ := by
    simpa only [V,x,stoppedTrajectoryPoint,curvatureStoppedRun,optimizerInitial] using
      (uniformMean_const (α := Fin M → Bool) (f x₀))
  have hgap := uniformMean_le_const P.gap (fun w : Fin M → Bool => h.gap_bound (x w M))
  rw [uniformMean_sub,uniformMean_const] at hgap
  change f x₀-V M ≤ P.gap at hgap
  rw [hzero] at hb
  simp only [uniformMean,pmfMean_finset_sum]
  change (∑ i : Fin M, uniformMean (fun w => inspectionDecrease P ε γ
    (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w))) ≤ P.gap
  linarith

end
end SampleReuse
