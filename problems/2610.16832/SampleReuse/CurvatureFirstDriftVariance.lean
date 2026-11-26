import SampleReuse.CurvatureFirstStoppedEnergy

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem actionDrift_charge {d : ℕ} (P : Parameters) {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ)
    {f : Point d → ℝ} {x : Point d} (a : CurvatureFirstAction d)
    (hv : ValidInspection f ε γ x a ∨ a = .success) :
    ‖actionDrift P ε a‖ ≤ (8/(3*ε))*inspectionDecrease P ε γ a := by
  have hL1 := P.gradientLip_pos
  have hL2 := P.hessianLip_pos
  cases a with
  | success => simp only [actionDrift,inspectionDecrease,norm_zero,mul_zero,le_refl]
  | gradient g =>
    have hg : 3*ε/4 < ‖g‖ := (hv.resolve_right (by intro he; cases he)).2
    have hn : ‖(‖g‖⁻¹:ℝ) • g‖ = 1 :=
      (normalized_alignment hε (hv.resolve_right (by intro he; cases he)).1 hg).1
    have hc : 0 ≤ ε/(4*P.gradientLip) := by positivity
    simp only [actionDrift,inspectionDecrease,norm_smul,hn,mul_one,Real.norm_eq_abs,abs_neg,abs_of_nonneg hc]
    have he : (8/(3*ε))*(3*ε^2/(32*P.gradientLip)) = ε/(4*P.gradientLip) := by field_simp; ring
    exact le_of_eq he.symm
  | curvature v =>
    simp only [actionDrift,inspectionDecrease,norm_zero]
    positivity

theorem actionInnovation_charge {d : ℕ} (P : Parameters) {ε γ : ℝ} (hγ : 0 < γ)
    {f : Point d → ℝ} {x : Point d} (a : CurvatureFirstAction d)
    (hv : ValidInspection f ε γ x a ∨ a = .success) (b : Bool) :
    ‖signValue b • actionInnovationVector P γ a‖^2 ≤ (12/γ)*inspectionDecrease P ε γ a := by
  have hL1 := P.gradientLip_pos
  have hL2 := P.hessianLip_pos
  have hb : |signValue b| = 1 := by cases b <;> norm_num [signValue]
  cases a with
  | success => simp only [actionInnovationVector,inspectionDecrease,smul_zero,norm_zero,
      zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  | gradient g =>
    simp only [actionInnovationVector,inspectionDecrease,smul_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    positivity
  | curvature v =>
    have hn : ‖v‖ = 1 := (hv.resolve_right (by intro he; cases he)).1
    have hc : 0 ≤ γ/P.hessianLip := by positivity
    simp only [actionInnovationVector,inspectionDecrease,norm_smul,Real.norm_eq_abs,hb,one_mul,
      hn,mul_one,abs_of_nonneg hc]
    have he : (12/γ)*(γ^3/(12*P.hessianLip^2)) = (γ/P.hessianLip)^2 := by field_simp; ring
    exact le_of_eq he.symm

theorem Admissible.stopped_drift_bound {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    uniformMean (fun w : Fin M → Bool => ∑ i : Fin M, ‖actionDrift P ε
      (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)‖) ≤ 8*P.gap/(3*ε) := by
  have hb := uniformMean_mono (fun w : Fin M → Bool => Finset.sum_le_sum (fun (i : Fin M) (_ : i ∈ Finset.univ) =>
    actionDrift_charge P hε hγ _ (stoppedInspectionAction_valid_or_success hBg hBH P ε γ scaleG scaleH f F tape i.val
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ i.val))))
  simp only [← Finset.mul_sum,uniformMean_mul] at hb
  have he := h.stopped_total_decrease (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 8/(3*ε))
  exact hb.trans (by convert hm using 1; ring)

theorem Admissible.stopped_variance_bound {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH M : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    uniformMean (fun w : Fin M → Bool => ∑ i : Fin M, ‖predictableSignInnovation
      (fun i w => actionInnovationVector P γ
        (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w)) i w‖^2) ≤ 12*P.gap/γ := by
  have hb := uniformMean_mono (fun w : Fin M → Bool => Finset.sum_le_sum (fun (i : Fin M) (_ : i ∈ Finset.univ) =>
    actionInnovation_charge P hγ _ (stoppedInspectionAction_valid_or_success hBg hBH P ε γ scaleG scaleH f F tape i.val
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ i.val)) (w i)))
  simp only [← Finset.mul_sum,uniformMean_mul] at hb
  have he := h.stopped_total_decrease (M := M) hBg hBH hε hγ scaleG scaleH tape
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 12/γ)
  exact hb.trans (by convert hm using 1; ring)

end
end SampleReuse
