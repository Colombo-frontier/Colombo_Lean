import SampleReuse.CurvatureFirstExecution

open MeasureTheory SecondOrder
open scoped InnerProductSpace Classical

namespace SampleReuse
noncomputable section

def inspectionHessian {Ω : Type*} {d T Bg BH : ℕ} (hBH : 0 < BH)
    (P : Parameters) (scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ) (s : OptimizerCache d) :=
  checkpointValue t s.2.2.2
    (checkpointPacket hBH scaleH P.hessianNoise P.hessianLip (fun z => hessian (F z))
      (hessianReserve T Bg BH) t s.2.2.2 s.1 tape)

def inspectionGradient {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg)
    (P : Parameters) (scaleG : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (s : OptimizerCache d) :=
  checkpointValue s.2.1 s.2.2.1
    (checkpointPacket hBg scaleG P.gradientNoise P.gradientLip (fun z => gradient (F z))
      (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1 tape)

def ValidInspection {d : ℕ} (f : Point d → ℝ) (ε γ : ℝ) (x : Point d) :
    CurvatureFirstAction d → Prop
  | .success => IsSOSP f ε γ x
  | .gradient g => ‖g-gradient f x‖ ≤ ε/4 ∧ 3*ε/4 < ‖g‖
  | .curvature v => ‖v‖ = 1 ∧ ⟪hessian f x v,v⟫_ℝ ≤ -γ/2

/-- Every branch is justified by the actual cached numerical estimates.
The gradient accuracy requirement is confined to gradient-checkpoint branches. -/
theorem curvatureFirstInspect_valid {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ) (s : OptimizerCache d)
    (hH : ‖inspectionHessian hBH P scaleH F tape t s-hessian f s.1‖ ≤ γ/4)
    (hG : sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s) = .certificate →
      ‖inspectionGradient hBg P scaleG F tape s-gradient f s.1‖ ≤ ε/4) :
    ValidInspection f ε γ s.1
      (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).action := by
  have hv := sourceCurvatureSelector_valid (3*γ/4) (inspectionHessian hBH P scaleH F tape t s)
  cases hs : sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s) with
  | certificate =>
    rw [hs] at hv
    have he := hG hs
    simp only [inspectionHessian] at hs
    simp only [curvatureFirstInspect, hs,
      curvatureTag, Bool.false_eq_true, if_false]
    split_ifs with hg
    · exact stopping_certificate hg he hv hH
    · exact ⟨he, lt_of_not_ge hg⟩
  | negative v =>
    rw [hs] at hv
    simp only [inspectionHessian] at hs
    simp only [curvatureFirstInspect, hs,
      curvatureTag, curvatureVector, if_true]
    exact ⟨hv.1, accurate_source_curvature hH hv.1 hv.2⟩

def inspectionNextPoint {d : ℕ} (P : Parameters) (ε γ : ℝ) (x : Point d)
    (a : CurvatureFirstAction d) (b : Bool) : Point d :=
  match a with
  | .success => x
  | .gradient g => gradientMove P ε x g
  | .curvature v => curvatureNext (γ/P.hessianLip) x v b

def inspectionDecrease {d : ℕ} (P : Parameters) (ε γ : ℝ) : CurvatureFirstAction d → ℝ
  | .success => 0
  | .gradient _ => 3*ε^2/(32*P.gradientLip)
  | .curvature _ => γ^3/(12*P.hessianLip^2)

/-- Conditional expected descent at an actual valid inspection. The fair sign
is sampled after inspection; no pointwise descent of both signs is assumed. -/
theorem Admissible.inspection_descent {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ)
    (x : Point d) (a : CurvatureFirstAction d) (hv : ValidInspection f ε γ x a) :
    (∫ b, f (inspectionNextPoint P ε γ x a b) ∂(PMF.uniformOfFintype Bool).toMeasure)-f x ≤
      -inspectionDecrease P ε γ a := by
  cases a with
  | success => simp only [inspectionNextPoint, inspectionDecrease, integral_const,
      measureReal_univ_eq_one, one_smul, sub_self, neg_zero, le_refl]
  | gradient g =>
    simpa only [inspectionNextPoint, inspectionDecrease, integral_const,
      measureReal_univ_eq_one, one_smul] using h.normalized_gradient_descent x g hε hv.1 hv.2
  | curvature v => exact h.signed_curvature_descent x v hγ hv.1 hv.2

end
end SampleReuse
