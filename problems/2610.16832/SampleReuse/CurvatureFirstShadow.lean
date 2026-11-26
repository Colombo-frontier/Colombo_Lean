import SampleReuse.CurvatureFirstValidity
import SecondOrder.FiniteMean

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem uniformMean_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (X : (Fin (m+1) → Bool) → E) :
    uniformMean X = uniformMean (fun b : Bool =>
      uniformMean (fun tail : Fin m → Bool => X (Fin.cons b tail))) := by
  rw [← uniformMean_equiv (Fin.consEquiv (fun _ => Bool)) X, uniformMean_prod]
  rfl

structure CurvatureShadowResult (d : ℕ) where
  point : Point d
  gradientSteps : ℕ
  curvatureSteps : ℕ

def CurvatureShadowResult.stop {d : ℕ} (x : Point d) : CurvatureShadowResult d := ⟨x,0,0⟩

def CurvatureShadowResult.addAction {d : ℕ} (a : CurvatureFirstAction d)
    (r : CurvatureShadowResult d) : CurvatureShadowResult d :=
  match a with
  | .success => r
  | .gradient _ => ⟨r.point,r.gradientSteps+1,r.curvatureSteps⟩
  | .curvature _ => ⟨r.point,r.gradientSteps,r.curvatureSteps+1⟩

def CurvatureShadowResult.work {d : ℕ} (P : Parameters) (ε γ : ℝ)
    (r : CurvatureShadowResult d) : ℝ :=
  (3*ε^2/(32*P.gradientLip))*r.gradientSteps +
    (γ^3/(12*P.hessianLip^2))*r.curvatureSteps

theorem CurvatureShadowResult.work_addAction {d : ℕ} (P : Parameters) (ε γ : ℝ)
    (a : CurvatureFirstAction d) (r : CurvatureShadowResult d) :
    (r.addAction a).work P ε γ = r.work P ε γ + inspectionDecrease P ε γ a := by
  cases a <;> simp only [addAction, work, inspectionDecrease, Nat.cast_add, Nat.cast_one] <;> ring

theorem CurvatureShadowResult.point_addAction {d : ℕ} (a : CurvatureFirstAction d)
    (r : CurvatureShadowResult d) : (r.addAction a).point = r.point := by cases a <;> rfl

/-- Analysis process stopped on the first invalid inspection. This predicate
uses the true population derivatives and is not an extra oracle capability of
the executable controller. Every accepted inspection is an actual controller
inspection of its immutable sample tape. -/
def curvatureFirstShadow {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    (m : ℕ) → ℕ → OptimizerCache d → (Fin m → Bool) → CurvatureShadowResult d
  | 0, _, s, _ => .stop s.1
  | m+1, t, s, signs =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    if ValidInspection f ε γ s.1 r.action then
      match r.action with
      | .success => .stop s.1
      | .gradient g => (curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m (t+1)
          (gradientMove P ε s.1 g, r.cache.2) (Fin.tail signs)).addAction (.gradient g)
      | .curvature v => (curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m (t+1)
          (curvatureNext (γ/P.hessianLip) s.1 v (signs 0), r.cache.2)
          (Fin.tail signs)).addAction (.curvature v)
    else .stop s.1

theorem Admissible.curvatureFirstShadow_energy {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (m t : ℕ) (s : OptimizerCache d) :
    uniformMean (fun signs =>
      let r := curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m t s signs
      f r.point + r.work P ε γ) ≤ f s.1 := by
  induction m generalizing t s with
  | zero => simp [curvatureFirstShadow, CurvatureShadowResult.stop, CurvatureShadowResult.work]
  | succ m ih =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    by_cases hv : ValidInspection f ε γ s.1 r.action
    · have hd := h.inspection_descent hε hγ s.1 r.action hv
      rw [PMF.integral_eq_sum] at hd
      change uniformMean (fun b => f (inspectionNextPoint P ε γ s.1 r.action b)) - f s.1 ≤
        -inspectionDecrease P ε γ r.action at hd
      rw [uniformMean_cons]
      simp only [curvatureFirstShadow, show curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s = r from rfl,
        if_pos hv, Fin.tail_cons, Fin.cons_zero]
      cases ha : r.action with
      | success =>
        simp [CurvatureShadowResult.stop, CurvatureShadowResult.work]
      | gradient g =>
        simp only [CurvatureShadowResult.point_addAction, CurvatureShadowResult.work_addAction,
          ← add_assoc, uniformMean_add, uniformMean_const]
        have hi := ih (t+1) (gradientMove P ε s.1 g,r.cache.2)
        simp only [uniformMean_add] at hi
        simp only [ha, inspectionNextPoint, inspectionDecrease, uniformMean_const] at hd
        simp only [inspectionDecrease]
        linarith
      | curvature v =>
        simp only [CurvatureShadowResult.point_addAction, CurvatureShadowResult.work_addAction,
          ← add_assoc, uniformMean_add, uniformMean_const]
        have hi := uniformMean_mono (fun b : Bool =>
          ih (t+1) (curvatureNext (γ/P.hessianLip) s.1 v b,r.cache.2))
        simp only [uniformMean_add] at hi
        simp only [ha, inspectionNextPoint] at hd
        linarith
    · simp only [curvatureFirstShadow, show curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s = r from rfl,
        if_neg hv, CurvatureShadowResult.stop, CurvatureShadowResult.work,
        Nat.cast_zero, mul_zero, add_zero, uniformMean_const, le_refl]

/-- Weighted expected counts of actual valid steps are bounded by the model
gap, uniformly in the persistent sample tape. Independence is used only for
the private fair signs, through the finite product mean. -/
theorem Admissible.curvatureFirstShadow_work {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (m : ℕ) :
    uniformMean (fun signs =>
      (curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m 0 (optimizerInitial x₀) signs).work P ε γ) ≤ P.gap := by
  have he := h.curvatureFirstShadow_energy hBg hBH hε hγ scaleG scaleH tape m 0 (optimizerInitial x₀)
  rw [uniformMean_add] at he
  have hl := uniformMean_mono (fun signs : Fin m → Bool =>
    sub_le_iff_le_add.mp (h.gap_bound
      (curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m 0 (optimizerInitial x₀) signs).point))
  rw [uniformMean_const, uniformMean_add, uniformMean_const] at hl
  change _ ≤ f x₀ at he
  linarith

end
end SampleReuse
