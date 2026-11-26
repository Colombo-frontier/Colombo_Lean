import SampleReuse.CurvatureFirstFinite
import SecondOrder.FiniteCandidate

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def optimizerMinDecrease (P : Parameters) (ε γ : ℝ) : ℝ :=
  min (3*ε^2/(32*P.gradientLip)) (γ^3/(12*P.hessianLip^2))

theorem optimizerMinDecrease_pos (P : Parameters) {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    0 < optimizerMinDecrease P ε γ := by
  unfold optimizerMinDecrease
  have hL1 := P.gradientLip_pos
  have hL2 := P.hessianLip_pos
  exact lt_min (by positivity) (by positivity)

theorem CurvatureShadowResult.work_nonneg {d : ℕ} (P : Parameters) {ε γ : ℝ}
    (hγ : 0 ≤ γ) (r : CurvatureShadowResult d) : 0 ≤ r.work P ε γ := by
  unfold work
  have hL1 := P.gradientLip_pos
  have hL2 := P.hessianLip_pos
  positivity

theorem CurvatureShadowResult.work_lower {d : ℕ} (P : Parameters) (ε γ : ℝ)
    (r : CurvatureShadowResult d) :
    optimizerMinDecrease P ε γ * (r.gradientSteps+r.curvatureSteps) ≤ r.work P ε γ := by
  unfold optimizerMinDecrease work
  have hg := mul_le_mul_of_nonneg_right (min_le_left (3*ε^2/(32*P.gradientLip))
    (γ^3/(12*P.hessianLip^2))) (Nat.cast_nonneg r.gradientSteps : (0:ℝ) ≤ r.gradientSteps)
  have hh := mul_le_mul_of_nonneg_right (min_le_right (3*ε^2/(32*P.gradientLip))
    (γ^3/(12*P.hessianLip^2))) (Nat.cast_nonneg r.curvatureSteps : (0:ℝ) ≤ r.curvatureSteps)
  linarith

/-- Valid execution can exhaust the finite iteration horizon only if it has
paid for that many descent steps. The probability is over actual independent
private signs, uniformly for every persistent oracle table. -/
theorem Admissible.curvatureFirst_valid_exhaustion {Ω : Type*} [MeasurableSpace Ω] {d T Bg BH : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) {m : ℕ} (hm : 0 < m) :
    (PMF.uniformOfFintype (Fin m → Bool)).toMeasure.real {bits |
      curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m 0 (optimizerInitial x₀) bits ∧
      curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape m 0 (optimizerInitial x₀) bits = none} ≤
        P.gap/(optimizerMinDecrease P ε γ*m) := by
  let cost (bits : Fin m → Bool) :=
    (curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m 0 (optimizerInitial x₀) bits).work P ε γ
  have hden : 0 < optimizerMinDecrease P ε γ*m :=
    mul_pos (optimizerMinDecrease_pos P hε hγ) (Nat.cast_pos.mpr hm)
  rw [uniform_probability_indicator]
  have hb := uniformMean_mono (fun bits : Fin m → Bool => show
      (@ite ℝ (curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m 0 (optimizerInitial x₀) bits ∧
        curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape m 0 (optimizerInitial x₀) bits = none)
      (Classical.propDecidable _) 1 0) ≤ (optimizerMinDecrease P ε γ*m)⁻¹*cost bits from by
    split_ifs with he
    · have hc := curvatureFirstShadow_counts_of_exhausted hBg hBH P ε γ scaleG scaleH f F tape
        m 0 (optimizerInitial x₀) bits he.1 he.2
      have hl := CurvatureShadowResult.work_lower P ε γ
        (curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m 0 (optimizerInitial x₀) bits)
      have hcast := congrArg (fun n : ℕ => (n:ℝ)) hc
      simp only [Nat.cast_add] at hcast
      rw [hcast] at hl
      have hh := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hden.le)
      simpa only [inv_mul_cancel₀ hden.ne'] using hh
    · exact mul_nonneg (inv_nonneg.mpr hden.le) (CurvatureShadowResult.work_nonneg P hγ.le _))
  rw [uniformMean_mul] at hb
  have hw := h.curvatureFirstShadow_work hBg hBH hε hγ scaleG scaleH tape m
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hden.le))
  simpa only [Set.mem_setOf_eq,div_eq_mul_inv,mul_comm] using hfinal

end
end SampleReuse
