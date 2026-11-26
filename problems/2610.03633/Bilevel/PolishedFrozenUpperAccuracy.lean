import Bilevel.PolishedFrozenAccuracy
import Bilevel.CachedUpperAccuracy

/-! Calibrated expected accuracy of the literal five-operation frozen-tilt
procedure. All original SFO conditional laws retain their full history. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenUpper
open Stateful CachedBudgetCalibration CachedParameterChoice CachedUpper

variable {X Y : Type} {History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] [MeasurableSpace History]
  {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  [FiniteDimensional ℝ Y] [Nontrivial Y]

set_option maxHeartbeats 1600000 in
theorem accuracy
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    {Λ Δ ε R₀ lower : ℝ} (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hlip : ∀ x y, ‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖ ≤ Λ*‖x-y‖)
    (hlower : ∀ x, lower ≤ P.hyperobjective P.canonicalResponse x)
    (x₀ : X) (yinit : Y) (hgap : P.hyperobjective P.canonicalResponse x₀-lower ≤ Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀) (h : History) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let ν := (PolishedFrozenProcedure.algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)
    Integrable (fun z => ‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖)
      (StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ∧
    (∫ z, ‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ≤ ε := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have hk : 0 ≤ Lg/μ := div_nonneg P.Lg_nonneg P.μ_pos.le
  have hLg : 0 < Lg := P.μ_pos.trans_le P.strong_convexity_le_smoothness
  have hE : 0 ≤ bias μ Lg Cf ρ := by
    unfold bias
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) P.ρ_nonneg) (sq_nonneg Cf))
      (mul_nonneg (by norm_num) (sq_nonneg μ))
  have ht := tilt_pos hE hε
  have hr := lowerRadius_pos hLg hE hε
  have hrA := anchorRadius_pos P.Lf_nonneg hLg hk hE hε
  have hδ := gradientRadius_pos hE hε
  have hη := upperRadius_pos hk hε
  have hrad := refreshRadius_pos (La := anchorSmoothness Lf (Lg/μ)) hΛ
    (anchorSmoothness_nonneg P.Lf_nonneg) hΔ hε
  have hG : 0 < gradientCap Λ Δ ε := gradient_cap_pos hΛ hΔ hε
  have hβ : 0 < failureProbability Λ Δ ε := failureTarget_pos hG hε
  have hprob : (5*outerCount Λ Δ ε:ℝ)*Real.exp (-(repetitions Λ Δ ε:ℝ)/8) ≤
      failureProbability Λ Δ ε := by
    have hh := six_operations_budget (outerCount_pos Λ Δ ε) hβ
    have he : 0≤Real.exp (-(repetitions Λ Δ ε:ℝ)/8) := (Real.exp_pos _).le
    have hn : (0:ℝ)≤outerCount Λ Δ ε := Nat.cast_nonneg _
    dsimp only [repetitions] at *
    nlinarith
  have hfail : failureProbability Λ Δ ε * gradientCap Λ Δ ε ≤ ε/2 :=
    (failure_loss_budget hG).trans (by linarith)
  have hb := estimator_error_budget (Λ := Λ) (Δ := Δ) P.Lf_nonneg hLg hk hE hε
  exact PolishedFrozenProcedure.expected_gradient_norm P O hfx hfy hgy hgx
    (tilt (bias μ Lg Cf ρ) ε)
    (initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀)
    (lowerRadius Lg (bias μ Lg Cf ρ) ε) (anchorRadius Lf Lg (Lg/μ) (bias μ Lg Cf ρ) ε)
    (gradientRadius (bias μ Lg Cf ρ) ε) (upperRadius (Lg/μ) ε) Λ
    (refreshRadius Λ (anchorSmoothness Lf (Lg/μ)) Δ ε) ε Δ lower R₀ (failureProbability Λ Δ ε)
    ht hr hrA (anchorRadius_le_lower Lf Lg (Lg/μ) (bias μ Lg Cf ρ) ε) hδ hη hΛ hrad.le hε hΔ hlip hlower (repetitions Λ Δ ε) x₀ yinit hgap hinit
    (outerCount Λ Δ ε) (outerCount_horizon hε) le_rfl hb hprob hfail h

end Bilevel.PolishedFrozenUpper
