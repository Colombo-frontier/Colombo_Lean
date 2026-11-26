import Bilevel.CachedOuterAccuracy
import Bilevel.CachedOuterCostBound
import Bilevel.CachedParameterAssembly

/-! Concrete cached upper algorithm and accuracy with every public tolerance,
initialization radius, repetition count, and failure budget instantiated. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedUpper
open Stateful CachedBudgetCalibration CachedParameterChoice

def bias (μ Lg Cf ρ : ℝ) : ℝ := (1+Lg/μ)*ρ*Cf^2/(2*μ^2)

def gradientCap (Λ Δ ε : ℝ) : ℝ :=
  Real.sqrt (2*Λ*Δ)+Real.sqrt (outerCount Λ Δ ε * energyCap Λ Δ ε)

def failureProbability (Λ Δ ε : ℝ) : ℝ := failureTarget (gradientCap Λ Δ ε) ε

def repetitions (Λ Δ ε : ℝ) : ℕ := confidenceCount (outerCount Λ Δ ε) (failureProbability Λ Δ ε)

instance repetitions_neZero (Λ Δ ε : ℝ) : NeZero (repetitions Λ Δ ε) :=
  ⟨(confidenceCount_pos _ _).ne'⟩

def initialRadius (μ Lg Cf t Λ Δ ε R₀ : ℝ) : ℝ :=
  R₀+Lg/μ*radiusCap Λ Δ ε+t*Cf/μ

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] [MeasurableSpace History]
  {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def algorithm (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    Procedure Unit History (CachedOuterProcedure.State X Y) :=
  let k := Lg/μ
  let E := bias μ Lg Cf ρ
  let t := tilt E ε
  CachedOuterProcedure.publicRun O μ Lg Cf t (initialRadius μ Lg Cf t Λ Δ ε R₀)
    (lowerRadius Lg E ε) (anchorRadius Lf Lg k E ε) (gradientRadius E ε) (upperRadius k ε)
    Λ (anchorSmoothness Lf k) Δ ε (repetitions Λ Δ ε) x₀ yinit

def output (Λ Δ ε : ℝ) (x₀ : X)
    (z : Fin (outerCount Λ Δ ε) × Outcome (CachedOuterProcedure.State X Y) History) : X :=
  CappedExecution.output Λ (energyCap Λ Δ ε) x₀ z.2.1.1 (outerCount Λ Δ ε) z.1

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
    let ν := (algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)
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
  have hprob : (6*outerCount Λ Δ ε:ℝ)*Real.exp (-(repetitions Λ Δ ε:ℝ)/8) ≤
      failureProbability Λ Δ ε := six_operations_budget (outerCount_pos Λ Δ ε) hβ
  have hfail : failureProbability Λ Δ ε * gradientCap Λ Δ ε ≤ ε/2 :=
    (failure_loss_budget hG).trans (by linarith)
  have hb := estimator_error_budget (Λ := Λ) (Δ := Δ) P.Lf_nonneg hLg hk hE hε
  exact CachedOuterProcedure.expected_gradient_norm P O hfx hfy hgy hgx
    (tilt (bias μ Lg Cf ρ) ε)
    (initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀)
    (lowerRadius Lg (bias μ Lg Cf ρ) ε) (anchorRadius Lf Lg (Lg/μ) (bias μ Lg Cf ρ) ε)
    (gradientRadius (bias μ Lg Cf ρ) ε) (upperRadius (Lg/μ) ε) Λ
    (refreshRadius Λ (anchorSmoothness Lf (Lg/μ)) Δ ε) ε Δ lower R₀ (failureProbability Λ Δ ε)
    ht hr hrA hδ hη hΛ hrad.le hε hΔ hlip hlower (repetitions Λ Δ ε) x₀ yinit hgap hinit
    (outerCount Λ Δ ε) (outerCount_horizon hε) le_rfl hb hprob hfail h

end Bilevel.CachedUpper
