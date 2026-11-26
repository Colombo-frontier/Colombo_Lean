import Bilevel.CachedUpperRateTheorem
import Bilevel.CachedNormalizedRate

/-! Normalized upper theorem for the revised manuscript. Actual accuracy and
original-SFO cost concern the same fully specified history-threaded algorithm.
This file proves upper bounds only; it makes no minimax lower-bound claim. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedUpper
open Stateful CachedBudgetCalibration CachedParameterChoice

def universalCurvature (L μ Lf Lg Cf ρ : ℝ) : ℝ :=
  max L ((1+Lg/μ)^2*(Lf+ρ*Cf/μ))

def normalizedLog (L μ Lf Lg Cf ρ Δ ε R₀ : ℝ) : ℝ :=
  let E := bias μ Lg Cf ρ
  let Λ := universalCurvature L μ Lf Lg Cf ρ
  CachedOracleCost.initializationLog μ Lg
    (initialRadius μ Lg Cf (tilt E ε) Λ Δ ε R₀) (anchorRadius Lf Lg (Lg/μ) E ε)

def normalizedBound (L μ Lf Lg Cf ρ σf σg Δ ε R₀ : ℝ) : ℝ :=
  (100000000000000*16384)*repetitions (universalCurvature L μ Lf Lg Cf ρ) Δ ε *
    max 1 (normalizedLog L μ Lf Lg Cf ρ Δ ε R₀) *
      ChiRefinementRates.normalizedExpansion L (ρ/μ) (L/μ) σf σg Δ ε

def threeRateBound (L μ Lf Lg Cf ρ σf σg Δ ε R₀ : ℝ) : ℝ :=
  (100000000000000*98304)*repetitions (universalCurvature L μ Lf Lg Cf ρ) Δ ε *
    max 1 (normalizedLog L μ Lf Lg Cf ρ Δ ε R₀) *
      (ChiRefinementRates.deterministic L (ρ/μ) (L/μ) Δ ε +
        ChiRefinementRates.upperNoise L (L/μ) σf Δ ε +
        ChiRefinementRates.lowerNoise L (ρ/μ) (L/μ) σg Δ ε)

theorem rateBound_le_normalized {L μ Lf Lg Cf ρ σf σg Δ ε R₀ : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg) (hCf : 0 ≤ Cf)
    (hρ : 0 ≤ ρ) (hLfL : Lf ≤ L) (hLgL : Lg ≤ L) (hCfL : Cf ≤ L)
    (hκ : 1 ≤ L/μ) (hΔ : 0 ≤ Δ) :
    rateBound μ Lf Lg Cf ρ σf σg (universalCurvature L μ Lf Lg Cf ρ) Δ ε R₀ ≤
      normalizedBound L μ Lf Lg Cf ρ σf σg Δ ε R₀ := by
  let Λ := universalCurvature L μ Lf Lg Cf ρ
  let D := initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀
  have he : (ρ/μ)*μ = ρ := div_mul_cancel₀ ρ hμ.ne'
  have hh := CachedNormalizedRate.source_core_le_normalizedExpansion
    (θ := ρ/μ) (ε := ε) (D := D) (σf := σf) (σg := σg)
    hμ hL hLf hLg hCf hLfL hLgL hCfL (div_nonneg hρ hμ.le) hκ hΔ
  dsimp only at hh
  rw [he] at hh
  have hq := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ (100000000000000:ℝ)*repetitions Λ Δ ε)
  unfold rateBound normalizedBound normalizedLog
  convert hq using 1; dsimp [D,Λ,universalCurvature,bias,anchorSmoothness]; ring

theorem normalizedBound_le_threeRateBound {L μ Lf Lg Cf ρ σf σg Δ ε R₀ : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hθ : 1 ≤ ρ/μ) (hκ : 1 ≤ L/μ)
    (hε : 0 < ε) (haccuracy : ε ≤ min L (Real.sqrt (L*Δ))) :
    normalizedBound L μ Lf Lg Cf ρ σf σg Δ ε R₀ ≤
      threeRateBound L μ Lf Lg Cf ρ σf σg Δ ε R₀ := by
  have hh := ChiRefinementRates.normalizedExpansion_le_six_rates_of_accuracy
    (σf := σf) (σg := σg) hL hΔ hθ hκ hε haccuracy
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ (100000000000000*16384:ℝ)*
      repetitions (universalCurvature L μ Lf Lg Cf ρ) Δ ε *
      max 1 (normalizedLog L μ Lf Lg Cf ρ Δ ε R₀))
  unfold normalizedBound threeRateBound
  convert hm using 1
  ring

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] [MeasurableSpace History]
  [FiniteDimensional ℝ Y] [Nontrivial Y] {σf σg μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

set_option maxHeartbeats 1200000 in
theorem normalized_upper
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    {L Δ ε R₀ lower : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hLfL : Lf ≤ L) (hLgL : Lg ≤ L) (hCfL : Cf ≤ L) (hκ : 1 ≤ L/μ)
    (hlower : ∀ x, lower ≤ P.hyperobjective P.canonicalResponse x)
    (x₀ : X) (yinit : Y) (hgap : P.hyperobjective P.canonicalResponse x₀-lower ≤ Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀) (h : History) :
    let Λ := universalCurvature L μ Lf Lg Cf ρ
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let ν := (algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)
    Integrable (fun z => ‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖)
      (StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ∧
    (∫ z, ‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ≤ ε ∧
    (∀ᵐ z ∂ν, (z.2.2:ℝ) ≤ normalizedBound L μ Lf Lg Cf ρ σf σg Δ ε R₀) ∧
    Integrable (fun z => (z.2.2:ℝ)) ν ∧
      (∫ z, (z.2.2:ℝ) ∂ν) ≤ normalizedBound L μ Lf Lg Cf ρ σf σg Δ ε R₀ := by
  let Λ := universalCurvature L μ Lf Lg Cf ρ
  have hΛ : 0 < Λ := hL.trans_le (le_max_left _ _)
  have hcurv : (1+Lg/μ)^2*(Lf+ρ*Cf/μ) ≤ Λ := le_max_right _ _
  have hLaΛ : anchorSmoothness Lf (Lg/μ) ≤ Λ := by
    have hh : 0 ≤ (1+Lg/μ)^2*(ρ*Cf/μ) := by
      exact mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg P.ρ_nonneg P.Cf_nonneg) P.μ_pos.le)
    unfold anchorSmoothness
    nlinarith
  have hlip (x y : X) : ‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖ ≤ Λ*‖x-y‖ :=
    (P.gradient_hyperobjective_norm_sub_le P.canonicalResponse x y).trans
      (mul_le_mul_of_nonneg_right hcurv (norm_nonneg _))
  have hc := general_upper P O hfx hfy hgy hgx hΛ hΔ hε hLaΛ hlip hlower x₀ yinit hgap hinit h
  have hb := rateBound_le_normalized (σf := σf) (σg := σg) (ε := ε) (R₀ := R₀)
    P.μ_pos hL P.Lf_nonneg P.Lg_nonneg P.Cf_nonneg P.ρ_nonneg hLfL hLgL hCfL hκ hΔ
  exact ⟨hc.1,hc.2.1,hc.2.2.1.mono (fun _ hz => hz.trans hb),hc.2.2.2.1,hc.2.2.2.2.trans hb⟩

set_option maxHeartbeats 1200000 in
/-- Upper half of the manuscript's D+U+G comparison, with both logarithms
explicit. No upper restriction on variation is required for this upper half. -/
theorem three_term_upper
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    {L Δ ε R₀ lower : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hLfL : Lf ≤ L) (hLgL : Lg ≤ L) (hCfL : Cf ≤ L)
    (hθ : 1 ≤ ρ/μ) (hκ : 1 ≤ L/μ) (haccuracy : ε ≤ min L (Real.sqrt (L*Δ)))
    (hlower : ∀ x, lower ≤ P.hyperobjective P.canonicalResponse x)
    (x₀ : X) (yinit : Y) (hgap : P.hyperobjective P.canonicalResponse x₀-lower ≤ Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀) (h : History) :
    let Λ := universalCurvature L μ Lf Lg Cf ρ
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let ν := (algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)
    Integrable (fun z => ‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖)
      (StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ∧
    (∫ z, ‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ≤ ε ∧
    (∀ᵐ z ∂ν, (z.2.2:ℝ) ≤ threeRateBound L μ Lf Lg Cf ρ σf σg Δ ε R₀) ∧
    Integrable (fun z => (z.2.2:ℝ)) ν ∧
      (∫ z, (z.2.2:ℝ) ∂ν) ≤ threeRateBound L μ Lf Lg Cf ρ σf σg Δ ε R₀ := by
  have hc := normalized_upper P O hfx hfy hgy hgx hL hΔ.le hε hLfL hLgL hCfL hκ
    hlower x₀ yinit hgap hinit h
  have hb := normalizedBound_le_threeRateBound (Lf := Lf) (Lg := Lg) (Cf := Cf)
    (σf := σf) (σg := σg) (R₀ := R₀) hL hΔ hθ hκ hε haccuracy
  exact ⟨hc.1,hc.2.1,hc.2.2.1.mono (fun _ hz => hz.trans hb),hc.2.2.2.1,hc.2.2.2.2.trans hb⟩

end Bilevel.CachedUpper
