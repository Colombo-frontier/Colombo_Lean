import Bilevel.CachedUpperAccuracy

/-! The same concrete cached algorithm has expected epsilon-stationarity,
an almost-sure original-query bound, and the corresponding expected bound.
The large-accuracy threshold is implemented separately by a zero-call kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedUpper
open Stateful CachedBudgetCalibration CachedParameterChoice

def cost (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) : ℝ :=
  let k := Lg/μ
  let E := bias μ Lg Cf ρ
  let t := tilt E ε
  CachedOuterProcedure.publicCost μ Lg σf σg (initialRadius μ Lg Cf t Λ Δ ε R₀)
    (lowerRadius Lg E ε) (anchorRadius Lf Lg k E ε) (gradientRadius E ε) (upperRadius k ε)
    Λ (anchorSmoothness Lf k) Δ ε (repetitions Λ Δ ε)

def returnInitial {X History : Type*} [MeasurableSpace X] [MeasurableSpace History]
    (x₀ : X) : Procedure Unit History X := Procedure.pure (fun _ => x₀) measurable_const

theorem returnInitial_calls {X History : Type*} [MeasurableSpace X] [MeasurableSpace History]
    (x₀ : X) : (returnInitial (History := History) x₀).CallsEq (fun _ => 0) :=
  Procedure.calls_pure _ _

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
theorem correctness_and_calls
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    {Λ Δ ε R₀ lower : ℝ} (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hLaΛ : anchorSmoothness Lf (Lg/μ) ≤ Λ)
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
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ≤ ε ∧
    (∀ᵐ z ∂ν, (z.2.2:ℝ) ≤ cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) ∧
    Integrable (fun z => (z.2.2:ℝ)) ν ∧
      (∫ z, (z.2.2:ℝ) ∂ν) ≤ cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have ha := accuracy O P hfx hfy hgy hgx hΛ hΔ hε hlip hlower x₀ yinit hgap hinit h
  have hb := CachedOuterProcedure.publicRun_calls_bound O μ Lg Cf (tilt (bias μ Lg Cf ρ) ε)
    (initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀)
    (lowerRadius Lg (bias μ Lg Cf ρ) ε) (anchorRadius Lf Lg (Lg/μ) (bias μ Lg Cf ρ) ε)
    (gradientRadius (bias μ Lg Cf ρ) ε) (upperRadius (Lg/μ) ε)
    Λ (anchorSmoothness Lf (Lg/μ)) Δ ε (repetitions Λ Δ ε)
    hΛ (anchorSmoothness_nonneg P.Lf_nonneg) hLaΛ hΔ hε x₀ yinit h
  have hc := CachedOuterProcedure.publicRun_costBound O μ Lg Cf (tilt (bias μ Lg Cf ρ) ε)
    (initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀)
    (lowerRadius Lg (bias μ Lg Cf ρ) ε) (anchorRadius Lf Lg (Lg/μ) (bias μ Lg Cf ρ) ε)
    (gradientRadius (bias μ Lg Cf ρ) ε) (upperRadius (Lg/μ) ε)
    Λ (anchorSmoothness Lf (Lg/μ)) Δ ε (repetitions Λ Δ ε)
    hΛ (anchorSmoothness_nonneg P.Lf_nonneg) hLaΛ hΔ hε x₀ yinit () h
  exact ⟨ha.1,ha.2,hb,hc.1,hc.2⟩

omit [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] [Nontrivial Y] in
/-- The source's `epsilon² >= 2 Lambda Delta` branch uses no oracle calls. -/
theorem zero_query_accuracy {Λ Δ ε lower : ℝ} (hΛ : 0 < Λ) (hε : 0 ≤ ε)
    (hlip : ∀ x y, ‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖ ≤ Λ*‖x-y‖)
    (hlower : ∀ x, lower ≤ P.hyperobjective P.canonicalResponse x)
    (x₀ : X) (hgap : P.hyperobjective P.canonicalResponse x₀-lower ≤ Δ)
    (hlarge : 2*Λ*Δ ≤ ε^2) (h : History) :
    Integrable (fun z => ‖gradient (P.hyperobjective P.canonicalResponse) z.1‖)
      ((returnInitial x₀).law ((),h)) ∧
    (∫ z, ‖gradient (P.hyperobjective P.canonicalResponse) z.1‖
      ∂(returnInitial x₀).law ((),h)) ≤ ε ∧
    (returnInitial (History := History) x₀).CallsEq (fun _ => 0) := by
  have hgrad (x : X) : HasGradientAt (P.hyperobjective P.canonicalResponse)
      (gradient (P.hyperobjective P.canonicalResponse) x) x := by
    rw [P.gradient_hyperobjective P.canonicalResponse x]
    exact P.hasGradient_hyperobjective P.canonicalResponse x
  have hnorm := Descent.zero_query_threshold (P.hyperobjective P.canonicalResponse) x₀
    (gradient (P.hyperobjective P.canonicalResponse) x₀) Λ lower ε hΛ hε
    (InnerContraction.smooth_upper_model _ _ _ hgrad hlip x₀) hlower
    (hgap.trans ((le_div_iff₀ (by positivity : 0 < 2*Λ)).mpr (by nlinarith)))
  have hm : StronglyMeasurable (fun z : Outcome X History =>
      ‖gradient (P.hyperobjective P.canonicalResponse) z.1‖) :=
    (((P.gradient_hyperobjective_lipschitz P.canonicalResponse).continuous.measurable.comp measurable_fst).norm).stronglyMeasurable
  refine ⟨?_,?_,returnInitial_calls x₀⟩
  · rw [returnInitial,Procedure.pure_law]
    exact integrable_dirac' hm
  · rw [returnInitial,Procedure.pure_law,integral_dirac' _ _ hm]
    exact hnorm

end Bilevel.CachedUpper
