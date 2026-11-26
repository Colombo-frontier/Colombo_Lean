import Bilevel.CachedUpperTheorem
import Bilevel.CachedCostRate

/-! Source general cached upper rate for the same concrete verified kernel.
Both logarithmic factors are explicit: the confidence repetition count and
the initialization logarithm appearing only in the accelerated deterministic
term of `CachedCostRate.core`. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedUpper
open Stateful CachedBudgetCalibration CachedParameterChoice

def rateBound (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) : ℝ :=
  100000000000000 * repetitions Λ Δ ε *
    CachedCostRate.core μ Lf Lg (bias μ Lg Cf ρ) Λ (anchorSmoothness Lf (Lg/μ)) Δ ε
      (initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀) σf σg

theorem cost_le_rateBound {μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ}
    (hμ : 0 < μ) (hμg : μ ≤ Lg) (hLf : 0 ≤ Lf) (hρ : 0 ≤ ρ)
    (hΛ : 0 < Λ) (hLaΛ : anchorSmoothness Lf (Lg/μ) ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ ≤ rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  have hk : 0 ≤ Lg/μ := div_nonneg (hμ.le.trans hμg) hμ.le
  have hE : 0 ≤ bias μ Lg Cf ρ := by
    unfold bias
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hρ) (sq_nonneg Cf))
      (mul_nonneg (by norm_num) (sq_nonneg μ))
  exact CachedCostRate.publicCost_le_core hμ hμg hLf hE hΛ
    (anchorSmoothness_nonneg hLf) hLaΛ hΔ hε (repetitions Λ Δ ε)

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
/-- The revised general cached upper bound: actual accuracy and both query
guarantees refer to the same fully specified original-SFO algorithm. -/
theorem general_upper
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
    (∀ᵐ z ∂ν, (z.2.2:ℝ) ≤ rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) ∧
    Integrable (fun z => (z.2.2:ℝ)) ν ∧
      (∫ z, (z.2.2:ℝ) ∂ν) ≤ rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have hc := correctness_and_calls P O hfx hfy hgy hgx hΛ hΔ hε hLaΛ hlip hlower
    x₀ yinit hgap hinit h
  have hb := cost_le_rateBound (Cf := Cf) (σf := σf) (σg := σg) (R₀ := R₀)
    P.μ_pos P.strong_convexity_le_smoothness P.Lf_nonneg P.ρ_nonneg hΛ hLaΛ hΔ hε
  exact ⟨hc.1,hc.2.1,hc.2.2.1.mono (fun _ hz => hz.trans hb),hc.2.2.2.1,hc.2.2.2.2.trans hb⟩

end Bilevel.CachedUpper
