import Bilevel.ChiUpperTheorem
import Bilevel.CachedCurvatureRate

/-! Actual-kernel upper half of `cor:curvature-controlled`. The supplied
curvature certificate is enlarged to dominate anchor smoothness, keeping
the original-query bound independent of chi except through logarithms.
No matching minimax lower bound is asserted here. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedUpper
open Stateful CachedBudgetCalibration CachedParameterChoice

def controlledConstant (C_F : ℝ) : ℝ := max 1 (max C_F 4)

def controlledCurvature (L μ Lf Lg Λcert : ℝ) : ℝ :=
  max L (max Λcert (anchorSmoothness Lf (Lg/μ)))

def controlledLog (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) : ℝ :=
  CachedOracleCost.initializationLog μ Lg
    (initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀)
    (anchorRadius Lf Lg (Lg/μ) (bias μ Lg Cf ρ) ε)

def controlledThreeRateBound (L μ Lf Lg Cf ρ σf σg Λ C_F Δ ε R₀ : ℝ) : ℝ :=
  (100000000000000*98304)*repetitions Λ Δ ε*max 1 C_F*
    max 1 (controlledLog μ Lf Lg Cf ρ Λ Δ ε R₀)*
      (CachedCurvatureRate.deterministic L (L/μ) Δ ε+
        ChiRefinementRates.upperNoise L (L/μ) σf Δ ε+
        CachedCurvatureRate.lowerNoise L (ρ/μ) (L/μ) σg Δ ε)

theorem controlled_curvature_budget {L μ Lf Lg Λcert C_F : ℝ}
    (hL : 0≤L) (hκ : 1≤L/μ)
    (hcert : Λcert≤C_F*L*(L/μ)^2)
    (hLa : anchorSmoothness Lf (Lg/μ)≤4*L*(L/μ)^2) :
    controlledCurvature L μ Lf Lg Λcert≤controlledConstant C_F*L*(L/μ)^2 := by
  let B := L*(L/μ)^2
  let C := controlledConstant C_F
  have hB : 0≤B := by dsimp [B]; positivity
  have hC1 : 1≤C := le_max_left _ _
  have hCF : C_F≤C := (le_max_left C_F 4).trans (le_max_right 1 _)
  have hC4 : 4≤C := (le_max_right C_F 4).trans (le_max_right 1 _)
  have hLB : L≤B := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hκ (n := 2)) hL
    simpa only [mul_one] using hh
  have h1 : L≤C*B := hLB.trans (le_mul_of_one_le_left hB hC1)
  have h2 : Λcert≤C*B := by
    have hh := mul_le_mul_of_nonneg_right hCF hB
    dsimp [B] at hh ⊢
    nlinarith
  have h3 : anchorSmoothness Lf (Lg/μ)≤C*B := by
    have hh := mul_le_mul_of_nonneg_right hC4 hB
    dsimp [B] at hh ⊢
    nlinarith
  have hh := max_le h1 (max_le h2 h3)
  dsimp [controlledCurvature]
  convert hh using 1
  dsimp [B,C]
  ring

theorem rateBound_le_curvatureControlled {L μ Lf Lg Cf ρ σf σg Λ C_F Δ ε R₀ : ℝ}
    (hμ : 0<μ) (hL : 0<L) (hLf : 0≤Lf) (hLg : 0≤Lg) (hCf : 0≤Cf) (hρ : 0≤ρ)
    (hLfL : Lf≤L) (hLgL : Lg≤L) (hCfL : Cf≤L)
    (hθ : 1≤ρ/μ) (hκ : 1≤L/μ) (hΔ : 0<Δ) (hε : 0<ε)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ))) (hΛb : Λ≤C_F*L*(L/μ)^2) :
    rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ ≤
      controlledThreeRateBound L μ Lf Lg Cf ρ σf σg Λ C_F Δ ε R₀ := by
  have hθ0 : 0≤ρ/μ := div_nonneg hρ hμ.le
  have he : (ρ/μ)*μ=ρ := div_mul_cancel₀ ρ hμ.ne'
  have hp := CachedNormalizedRate.normalized_parameters hμ hL hLf hLg hCf hLfL hLgL hCfL hθ0 hκ
  rw [he] at hp
  have hE : 0≤bias μ Lg Cf ρ := by unfold bias; positivity
  have hh := CachedCurvatureRate.core_le_three_rates (C_F := C_F)
    (D := initialRadius μ Lg Cf (tilt (bias μ Lg Cf ρ) ε) Λ Δ ε R₀)
    (σf := σf) (σg := σg) hμ hL hLf hLg hE hθ hκ hΔ hε haccuracy
    (div_le_div_of_nonneg_right hLgL hμ.le) (div_le_div_of_nonneg_right hLfL hμ.le)
    hp.2.2 hΛb hp.2.1
  have hq := mul_le_mul_of_nonneg_left hh
    (by positivity : 0≤(100000000000000:ℝ)*repetitions Λ Δ ε)
  unfold rateBound controlledThreeRateBound controlledLog
  convert hq using 1
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
  (O : HistorySFO (Query := X×Y) (History := History) (X := X) (Y := Y) σf σg)

set_option maxHeartbeats 1200000 in
/-- Upper half of the curvature-controlled corollary for the concrete
original-SFO algorithm, with accuracy and both cost bounds on the same law. -/
theorem curvature_controlled_upper
    (hfx : ∀ x y,O.upper.truth_x (x,y)=P.fx x y)
    (hfy : ∀ x y,O.upper.truth_y (x,y)=P.fy x y)
    (hgy : ∀ x y,O.lower.truth_y (x,y)=P.gy x y)
    (hgx : ∀ x y,O.lower.truth_x (x,y)=P.gx x y)
    {L Λcert C_F Δ ε R₀ lower : ℝ} (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε)
    (hLfL : Lf≤L) (hLgL : Lg≤L) (hCfL : Cf≤L)
    (hθ : 1≤ρ/μ) (hκ : 1≤L/μ) (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hcert : Λcert≤C_F*L*(L/μ)^2)
    (hlip : ∀ x y,‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖≤Λcert*‖x-y‖)
    (hlower : ∀ x,lower≤P.hyperobjective P.canonicalResponse x)
    (x₀ : X) (yinit : Y) (hgap : P.hyperobjective P.canonicalResponse x₀-lower≤Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖≤R₀) (h : History) :
    let Λ := controlledCurvature L μ Lf Lg Λcert
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let ν := (algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)
    Integrable (fun z => ‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖)
      (StochasticOuter.outputLaw (outerCount Λ Δ ε) ν) ∧
    (∫ z,‖gradient (P.hyperobjective P.canonicalResponse) (output Λ Δ ε x₀ z)‖
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε) ν)≤ε ∧
    (∀ᵐ z ∂ν,(z.2.2:ℝ)≤controlledThreeRateBound L μ Lf Lg Cf ρ σf σg Λ (controlledConstant C_F) Δ ε R₀) ∧
    Integrable (fun z => (z.2.2:ℝ)) ν ∧
      (∫ z,(z.2.2:ℝ) ∂ν)≤controlledThreeRateBound L μ Lf Lg Cf ρ σf σg Λ (controlledConstant C_F) Δ ε R₀ := by
  let Λ := controlledCurvature L μ Lf Lg Λcert
  have hΛ : 0<Λ := hL.trans_le (le_max_left _ _)
  have hLaΛ : anchorSmoothness Lf (Lg/μ)≤Λ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hcertΛ : Λcert≤Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hfull (x y : X) : ‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖≤Λ*‖x-y‖ :=
    (hlip x y).trans (mul_le_mul_of_nonneg_right hcertΛ (norm_nonneg _))
  have hp := CachedNormalizedRate.normalized_parameters P.μ_pos hL P.Lf_nonneg P.Lg_nonneg
    P.Cf_nonneg hLfL hLgL hCfL (div_nonneg P.ρ_nonneg P.μ_pos.le) hκ
  have hΛb : Λ≤controlledConstant C_F*L*(L/μ)^2 :=
    controlled_curvature_budget hL.le hκ hcert hp.2.1
  have hc := general_upper P O hfx hfy hgy hgx hΛ hΔ.le hε hLaΛ hfull hlower
    x₀ yinit hgap hinit h
  have hb := rateBound_le_curvatureControlled (σf := σf) (σg := σg) (R₀ := R₀)
    P.μ_pos hL P.Lf_nonneg P.Lg_nonneg P.Cf_nonneg P.ρ_nonneg hLfL hLgL hCfL
    hθ hκ hΔ hε haccuracy hΛb
  exact ⟨hc.1,hc.2.1,hc.2.2.1.mono (fun _ hz => hz.trans hb),hc.2.2.2.1,hc.2.2.2.2.trans hb⟩

end Bilevel.CachedUpper
