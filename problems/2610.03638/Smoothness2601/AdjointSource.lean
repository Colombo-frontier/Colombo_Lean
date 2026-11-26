import Smoothness2601.AdjointSolve
import Smoothness2601.AdjointCost

/-! Source accuracy choices and the adjoint sample bound with constants
independent of differencing degree, radius and target accuracy. -/
noncomputable section
namespace Smoothness2601.AdjointSource
open AdjointGeometry

theorem bias_floor_of_accuracy {μ a u : ℝ} (hμ : 0 < μ) (ha : 0 ≤ a) (hu : 0 ≤ u)
    (haμ : a ≤ μ*u/8) : 6*a ^ 2/μ ^ 2 ≤ u ^ 2/4 := by
  have hs := (sq_le_sq₀ ha (by positivity : 0 ≤ μ*u/8)).mpr haμ
  apply (div_le_iff₀ (sq_pos_of_pos hμ)).mpr
  nlinarith [sq_nonneg (μ*u)]

theorem accuracy_choices (b : Budgets) {cₐ ε : ℝ} (hcₐ : 0 < cₐ) (hε : 0 < ε)
    (hsmall : cₐ ≤ b.μ/(256*b.L₁)) :
    6*(cₐ*ε) ^ 2/b.μ ^ 2 ≤ (ε/(32*b.L₁)) ^ 2/4 := by
  have hL := b.L₁_pos
  apply bias_floor_of_accuracy b.μ_pos (mul_pos hcₐ hε).le (by positivity)
  have hh := mul_le_mul_of_nonneg_right hsmall hε.le
  exact hh.trans_eq (by ring)

def varianceConstant (b : Budgets) : ℝ :=
  8*stepsize b ^ 2*b.σ ^ 2/(1-Real.sqrt (rate b)) ^ 2

def costConstant (b : Budgets) (c : ℝ) : ℝ :=
  2*AdjointCost.iterationConstant (rate b) (radius b)*AdjointCost.scaleConstant c+
    varianceConstant b*c ^ 2

theorem costConstant_pos (b : Budgets) (hμL : b.μ ≤ b.L₁) (c : ℝ) : 0 < costConstant b c := by
  have hr := rate_range b hμL
  have hJ := AdjointCost.iterationConstant_pos hr.1 hr.2 (radius_nonneg b)
  have hS := AdjointCost.scaleConstant_pos c
  have hN : 0 ≤ varianceConstant b := by unfold varianceConstant; positivity
  unfold costConstant
  positivity

theorem sample_budget (b : Budgets) (hμL : b.μ ≤ b.L₁) (k : ℕ) {h c ε : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεc : ε ≤ c) :
    (AdjointSolve.samples b k h (ε/c) : ℝ) ≤ costConstant b c*
      ((1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2)+(2*k+2:ℕ)*Real.log (2/ε)) := by
  have hr := rate_range b hμL
  have hJ := AdjointCost.iterations_log hr.1 hr.2 (radius_nonneg b)
    (div_pos hε hc) ((div_le_one hc).mpr hεc)
  have hC := (AdjointCost.iterationConstant_pos hr.1 hr.2 (radius_nonneg b)).le
  have hscale := AdjointCost.log_scale hc hε hε1
  have hJ' := hJ.trans (mul_le_mul_of_nonneg_left hscale hC)
  have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have hS := (AdjointCost.scaleConstant_pos c).le
  have hCprod : 0 ≤ AdjointCost.iterationConstant (rate b) (radius b)*AdjointCost.scaleConstant c*
      Real.log (2/ε) := by positivity
  have hNJ : ((2*k+4:ℕ):ℝ)*(AdjointSolve.iterations b (ε/c):ℝ) ≤
      (2*AdjointCost.iterationConstant (rate b) (radius b)*AdjointCost.scaleConstant c)*
        ((2*k+2:ℕ)*Real.log (2/ε)) := by
    have hm := mul_le_mul_of_nonneg_left hJ' (by positivity : 0 ≤ ((2*k+4:ℕ):ℝ))
    change ((2*k+4:ℕ):ℝ)*(AdjointSolve.iterations b (ε/c):ℝ) ≤ _ at hm
    push_cast at hm ⊢
    nlinarith
  have he : 8*noiseTerm b ((2*k+1:ℕ)/h)/((ε/c) ^ 2*(1-Real.sqrt (rate b)) ^ 2) =
      (varianceConstant b*c ^ 2)*((1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2)) := by
    unfold noiseTerm varianceConstant
    have hs : 1-Real.sqrt (rate b) ≠ 0 :=
      (sub_pos.mpr ((Real.sqrt_lt' (by norm_num)).mpr (by simpa using hr.2))).ne'
    field_simp
    ring
  have hb := AdjointSolve.sample_budget (b := b) hμL k hh (u := ε/c)
  rw [he] at hb
  have hN : 0 ≤ varianceConstant b*c ^ 2 := by unfold varianceConstant; positivity
  have hJcoef : 0 ≤ 2*AdjointCost.iterationConstant (rate b) (radius b)*AdjointCost.scaleConstant c := by positivity
  have hA : 0 ≤ (1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2) := by positivity
  have hB : 0 ≤ (2*k+2:ℕ)*Real.log (2/ε) := mul_nonneg (by positivity) hL
  have hcross₁ := mul_nonneg hN hB
  have hcross₂ := mul_nonneg hJcoef hA
  unfold costConstant
  nlinarith

open MeasureTheory ProbabilityTheory

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [FiniteDimensional ℝ Y] {b : Budgets}
  (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

/-- The source projected adjoint claim, with all moments and bias derived
from Population and the original full-gradient oracle. -/
theorem projected_adjoint_solve {pmax : WithTop ℕ} {M Λ β cₐ ε : ℝ}
    (hμL : b.μ ≤ b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (hcₐ : 0 < cₐ) (hsmall : cₐ ≤ b.μ/(256*b.L₁))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεL : ε ≤ 32*b.L₁)
    (hreg : P.HigherRegularity pmax (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ pmax) (p : X × Y) (history : History) :
    let k := Population.stencilHalfOrder r
    let h := Population.populationRadius b M Λ β (ballRadius b) (cₐ*ε) r
    let u := ε/(32*b.L₁)
    (AdjointSolve.program P O k h u).CallsEq (fun _ => AdjointSolve.samples b k h u) ∧
    (∀ᵐ z ∂(AdjointSolve.program P O k h u).law (p,history), ‖z.1‖ ≤ ballRadius b) ∧
    Integrable (fun z => ‖z.1-target P p‖) ((AdjointSolve.program P O k h u).law (p,history)) ∧
    (∫ z, ‖z.1-target P p‖ ∂(AdjointSolve.program P O k h u).law (p,history)) ≤ u ∧
    (AdjointSolve.samples b k h u : ℝ) ≤ costConstant b (32*b.L₁)*
      ((1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2)+(2*k+2:ℕ)*Real.log (2/ε)) := by
  dsimp only
  have hL : 0 < 32*b.L₁ := mul_pos (by norm_num) b.L₁_pos
  have ha : 0 < cₐ*ε := mul_pos hcₐ hε
  have hm := AdjointSolve.population_solve P O hμL hM hΛ hβ ha (div_pos hε hL)
    (accuracy_choices b hcₐ hε hsmall) hreg r hr hrp p history
  exact ⟨AdjointSolve.program_calls P O _ _ _,AdjointSolve.program_bounded P O _ _ _ p history,
    hm.1,hm.2,sample_budget b hμL _ (Population.populationRadius_pos (ballRadius_one b) ha r)
      hL hε hε1 hεL⟩

end Smoothness2601.AdjointSource
