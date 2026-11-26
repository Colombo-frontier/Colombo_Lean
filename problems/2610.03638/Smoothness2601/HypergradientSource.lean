import Smoothness2601.HypergradientSolve

/-! Equation eq:outer-error for the fully executed source estimator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.Stateful
namespace Smoothness2601.HypergradientSource
open AdjointGeometry HypergradientGeometry

def innerAccuracy (b : Budgets) (ε : ℝ) : ℝ := ε/(32*innerSensitivity b)
def adjointAccuracy (b : Budgets) (ε : ℝ) : ℝ := ε/(32*b.L₁)
def differenceRadius (b : Budgets) (M Λ β cₐ ε : ℝ) (r : ℕ) : ℝ :=
  Population.populationRadius b M Λ β (ballRadius b) (cₐ*ε) r

theorem bias_small (b : Budgets) (hμL : b.μ ≤ b.L₁) {cₐ ε : ℝ}
    (hsmall : cₐ ≤ b.μ/(256*b.L₁)) (hε : 0 ≤ ε) : cₐ*ε ≤ ε/32 := by
  have hh : b.μ/(256*b.L₁) ≤ 1/32 :=
    (div_le_iff₀ (mul_pos (by norm_num) b.L₁_pos)).mpr (by nlinarith [b.L₁_pos])
  have ht := mul_le_mul_of_nonneg_right (hsmall.trans hh) hε
  nlinarith

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def program (M Λ β cₐ : ℝ) (r : ℕ) (D ε : ℝ) : Procedure (X × Y) History X :=
  HypergradientSolve.program P O (Population.stencilHalfOrder r) (differenceRadius b M Λ β cₐ ε r)
    D (innerAccuracy b ε) (adjointAccuracy b ε) ε

def samples (b : Budgets) (M Λ β cₐ : ℝ) (r : ℕ) (D ε : ℝ) : ℕ :=
  HypergradientSolve.samples b (Population.stencilHalfOrder r) (differenceRadius b M Λ β cₐ ε r)
    D (innerAccuracy b ε) (adjointAccuracy b ε) ε

theorem program_calls (M Λ β cₐ : ℝ) (r : ℕ) (D ε : ℝ) :
    (program P O M Λ β cₐ r D ε).CallsEq (fun _ => samples b M Λ β cₐ r D ε) :=
  HypergradientSolve.program_calls P O _ _ _ _ _ _

variable [FiniteDimensional ℝ Y]

theorem program_error {pmax : WithTop ℕ} {M Λ β cₐ D ε : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (hcₐ : 0 < cₐ) (hsmall : cₐ ≤ b.μ/(256*b.L₁)) (hD : 0 ≤ D) (hε : 0 < ε)
    (hreg : P.HigherRegularity pmax (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ pmax)
    (p : X × Y) (history : History) (hinit : ‖p.2-P.yStar p.1‖ ≤ D) :
    Integrable (fun z => ‖z.1-gradient P.objective p.1‖)
      ((program P O M Λ β cₐ r D ε).law (p,history)) ∧
    (∫ z, ‖z.1-gradient P.objective p.1‖ ∂(program P O M Λ β cₐ r D ε).law (p,history)) ≤ ε/8 := by
  have ha := mul_pos hcₐ hε
  have hL := b.L₁_pos
  have hC := innerSensitivity_pos b
  have hm := HypergradientSolve.program_error P O hgap (Population.stencilHalfOrder r)
    (Population.populationRadius_pos (ballRadius_one b) ha r) ha.le hD
    (by unfold innerAccuracy; positivity : 0 < innerAccuracy b ε)
    (by unfold adjointAccuracy; positivity : 0 < adjointAccuracy b ε) hε
    (AdjointSource.accuracy_choices b hcₐ hε hsmall)
    (fun x y v hv => DifferencingOracle.populationRadius_y_bias P hM hΛ hβ (ballRadius_one b)
      ha hreg r hr hrp x y v hv)
    (fun x y v hv => DifferencingOracle.populationRadius_x_bias P hM hΛ hβ (ballRadius_one b)
      ha hreg r hr hrp x y v hv) p history hinit
  refine ⟨hm.1,hm.2.trans ?_⟩
  have he₁ : b.L₁*adjointAccuracy b ε = ε/32 := by
    unfold adjointAccuracy
    field_simp
    ring
  have he₂ : innerSensitivity b*innerAccuracy b ε = ε/32 := by
    unfold innerAccuracy
    field_simp
    ring
  rw [he₁,he₂]
  linarith [bias_small b hgap.le hsmall hε.le]

end Smoothness2601.HypergradientSource
