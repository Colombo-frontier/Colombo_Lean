import Smoothness2601.HypergradientKernels
import Smoothness2601.InnerSource
import Smoothness2601.AdjointSource

/-! The complete source hypergradient estimator as one actual history-threaded
kernel: restart inner SGD, projected adjoint solve, fresh final direction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.Stateful
namespace Smoothness2601.HypergradientSolve
open AdjointGeometry HypergradientGeometry HypergradientKernels

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

/-- The initial y is an explicit program input, rather than a fixed constant
chosen after the population; x remains frozen throughout this inner run. -/
def inner (D u : ℝ) : Procedure (X × Y) History Y :=
  InnerSolve.scheduled (InnerOracle.blockY P O true) (fun z => (z.1.1,z.2)) (by fun_prop)
    Prod.snd measurable_snd (InnerGeometry.stepsize b) (InnerGeometry.rate b) D u

def adjointThenDirection (k : ℕ) (h u ε : ℝ) : Procedure (X × Y) History X :=
  (AdjointSolve.program P O k h u).bind
    (direction P O k h (outputBatch b ((2*k+1:ℕ)/h) ε))

def afterInner (k : ℕ) (h u ε : ℝ) : Procedure ((X × Y) × Y) History X :=
  (adjointThenDirection P O k h u ε).reparam (fun z => (z.1.1,z.2)) (by fun_prop)

def program (k : ℕ) (h D uy uv ε : ℝ) : Procedure (X × Y) History X :=
  (inner P O D uy).bind (afterInner P O k h uv ε)

def samples (b : Budgets) (k : ℕ) (h D uy uv ε : ℝ) : ℕ :=
  InnerPopulation.samples b D uy+AdjointSolve.samples b k h uv+
    AdjointSolve.stepSamples k h (outputBatch b ((2*k+1:ℕ)/h) ε)

theorem inner_calls (D u : ℝ) :
    (inner P O D u).CallsEq (fun _ => InnerPopulation.samples b D u) :=
  InnerSolve.scheduled_calls _ _ _ _ _ _ _ _ _

theorem adjointThenDirection_calls (k : ℕ) (h u ε : ℝ) :
    (adjointThenDirection P O k h u ε).CallsEq (fun _ => AdjointSolve.samples b k h u+
      AdjointSolve.stepSamples k h (outputBatch b ((2*k+1:ℕ)/h) ε)) :=
  Procedure.CallsEq.bind _ _ _ _ (AdjointSolve.program_calls P O k h u) (direction_calls P O k h _)

theorem program_calls (k : ℕ) (h D uy uv ε : ℝ) :
    (program P O k h D uy uv ε).CallsEq (fun _ => samples b k h D uy uv ε) := by
  have hp := Procedure.CallsEq.reparam _ _ (adjointThenDirection_calls P O k h uv ε)
    (fun z : (X × Y) × Y => (z.1.1,z.2)) (by fun_prop)
  simpa only [samples,Nat.add_assoc] using Procedure.CallsEq.bind _ _ _ _ (inner_calls P O D uy) hp

variable [FiniteDimensional ℝ Y]

theorem inner_expected_norm (hgap : b.μ < b.L₁) {D u : ℝ} (hD : 0 ≤ D) (hu : 0 < u)
    (p : X × Y) (history : History) (hinit : ‖p.2-P.yStar p.1‖ ≤ D) :
    Integrable (fun z => ‖z.1-P.yStar p.1‖) ((inner P O D u).law (p,history)) ∧
    (∫ z, ‖z.1-P.yStar p.1‖ ∂(inner P O D u).law (p,history)) ≤ u := by
  have hr := InnerGeometry.rate_range b hgap
  apply InnerSolve.scheduled_norm _ _ _ _ _ (InnerGeometry.stepsize_pos b).ne'
    hr.1 hr.2 hD hu (fun p => P.yStar p.1) _ p history hinit
  intro p y
  rw [InnerOracle.lowerY_truth]
  exact InnerGeometry.contraction P p.1 y

theorem adjointThenDirection_error (hμL : b.μ ≤ b.L₁) (k : ℕ) {h a u ε : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hu : 0 < u) (hε : 0 < ε) (hfloor : 6*a ^ 2/b.μ ^ 2 ≤ u ^ 2/4)
    (hbiasY : ∀ x y v, ‖v‖ ≤ ballRadius b → ‖(P.gradientDifference x y v k h).snd-P.gyy x y v‖ ≤ a)
    (hbiasX : ∀ x y v, ‖v‖ ≤ ballRadius b → ‖(P.gradientDifference x y v k h).fst-P.gxy x y v‖ ≤ a)
    (p : X × Y) (history : History) :
    Integrable (fun z => ‖z.1-gradient P.objective p.1‖)
      ((adjointThenDirection P O k h u ε).law (p,history)) ∧
    (∫ z, ‖z.1-gradient P.objective p.1‖ ∂(adjointThenDirection P O k h u ε).law (p,history)) ≤
      ε/32+a+b.L₁*u+innerSensitivity b*‖p.2-P.yStar p.1‖ := by
  have hv := AdjointSolve.program_expected_norm P O hμL k hh ha hu hfloor hbiasY p history
  have hb := Procedure.bind_output_bound (AdjointSolve.program P O k h u)
    (direction P O k h (outputBatch b ((2*k+1:ℕ)/h) ε)) p history
    (fun q => ‖q-gradient P.objective p.1‖) (by fun_prop) (fun _ => norm_nonneg _)
    (fun v => ε/32+a+b.L₁*‖v-target P p‖+innerSensitivity b*‖p.2-P.yStar p.1‖)
    (((integrable_const (ε/32+a)).add (hv.1.const_mul b.L₁)).add (integrable_const _))
    (fun z => (direction_error P O k hh hε hbiasX (p,z.1) z.2.1).1)
    (fun z => (direction_error P O k hh hε hbiasX (p,z.1) z.2.1).2)
  refine ⟨hb.1,hb.2.trans ?_⟩
  have he₁ := integral_add (integrable_const (μ := (AdjointSolve.program P O k h u).law (p,history))
    (ε/32+a)) (hv.1.const_mul b.L₁)
  have he₂ := integral_add ((integrable_const (ε/32+a)).add (hv.1.const_mul b.L₁))
    (integrable_const (innerSensitivity b*‖p.2-P.yStar p.1‖))
  simp only [Pi.add_apply] at he₁ he₂
  rw [he₂,he₁,integral_const_mul]
  simp only [integral_const,measureReal_univ_eq_one,one_smul]
  exact add_le_add_right (add_le_add_left (mul_le_mul_of_nonneg_left hv.2 b.L₁_pos.le) _) _

theorem program_error (hgap : b.μ < b.L₁) (k : ℕ) {h a D uy uv ε : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hD : 0 ≤ D) (huy : 0 < uy) (huv : 0 < uv) (hε : 0 < ε)
    (hfloor : 6*a ^ 2/b.μ ^ 2 ≤ uv ^ 2/4)
    (hbiasY : ∀ x y v, ‖v‖ ≤ ballRadius b → ‖(P.gradientDifference x y v k h).snd-P.gyy x y v‖ ≤ a)
    (hbiasX : ∀ x y v, ‖v‖ ≤ ballRadius b → ‖(P.gradientDifference x y v k h).fst-P.gxy x y v‖ ≤ a)
    (p : X × Y) (history : History) (hinit : ‖p.2-P.yStar p.1‖ ≤ D) :
    Integrable (fun z => ‖z.1-gradient P.objective p.1‖) ((program P O k h D uy uv ε).law (p,history)) ∧
    (∫ z, ‖z.1-gradient P.objective p.1‖ ∂(program P O k h D uy uv ε).law (p,history)) ≤
      ε/32+a+b.L₁*uv+innerSensitivity b*uy := by
  have hy := inner_expected_norm P O hgap hD huy p history hinit
  have hb := Procedure.bind_output_bound (inner P O D uy) (afterInner P O k h uv ε) p history
    (fun q => ‖q-gradient P.objective p.1‖) (by fun_prop) (fun _ => norm_nonneg _)
    (fun y => ε/32+a+b.L₁*uv+innerSensitivity b*‖y-P.yStar p.1‖)
    ((integrable_const _).add (hy.1.const_mul _))
    (fun z => (adjointThenDirection_error P O hgap.le k hh ha huv hε hfloor hbiasY hbiasX
      (p.1,z.1) z.2.1).1)
    (fun z => (adjointThenDirection_error P O hgap.le k hh ha huv hε hfloor hbiasY hbiasX
      (p.1,z.1) z.2.1).2)
  refine ⟨hb.1,hb.2.trans ?_⟩
  have he := integral_add (integrable_const (μ := (inner P O D uy).law (p,history)) (ε/32+a+b.L₁*uv))
    (hy.1.const_mul (innerSensitivity b))
  simp only [Pi.add_apply] at he
  rw [he,integral_const_mul]
  simp only [integral_const,measureReal_univ_eq_one,one_smul]
  exact add_le_add_left (mul_le_mul_of_nonneg_left hy.2 (innerSensitivity_pos b).le) _

end Smoothness2601.HypergradientSolve
