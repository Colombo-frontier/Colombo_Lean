import Smoothness2601.AdjointKernels
import Smoothness2601.AdjointIteration
import Smoothness2601.AdjointGeometry
import Smoothness2601.DifferencingOracle

/-! Actual source projected adjoint solver: serial Chebyshev node calls,
fresh upper-gradient calls, radial projection and fixed geometric batches. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Bilevel.Stateful Bilevel.PrimitiveGeometry
namespace Smoothness2601.AdjointSolve
open AdjointGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def clippedInput (b : Budgets) (z : (X × Y) × Y) : X × Y × Y :=
  (z.1.1,z.1.2,Bilevel.Clipping.clip (ballRadius b) z.2)

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [BorelSpace X]
  [CompleteSpace Y] [SecondCountableTopology X] in
theorem clippedInput_measurable (b : Budgets) :
    Measurable (clippedInput (X := X) (Y := Y) b) :=
  (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk
    (AdjointContraction.clip_stronglyMeasurable (ballRadius b) measurable_snd.stronglyMeasurable).measurable)

def step (k : ℕ) (h : ℝ) (N : ℕ) : Procedure ((X × Y) × Y) History Y :=
  (AdjointKernels.projectedStep (InnerOracle.blockY P O false)
    (DifferencingOracle.estimatorY P O k h N) (fun p => (p.1,p.2.1)) (by fun_prop)
    (fun p => p.2.2) (by fun_prop) (ballRadius b) N (stepsize b)).reparam
      (clippedInput b) (clippedInput_measurable b)

def stepSamples (k : ℕ) (h : ℝ) (N : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (2*k+2), DifferencingOracle.nodeBatch k h N j)+N

theorem step_calls (k : ℕ) (h : ℝ) (N : ℕ) :
    (step P O k h N).CallsEq (fun _ => stepSamples k h N) :=
  Procedure.CallsEq.reparam _ _
    (AdjointKernels.projectedStep_calls _ _ _ _ _ _ _ _ _ _
      (DifferencingOracle.estimatorY_calls P O k h N)) _ _

theorem step_bounded (k : ℕ) (h : ℝ) (N : ℕ) (p : X × Y) (v : Y) (history : History) :
    ∀ᵐ z ∂(step P O k h N).law ((p,v),history), ‖z.1‖ ≤ ballRadius b :=
  AdjointKernels.projectedStep_bounded _ _ _ _ _ _ (ballRadius_nonneg b) N (stepsize b)
    (clippedInput b (p,v)) history

theorem step_samples_bound (k : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ) (hN : 0 < N) :
    (stepSamples k h N : ℝ) ≤ 2*(N:ℝ)+(2*k+2:ℕ) := by
  have ht := DifferencingOracle.estimator_count_bound k hh (Nat.cast_pos.mpr hN)
  dsimp [stepSamples]
  push_cast at ht ⊢
  linarith

variable [FiniteDimensional ℝ Y]

theorem step_error (hμL : b.μ ≤ b.L₁) (k : ℕ) {h a : ℝ} (hh : 0 < h) (ha : 0 ≤ a)
    (hbias : ∀ x y v, ‖v‖ ≤ ballRadius b →
      ‖(P.gradientDifference x y v k h).snd-P.gyy x y v‖ ≤ a)
    (N : ℕ) (hN : 0 < N) (p : X × Y) (v : Y) (history : History) :
    Integrable (fun z => ‖z.1-target P p‖ ^ 2) ((step P O k h N).law ((p,v),history)) ∧
    (∫ z, ‖z.1-target P p‖ ^ 2 ∂(step P O k h N).law ((p,v),history)) ≤
      rate b*‖v-target P p‖ ^ 2+biasTerm b a+noiseTerm b ((2*k+1:ℕ)/h)/(N:ℝ) := by
  let c := Bilevel.Clipping.clip (ballRadius b) v
  let m := (P.gradientDifference p.1 p.2 c k h).snd
  have hm := AdjointKernels.projectedStep_error (InnerOracle.blockY P O false)
    (DifferencingOracle.estimatorY P O k h N) (fun p => (p.1,p.2.1)) (by fun_prop)
    (fun p => p.2.2) (by fun_prop) (ballRadius_nonneg b) N hN (stepsize_pos b).ne'
    (p.1,p.2,c) history m (target P p) (target_in_ball P p)
    (fun center => DifferencingOracle.estimatorY_center_error P O k hh (Nat.cast_pos.mpr hN)
      (p.1,p.2,c) history center)
  refine ⟨hm.1,hm.2.trans ?_⟩
  rw [InnerOracle.upperY_truth]
  have hd := clipped_drift P hμL ha p v m (hbias _ _ _
    (Bilevel.Clipping.bounded _ (ballRadius_nonneg b) v))
  have he : stepsize b ^ 2*(b.σ ^ 2*((2*k+1:ℕ)/h) ^ 2/(N:ℝ)+b.σ ^ 2/(N:ℝ)) =
      noiseTerm b ((2*k+1:ℕ)/h)/(N:ℝ) := by unfold noiseTerm; ring
  rw [he]
  exact add_le_add_right hd _

def iterations (b : Budgets) (u : ℝ) : ℕ := GeometricBatches.iterations (rate b) (radius b) u
def batch (b : Budgets) (W u : ℝ) (j : ℕ) : ℕ :=
  GeometricBatches.batch (rate b) (noiseTerm b W) u (iterations b u) j

def program (k : ℕ) (h u : ℝ) : Procedure (X × Y) History Y :=
  AdjointIteration.run (fun j => step P O k h (batch b ((2*k+1:ℕ)/h) u j)) (iterations b u)

def samples (b : Budgets) (k : ℕ) (h u : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (iterations b u), stepSamples k h (batch b ((2*k+1:ℕ)/h) u j)

omit [FiniteDimensional ℝ Y] in
theorem program_calls (k : ℕ) (h u : ℝ) :
    (program P O k h u).CallsEq (fun _ => samples b k h u) :=
  AdjointIteration.run_calls _ _ (fun _ => step_calls P O k h _) _

omit [FiniteDimensional ℝ Y] in
theorem program_bounded (k : ℕ) (h u : ℝ) (p : X × Y) (history : History) :
    ∀ᵐ z ∂(program P O k h u).law (p,history), ‖z.1‖ ≤ ballRadius b :=
  AdjointIteration.run_bounded _ (ballRadius_nonneg b)
    (fun _ p v history => step_bounded P O k h _ p v history) _ p history

theorem program_expected_norm (hμL : b.μ ≤ b.L₁) (k : ℕ) {h a u : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hu : 0 < u) (hfloor : 6*a ^ 2/b.μ ^ 2 ≤ u ^ 2/4)
    (hbias : ∀ x y v, ‖v‖ ≤ ballRadius b →
      ‖(P.gradientDifference x y v k h).snd-P.gyy x y v‖ ≤ a)
    (p : X × Y) (history : History) :
    Integrable (fun z => ‖z.1-target P p‖) ((program P O k h u).law (p,history)) ∧
    (∫ z, ‖z.1-target P p‖ ∂(program P O k h u).law (p,history)) ≤ u := by
  have hr := rate_range b hμL
  have hd : 0 ≤ biasTerm b a := by
    have := stepsize_pos b
    have := b.μ_pos
    unfold biasTerm
    positivity
  have hA : 0 ≤ noiseTerm b ((2*k+1:ℕ)/h) := by unfold noiseTerm; positivity
  have hf : biasTerm b a/(1-rate b) ≤ u ^ 2/4 := by
    unfold biasTerm rate
    rw [AdjointContraction.bias_floor (stepsize_pos b) b.μ_pos]
    exact hfloor
  exact AdjointIteration.geometric_norm hr.1 hr.2 hd hA (radius_nonneg b) hu hf
    (fun j => step P O k h (batch b ((2*k+1:ℕ)/h) u j)) (target P)
    (fun j p v history => step_error P O hμL k hh ha hbias _
      (GeometricBatches.batch_pos _ _ _ _ _) p v history) p history (target_norm P p)

theorem population_solve {pmax : WithTop ℕ} {M Λ β a u : ℝ}
    (hμL : b.μ ≤ b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) (ha : 0 < a) (hu : 0 < u)
    (hfloor : 6*a ^ 2/b.μ ^ 2 ≤ u ^ 2/4)
    (hreg : P.HigherRegularity pmax (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ pmax) (p : X × Y) (history : History) :
    Integrable (fun z => ‖z.1-target P p‖)
      ((program P O (Population.stencilHalfOrder r)
        (Population.populationRadius b M Λ β (ballRadius b) a r) u).law (p,history)) ∧
    (∫ z, ‖z.1-target P p‖ ∂(program P O (Population.stencilHalfOrder r)
        (Population.populationRadius b M Λ β (ballRadius b) a r) u).law (p,history)) ≤ u :=
  program_expected_norm P O hμL _ (Population.populationRadius_pos (ballRadius_one b) ha r) ha.le hu hfloor
    (fun x y v hv => DifferencingOracle.populationRadius_y_bias P hM hΛ hβ (ballRadius_one b)
      ha hreg r hr hrp x y v hv) p history

theorem sample_budget (hμL : b.μ ≤ b.L₁) (k : ℕ) {h u : ℝ} (hh : 0 < h) :
    (samples b k h u : ℝ) ≤ (2*k+4:ℕ)*(iterations b u:ℝ)+
      8*noiseTerm b ((2*k+1:ℕ)/h)/(u ^ 2*(1-Real.sqrt (rate b)) ^ 2) := by
  have hstep := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (iterations b u)) =>
    step_samples_bound k hh (batch b ((2*k+1:ℕ)/h) u j) (GeometricBatches.batch_pos _ _ _ _ _))
  have hgeo := GeometricBatches.total_cost (u := u) (rate_range b hμL).2
    (by unfold noiseTerm; positivity : 0 ≤ noiseTerm b ((2*k+1:ℕ)/h)) (iterations b u)
  change (∑ j ∈ Finset.range (iterations b u), (batch b ((2*k+1:ℕ)/h) u j:ℝ)) ≤ _ at hgeo
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ← Finset.mul_sum] at hstep
  dsimp [samples]
  push_cast at hgeo hstep ⊢
  simp only [div_eq_mul_inv] at hgeo hstep ⊢
  nlinarith

end Smoothness2601.AdjointSolve
