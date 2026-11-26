import Smoothness2601.NormalizedOutput
import Smoothness2601.OuterSchedule
import Smoothness2601.HypergradientCost

/-! Actual source upper algorithm before optimizing the differencing order:
fixed original-call budget, restarted lower/adjoint solves, normalized outer
path, and an independently uniform output with expected norm at most 3ε/4. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.Stateful
namespace Smoothness2601.OuterSource
open HypergradientGeometry OuterSchedule

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def estimator (M Λ β cₐ : ℝ) (r : ℕ) (ε : ℝ) : Procedure (X × Y) History X :=
  HypergradientSource.program P O M Λ β cₐ r (radius b ε) ε

def path (M Λ β cₐ : ℝ) (r : ℕ) (ε : ℝ) :
    Procedure (X × Y) History (NormalizedExecution.Path X (iterations b ε)) :=
  NormalizedExecution.run (estimator P O M Λ β cₐ r ε) (stepsize b ε) (iterations b ε)

def callCount (b : Budgets) (M Λ β cₐ : ℝ) (r : ℕ) (ε : ℝ) : ℕ :=
  iterations b ε*HypergradientSource.samples b M Λ β cₐ r (radius b ε) ε

theorem path_calls (M Λ β cₐ : ℝ) (r : ℕ) (ε : ℝ) :
    (path P O M Λ β cₐ r ε).CallsEq (fun _ => callCount b M Λ β cₐ r ε) :=
  NormalizedExecution.run_calls _ _ (HypergradientSource.program_calls P O M Λ β cₐ r _ ε) _ _

def outputLaw (M Λ β cₐ : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (p : X × Y) (history : History) :
    Measure (Fin (iterations b ε) × Outcome (NormalizedExecution.Path X (iterations b ε)) History) :=
  letI : NeZero (iterations b ε) := ⟨(iterations_pos b hε).ne'⟩
  NormalizedExecution.outputLaw (estimator P O M Λ β cₐ r ε) (stepsize b ε) (iterations b ε) p history

instance outputLaw_probability (M Λ β cₐ : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (p : X × Y) (history : History) : IsProbabilityMeasure (outputLaw P O M Λ β cₐ r hε p history) := by
  unfold outputLaw
  infer_instance

theorem output_calls (M Λ β cₐ : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (p : X × Y) (history : History) :
    ∀ᵐ z ∂outputLaw P O M Λ β cₐ r hε p history, z.2.2.2 = callCount b M Λ β cₐ r ε := by
  unfold outputLaw NormalizedExecution.outputLaw
  apply (Measure.ae_prod_iff_ae_ae
    ((measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton _))).mpr
  filter_upwards with i
  exact path_calls P O M Λ β cₐ r ε p history

variable [FiniteDimensional ℝ Y]

/-- The actual conditional-kernel output has finite expected gradient norm
and the source 3ε/4 margin. Neither descent nor estimator error is assumed. -/
theorem expected_stationarity {pmax : WithTop ℕ} {M Λ β cₐ ε : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (hcₐ : 0 < cₐ) (hsmall : cₐ ≤ b.μ/(256*b.L₁)) (hε : 0 < ε)
    (hreg : P.HigherRegularity pmax (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ pmax)
    (p : X × Y) (history : History) (hinit : P.Initialized p.1 p.2) :
    Integrable (fun z => ‖gradient P.objective (NormalizedExecution.selected z)‖)
      (outputLaw P O M Λ β cₐ r hε p history) ∧
    (∫ z, ‖gradient P.objective (NormalizedExecution.selected z)‖
      ∂outputLaw P O M Λ β cₐ r hε p history) ≤ 3*ε/4 := by
  letI : NeZero (iterations b ε) := ⟨(iterations_pos b hε).ne'⟩
  have hf (x : X) : HasGradientAt P.objective (gradient P.objective x) x :=
    (P.primitive.hasGradient_hyperobjective P.primitive.canonicalResponse x).differentiableAt.hasGradientAt
  have hfloor (x : X) : sInf (Set.range P.objective) ≤ P.objective x :=
    csInf_le hinit.bounded_below ⟨x,rfl⟩
  have hA (x : X) (h : History) (hdist : ‖x-p.1‖ ≤ travel b ε) :=
    HypergradientSource.program_error P O hgap hM hΛ hβ hcₐ hsmall (radius_nonneg b hε) hε hreg
      r hr hrp (x,p.2) h (InnerGeometry.initial_radius P p.1 x p.2 hinit.inner_error hdist)
  have hh := NormalizedExecution.expected_selected_norm (estimator P O M Λ β cₐ r ε)
    P.objective (gradient P.objective) (outerSmoothness_pos b).le (stepsize_pos b hε)
    hf (outer_smoothness P) (sInf (Set.range P.objective)) hfloor (iterations b ε) le_rfl
    p history hinit.initial_gap hA
  exact ⟨hh.1,hh.2.trans (stationarity_budget b hε)⟩

theorem total_sample_budget (b : Budgets) (hgap : b.μ < b.L₁)
    {M Λ β cₐ ε : ℝ} (hcₐ : 0 < cₐ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεC : ε ≤ 32*innerSensitivity b) (hεL : ε ≤ 32*b.L₁) (r : ℕ) :
    let h := HypergradientSource.differenceRadius b M Λ β cₐ ε r
    let k := Population.stencilHalfOrder r
    (callCount b M Λ β cₐ r ε:ℝ) ≤ (iterations b ε:ℝ)*HypergradientCost.constant b*
      ((1+((2*k+1:ℕ)/h) ^ 2)*(1/ε ^ 2)+(2*k+2:ℕ)*Real.log (2/ε)+Real.log (2+radius b ε/ε)) := by
  dsimp only
  have hb := HypergradientCost.per_outer_budget b hgap (Population.stencilHalfOrder r)
    (Population.populationRadius_pos (b := b) (M := M) (Λ := Λ) (β := β)
      (AdjointGeometry.ballRadius_one b) (mul_pos hcₐ hε) r)
    (radius_nonneg b hε) hε hε1 hεC hεL
  have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (iterations b ε): (0:ℝ) ≤ iterations b ε)
  simpa only [callCount,HypergradientSource.samples,Nat.cast_mul,mul_assoc] using hh

end Smoothness2601.OuterSource
