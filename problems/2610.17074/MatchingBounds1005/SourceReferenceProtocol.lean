import MatchingBounds1005.SourceReferenceReplay
import MatchingBounds1005.CensoredReferenceSampler

/-! The concrete source calculation defines an actual censored Gaussian protocol. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.SourceReferenceReplay
open GaussianVector ReferenceState TensorChannelRows SequentialPosterior
open SourceReferenceProgram ShiftedSequential AccumulatedRows CensoredGaussianProcess
open TensorGeometry hiding Vec

variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

theorem current_measurable (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (n : ℕ) (i : Fin (d + d)) :
    Measurable (fun h : History (Rot × Seed) (H * (d + d)) n => current P A U n h i) :=
  (jointRows_measurable P.σ₃ P.σ₄ i).comp
    ((confinedQuery_measurable A P.R n).comp (before_measurable P A U hb hc hQ n))

def fullSignal (P : Parameters d N) (U : Rot → Vec d →L[ℝ] Vec d) (ρ : Rot) : Vec (jointDim d) :=
  normalizedSignal P.σ₃ P.σ₄
    (tensorCoordinates d 3 (cubicSignal P.τ P.a (fun i => U ρ (P.b i))))
    (tensorCoordinates d 4 (quarticSignal P.τ P.a (fun i => U ρ (P.b i))))

theorem fullSignal_measurable (P : Parameters d N) (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i))) : Measurable (fullSignal P U) := by
  have hr : Measurable (fun ρ i => U ρ (P.b i)) := measurable_pi_lambda _ hb
  have h3 := (tensorCoordinates d 3).continuous.measurable.comp
    ((VisibleReadouts.signal_measurable 3 (-120 * P.τ * P.a ^ 3)).comp hr)
  have h4 := (tensorCoordinates d 4).continuous.measurable.comp
    ((VisibleReadouts.signal_measurable 4 (120 * P.τ * P.a ^ 4)).comp hr)
  exact TensorAdaptiveRows.normalizedSignal_measurable P.σ₃ P.σ₄ _ _ h3 h4

def protocol (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2)))) :
    CensoredProtocol (Rot × Seed) (jointDim d) (H * (d + d)) where
  original := {
    rowProtocol := AccumulatedRows.protocol (current P A U) (current_measurable P A U hb hc hQ)
    signal := fun ω => fullSignal P U ω.1
    measurable_signal := (fullSignal_measurable P U hb).comp measurable_fst }
  visible n h := visibleSignal P.τ P.a P.σ₃ P.σ₄ (before P A U n h)
  measurable_visible n := (visibleSignal_measurable P.τ P.a P.σ₃ P.σ₄).comp
    (before_measurable P A U hb hc hQ n)

theorem queryInput_eq (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (n : ℕ) (h : History (Rot × Seed) (H * (d + d)) n) :
    queryInput A P.τ P.a P.σ₃ P.σ₄ P.R n (before P A U n h) =
      ReferenceTransitionLink.accessibleInput (protocol P A U hb hc hQ) n h := by
  unfold queryInput ReferenceTransitionLink.accessibleInput
  rw [oldRows_before, oldAnswers_before, queryRows_before]
  rfl

/-- The implemented finite-row response is exactly the previously proved
reference transition, including all fitted previous measurements. -/
theorem transition_eq_reference (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (n : ℕ) (h : History (Rot × Seed) (H * (d + d)) n) (z : Vec (jointDim d)) :
    ReferenceTransition.transition 1
      (queryInput A P.τ P.a P.σ₃ P.σ₄ P.R n (before P A U n h), z) =
        response (protocol P A U hb hc hQ) 1 n ((protocol P A U hb hc hQ).visible n) (h, z) := by
  rw [queryInput_eq P A U hb hc hQ]
  exact ReferenceTransitionLink.transition_eq_response _ _ _ _ _

end MatchingBounds1005.SourceReferenceReplay
