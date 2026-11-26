import MatchingBounds1005.SourceReferenceProtocol
import MatchingBounds1005.SourceReferencePrefix
import MatchingBounds1005.TensorVisibleSignal
import MatchingBounds1005.CensoredTraceEnergy

/-! Exact hidden signals and tensor observation rows of the actual source
reference protocol, including uniform signal-norm control for integrability. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace MatchingBounds1005.SourceReferenceReplay
open ReferenceState TensorChannelRows TensorGeometry TensorAdaptiveRows SequentialPosterior
open SourceReferenceProgram CensoredGaussianProcess ShiftedSequential HistoryPath
variable {Rot Seed : Type} [MeasurableSpace Rot] [MeasurableSpace Seed] {d H N : ℕ}

def actualQuery (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d) (n : ℕ) (h : History (Rot × Seed) (H * (d + d)) n) : Vec d :=
  confinedQuery A P.R n (before P A U n h)

theorem actualQuery_measurable (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2)))) (n : ℕ) :
    Measurable (actualQuery (H := H) P A U n) :=
  (confinedQuery_measurable A P.R n).comp (before_measurable P A U hb hc hQ n)

theorem protocol_tensorRows (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2)))) :
    (protocol (H := H) P A U hb hc hQ).original.rowProtocol =
      tensorProtocol P.σ₃ P.σ₄ (actualQuery P A U) (actualQuery_measurable P A U hb hc hQ) := rfl

theorem protocol_hidden (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (hτ : ∀ i, 0 < P.disclosure i) (n : ℕ) (h : History (Rot × Seed) (H * (d + d)) n) :
    hidden (protocol P A U hb hc hQ) n h = normalizedSignal P.σ₃ P.σ₄
      (stoppedCoordinates 3 Finset.univ (fun i => U (initialSeed n h).1 (P.b i))
        (-120 * P.τ * P.a ^ 3) (fun i => P.disclosure i - 1) n)
      (stoppedCoordinates 4 Finset.univ (fun i => U (initialSeed n h).1 (P.b i))
        (120 * P.τ * P.a ^ 4) (fun i => P.disclosure i - 1) n) := by
  change fullSignal P U (initialSeed n h).1 - visibleSignal P.τ P.a P.σ₃ P.σ₄ (before P A U n h) = _
  unfold fullSignal visibleSignal
  rw [before_readouts P A U hτ]
  exact hidden_normalized_signal _ _ _ _ _ _ _ _

theorem protocol_hidden_norm (P : Parameters d N) (A : Model.Algorithm d Seed)
    (U : Rot → Vec d →L[ℝ] Vec d)
    (hb : ∀ i, Measurable (fun ρ => U ρ (P.b i)))
    (hc : Measurable (fun ρ => U ρ P.c))
    (hQ : Measurable (fun p : Rot × Vec d => U p.1 (P.Q ((U p.1).adjoint p.2))))
    (hτ : ∀ i, 0 < P.disclosure i) (hunit : ∀ ρ i, ‖U ρ (P.b i)‖ = 1)
    (n : ℕ) (h : History (Rot × Seed) (H * (d + d)) n) :
    ‖hidden (protocol P A U hb hc hQ) n h‖ ^ 2 / (2 * (1 : ℝ) ^ 2) ≤
      (N : ℝ) ^ 2 * (-120 * P.τ * P.a ^ 3) ^ 2 / (2 * P.σ₃ ^ 2) +
      (N : ℝ) ^ 2 * (120 * P.τ * P.a ^ 4) ^ 2 / (2 * P.σ₄ ^ 2) := by
  rw [protocol_hidden P A U hb hc hQ hτ]
  simpa only [one_pow, mul_one, Finset.card_univ, Fintype.card_fin] using
    stopped_pair_norm_energy Finset.univ (fun i => U (initialSeed n h).1 (P.b i))
      (fun i _ => hunit _ i) (-120 * P.τ * P.a ^ 3) (120 * P.τ * P.a ^ 4)
      P.σ₃ P.σ₄ (fun i => P.disclosure i - 1) n

end MatchingBounds1005.SourceReferenceReplay
