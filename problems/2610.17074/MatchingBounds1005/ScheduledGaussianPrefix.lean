import MatchingBounds1005.ScheduledHaarPrefix
import MatchingBounds1005.GaussianBlockGeometry

/-! Quantitative hidden-prefix control under the actual single-Haar law,
derived by exact transcript pushforward from genuine iid Gaussian starts. -/
noncomputable section
open scoped InnerProductSpace
open MeasureTheory RandomizedFO2003.Rotations
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianHaar
open MatchingBounds1005.GaussianStarts MatchingBounds1005.GaussianBlockGeometry
open MatchingBounds1005.GaussianMatrix
open MatchingBounds1005.ScheduledPrefix

namespace MatchingBounds1005.ScheduledHaar
universe u

theorem RoundPolicy.gaussian_chronological_representation (d n : ℕ)
    (hdim : 0 < d + actionCount n) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ]
    (Q : Vec (d + actionCount n) →L[ℝ] Vec (d + actionCount n))
    (plan : RoundPolicy (Vec (d + actionCount n)) n H)
    (I : ℕ → Submodule ℝ (Vec (d + actionCount n)))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q n I) :
    (μ.prod (haarLaw (Vec (d + actionCount n)))).map
      (fun p => plan.run n Q (p.2 : Vec (d + actionCount n) →L[ℝ]
        Vec (d + actionCount n)) p.1) =
      (gaussianPairLaw (d + actionCount n) (actionCount n) μ).map
        (fun p => (plan.compile Q n).directAmbientTranscript
          d (actionCount n) (fun _ => .initial) id
            (normalizePairs (d + actionCount n) (actionCount n) p)) ∧
    (∀ᵐ p ∂gaussianPairLaw (d + actionCount n) (actionCount n) μ,
      ChronologicalIn I
        (cyclicSpan Q (AmbientPairHistory.starts (Vec (d + actionCount n)) (actionCount n) p))
        (List.ofFn (roundQueryTrace (Vec (d + actionCount n)) n
          ((plan.compile Q n).directAmbientTranscript d (actionCount n)
            (fun _ => .initial) id
              (normalizePairs (d + actionCount n) (actionCount n) p))))) := by
  have hr := plan.haar_ambient_chronological d n μ Q I hmono hschedule
  have hn := normalizePairs_preserving hdim (actionCount n) μ
  constructor
  · have htr := ((plan.compile Q n).haar_ambient_information d (actionCount n) μ).1
    have hp := congrArg (fun ν => ν.map ((plan.compile Q n).directAmbientTranscript
      d (actionCount n) (fun _ => .initial) id)) hn.map_eq
    dsimp only at hp
    rw [Measure.map_map htr hn.measurable] at hp
    exact hr.1.trans hp.symm
  · have hp := hn.quasiMeasurePreserving.ae hr.2
    simpa only [cyclicSpan_normalizePairs, plan.selectQueries_eq] using hp

/-- The only probabilistic input is the already proved iid Gaussian cyclic
angle estimate. The output event is measurable and concerns the actual full
scheduled Haar transcript, uniformly over all hidden directions and prefixes. -/
theorem RoundPolicy.haar_prefix_failure (d n : ℕ)
    (hdim : 0 < d + actionCount n) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (Q : Vec (d + actionCount n) →L[ℝ] Vec (d + actionCount n))
    (plan : RoundPolicy (Vec (d + actionCount n)) n H)
    (I : ℕ → Submodule ℝ (Vec (d + actionCount n)))
    (A : Submodule ℝ (Vec (d + actionCount n)))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q n I)
    (hIA : ∀ t, I t ≤ A) {η ζ : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hangle : (gaussianMatrixLaw (d + actionCount n) (actionCount n + actionCount n)).real
      {g | ¬ CyclicAngleGood A Q g η} ≤ ζ) :
    (μ.prod (haarLaw (Vec (d + actionCount n)))).real
      {p | roundQueryTrace (Vec (d + actionCount n)) n
        (plan.run n Q (p.2 : Vec (d + actionCount n) →L[ℝ] Vec (d + actionCount n)) p.1)
          ∉ prefixEvent I A η} ≤ ζ := by
  let sim := fun p => (plan.compile Q n).directAmbientTranscript
    d (actionCount n) (fun _ => .initial) id
      (normalizePairs (d + actionCount n) (actionCount n) p)
  let bad := (transcriptEvent n (H := H) I A η)ᶜ
  have hbad : MeasurableSet bad := (measurableSet_transcriptEvent n I A η).compl
  have hn := normalizePairs_preserving hdim (actionCount n) μ
  have hsim : Measurable sim :=
    ((plan.compile Q n).haar_ambient_information d (actionCount n) μ).1.comp hn.measurable
  have hr := plan.gaussian_chronological_representation d n hdim μ Q I hmono hschedule
  have hlaw := congrArg (fun ν => ν bad) hr.1
  dsimp only at hlaw
  rw [Measure.map_apply (plan.run_measurable d n Q) hbad, Measure.map_apply hsim hbad] at hlaw
  have heq := congrArg ENNReal.toReal hlaw
  change (μ.prod (haarLaw (Vec (d + actionCount n)))).real
      {p | roundQueryTrace (Vec (d + actionCount n)) n
        (plan.run n Q (p.2 : Vec (d + actionCount n) →L[ℝ] Vec (d + actionCount n)) p.1)
          ∉ prefixEvent I A η} =
    (gaussianPairLaw (d + actionCount n) (actionCount n) μ).real (sim ⁻¹' bad) at heq
  rw [heq]
  have hsubset : sim ⁻¹' bad ≤ᵐ[gaussianPairLaw (d + actionCount n) (actionCount n) μ]
      {p | ¬ CyclicAngleGood A Q
        (AmbientPairHistory.starts (Vec (d + actionCount n)) (actionCount n) p) η} := by
    filter_upwards [hr.2] with p hp
    intro hfail hgood
    exact hfail (chronological_mem_prefixEvent _ I A _ hmono hp hIA hη hηhalf hgood)
  apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset))
  exact (preserving_failure_le (starts_preserving (d + actionCount n) (actionCount n) μ)
    {g | ¬ CyclicAngleGood A Q g η}).trans hangle

/-- Source commands keep their public semantics: disclosures and the frozen
unqueried candidate are represented by the already verified compiled rounds. -/
theorem SourcePolicy.haar_prefix_failure (w : List SourceKind) (d : ℕ)
    (hdim : 0 < d + actionCount w.length) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (Q : Vec (d + actionCount w.length) →L[ℝ] Vec (d + actionCount w.length))
    (plan : SourcePolicy (E := Vec (d + actionCount w.length)) w H)
    (I : ℕ → Submodule ℝ (Vec (d + actionCount w.length)))
    (A : Submodule ℝ (Vec (d + actionCount w.length)))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q w I)
    (hIA : ∀ t, I t ≤ A) {η ζ : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hangle : (gaussianMatrixLaw (d + actionCount w.length)
      (actionCount w.length + actionCount w.length)).real
      {g | ¬ CyclicAngleGood A Q g η} ≤ ζ) :
    (μ.prod (haarLaw (Vec (d + actionCount w.length)))).real
      {p | roundQueryTrace (Vec (d + actionCount w.length)) w.length
        ((plan.compile w).run w.length Q
          (p.2 : Vec (d + actionCount w.length) →L[ℝ] Vec (d + actionCount w.length)) p.1)
          ∉ prefixEvent I A η} ≤ ζ :=
  (plan.compile w).haar_prefix_failure d w.length hdim μ Q I A hmono
    (plan.compile_scheduled w Q I hschedule) hIA hη hηhalf hangle

end MatchingBounds1005.ScheduledHaar

namespace MatchingBounds1005.ScheduledPrefix
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem prefixEvent_readout {n : ℕ} {xs : Fin n → E}
    {I : ℕ → Submodule ℝ E} {A : Submodule ℝ E} {η : ℝ}
    (hx : xs ∈ prefixEvent I A η) (t : ℕ) (i : Fin n) (hi : i.val ≤ t)
    (a : E) (ha : a ∈ A) (hh : a ∈ (I t)ᗮ) :
    |⟪a, xs i⟫_ℝ| ≤ 2 * η * ‖a‖ * ‖xs i‖ := by
  have h := hx t a ha hh (Pi.single i 1)
  have he : synthesis xs t (Pi.single i 1) = xs i := by
    unfold synthesis
    rw [Finset.sum_eq_single i]
    · simp [maskedPrefix, hi]
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  simpa only [he] using h

end MatchingBounds1005.ScheduledPrefix
