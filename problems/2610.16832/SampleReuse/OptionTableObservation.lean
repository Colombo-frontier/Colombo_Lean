import SampleReuse.OptionTableMarginal
import SampleReuse.PersistentTableKernel

open SecondOrder MeasureTheory ProbabilityTheory
open scoped Classical

namespace SampleReuse
noncomputable section

variable {S Handle A Y : Type} [Fintype Handle] [Fintype A]
  [MeasurableSpace S] [MeasurableSpace Handle] [MeasurableSingletonClass Handle]
  [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Y]

local instance optionObservation_measurable : MeasurableSpace (Option Handle) := ⊤
local instance optionObservation_singleton : MeasurableSingletonClass (Option Handle) := ⟨fun _ => trivial⟩

omit [MeasurableSpace Handle] [MeasurableSingletonClass Handle] in
theorem option_table_marginal_measure (q : PMF A) (p : Handle → PMF A) :
    (finitePiPMF (fun key : Option Handle => key.elim q p)).toMeasure.map
      (fun table => fun r => table (some r)) = (finitePiPMF p).toMeasure := by
  rw [PMF.toMeasure_map _ _ (measurable_of_countable _),option_table_marginal]

omit [MeasurableSpace Handle] [MeasurableSingletonClass Handle] in
/-- A measurable numerical observation that ignores the nuisance dummy key
has precisely its immutable real-handle table law. -/
theorem option_table_observation_law
    (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Option Handle) (hq : ∀ n, Measurable (query n))
    (q : PMF A) (p : Handle → PMF A) (N : ℕ)
    (Φ : FiniteHistory S A N → Y) (hΦ : Measurable Φ)
    (obs : S × (Handle → A) → Y) (hobs : Measurable obs)
    (hsim : ∀ s table a₀, Φ (tableHistory query s (extendOptionTable a₀ table) N) = obs (s,table)) :
    (adaptiveKernelLaw μ (measurableDisclosureKernel query hq (fun key => key.elim q p)) N).map Φ =
      (μ.prod (finitePiPMF p).toMeasure).map obs := by
  have ht : Measurable (fun table : (Option Handle → A) => fun r => table (some r)) :=
    measurable_of_countable _
  have hm : (μ.prod (finitePiPMF (fun key : Option Handle => key.elim q p)).toMeasure).map
      (fun z : S × (Option Handle → A) => (z.1,fun r => z.2 (some r))) =
      μ.prod (finitePiPMF p).toMeasure := by
    have hh := Measure.map_prod_map μ
      (finitePiPMF (fun key : Option Handle => key.elim q p)).toMeasure measurable_id ht
    rw [Measure.map_id,option_table_marginal_measure] at hh
    exact hh.symm
  rw [← fixed_table_transcript_law query hq (fun key => key.elim q p) μ N,
    Measure.map_map hΦ (tableHistory_measurable query hq N),← hm]
  have hproj : Measurable (fun z : S × (Option Handle → A) => (z.1,fun r => z.2 (some r))) :=
    measurable_fst.prodMk (ht.comp measurable_snd)
  rw [Measure.map_map hobs hproj]
  congr 1
  funext z
  have he : z.2 = extendOptionTable (z.2 none) (fun r => z.2 (some r)) := by
    funext key
    cases key <;> rfl
  change Φ (tableHistory query z.1 z.2 N) = obs (z.1,fun r => z.2 (some r))
  conv_lhs => rw [he]
  exact hsim z.1 (fun r => z.2 (some r)) (z.2 none)

end
end SampleReuse
