import SampleReuse.PersistentInfiniteTape
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section

theorem measurableSet_finite_sections {Ξ A : Type*} [MeasurableSpace Ξ]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (E : Ξ → A → Prop) (hE : ∀ a, MeasurableSet {ξ | E ξ a}) :
    MeasurableSet {w : Ξ × A | E w.1 w.2} := by
  have he : {w : Ξ × A | E w.1 w.2} = ⋃ a : A, {ξ | E ξ a} ×ˢ {a} := by
    ext ⟨ξ,a⟩
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun a => (hE a).prod (measurableSet_singleton a))

theorem product_event_real {Ξ A : Type*} [MeasurableSpace Ξ] [MeasurableSpace A]
    (μ : Measure Ξ) (ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (Ξ × A)) (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∫ ξ, ν.real {a | (ξ,a) ∈ E} ∂μ := by
  rw [measureReal_def,Measure.prod_apply hE]
  exact (integral_toReal (measurable_measure_prodMk_left hE).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top ν _))).symm

theorem iidSampleTapeLaw_joint_prefix {Ξ Z : Type*} [MeasurableSpace Ξ]
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (p : PMF Z) (n : ℕ) :
    (μ.prod (iidSampleTapeLaw p)).map (fun w : Ξ × (ℕ → Z) => (w.1,fun i : Fin n => w.2 i.val)) =
      μ.prod (finitePiPMF (fun _ : Fin n => p)).toMeasure := by
  have hp : Measurable (fun (tape : ℕ → Z) (i : Fin n) => tape i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hh := Measure.map_prod_map μ (iidSampleTapeLaw p) measurable_id hp
  rw [Measure.map_id,iidSampleTapeLaw_prefix_pmf] at hh
  exact hh.symm

/-- Exact finite-cylinder probability on the independent private-seed and
infinite sample-tape space. No finite-horizon tape law is assumed. -/
theorem iidSampleTapeLaw_event_probability {Ξ Z : Type*} [MeasurableSpace Ξ]
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (p : PMF Z) (n : ℕ)
    (E : Ξ → (Fin n → Z) → Prop) (hE : ∀ tape, MeasurableSet {ξ | E ξ tape}) :
    (μ.prod (iidSampleTapeLaw p)).real {w : Ξ × (ℕ → Z) | E w.1 (fun i => w.2 i.val)} =
      ∫ ξ, pmfEventProbability (finitePiPMF (fun _ : Fin n => p)) (fun tape => decide (E ξ tape)) ∂μ := by
  have hm : Measurable (fun w : Ξ × (ℕ → Z) => (w.1,fun i : Fin n => w.2 i.val)) :=
    measurable_fst.prodMk (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp measurable_snd))
  have he := measurableSet_finite_sections E hE
  have hmap := congrArg (fun ν : Measure (Ξ × (Fin n → Z)) => ν.real {w | E w.1 w.2})
    (iidSampleTapeLaw_joint_prefix μ p n)
  dsimp only at hmap
  rw [measureReal_def,Measure.map_apply hm he] at hmap
  change (μ.prod (iidSampleTapeLaw p)).real {w : Ξ × (ℕ → Z) | E w.1 (fun i => w.2 i.val)} = _ at hmap
  rw [hmap,product_event_real μ _ _ he]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simpa only [decide_eq_true_eq] using
    pmfEventProbability_measure (finitePiPMF (fun _ : Fin n => p)) (fun tape => decide (E ξ tape))

end
end SampleReuse
