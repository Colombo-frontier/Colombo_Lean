import SampleReuse.PersistentFiniteCap
import SampleReuse.PersistentInfiniteTape

open SecondOrder MeasureTheory
open scoped ENNReal
namespace SampleReuse
noncomputable section

/-- Finite sample laws suffice for the lower bound. Samples are full scalar
losses; admissibility refers to their actual common value/gradient/Hessian. -/
structure FiniteScalarInstance (M : Parameters) (d : ℕ) where
  Sample : Type
  finite : Fintype Sample
  measurable : MeasurableSpace Sample
  singletons : @MeasurableSingletonClass Sample measurable
  law : PMF Sample
  population : Point d → ℝ
  sample : Sample → Point d → ℝ
  smooth : ∀ z, ContDiff ℝ 2 (sample z)
  admissible : letI := measurable
    Admissible law.toMeasure M population sample 0

attribute [instance] FiniteScalarInstance.finite FiniteScalarInstance.measurable FiniteScalarInstance.singletons

def finiteInstanceReply {M : Parameters} {d : ℕ} (I : FiniteScalarInstance M d)
    (x : Point d) (z : I.Sample) := richReply I.sample z x

def finiteInstanceCost {M : Parameters} {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (I : FiniteScalarInstance M d) : ℝ≥0∞ :=
  ∫⁻ w : Ξ × (ℕ → I.Sample), (P w.1).extendedCost (finiteInstanceReply I) w.2
    ∂μ.prod (iidSampleTapeLaw I.law)

def SolvesFiniteInstances {M : Parameters} {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (ε γ : ℝ) : Prop :=
  ∀ I : FiniteScalarInstance M d, (2/3:ℝ) ≤
    (μ.prod (iidSampleTapeLaw I.law)).real {w : Ξ × (ℕ → I.Sample) |
      (P w.1).Halts (finiteInstanceReply I) w.2 ∧
      IsSOSP I.population ε γ ((P w.1).outputFor (finiteInstanceReply I) w.2)}

/-- Operational measurability of the numerical algorithm under every finite
smooth scalar sample oracle. It imposes no span, norm, finite-state, finite-
handle, or termination restriction, and no success or probability bound. -/
structure OperationallyMeasurable {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S) : Prop where
  finite_output : ∀ (Z : Type) [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (F : Z → Point d → ℝ), (∀ z, ContDiff ℝ 2 (F z)) → ∀ N (table : Fin (N+1) → Z),
    Measurable (fun ξ => finiteCapOutput (P ξ) (fun x z => richReply F z x) N table)
  stop_run : ∀ (Z : Type) [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (F : Z → Point d → ℝ), (∀ z, ContDiff ℝ 2 (F z)) → ∀ n,
    Measurable (fun w : Ξ × (ℕ → Z) => (P w.1).stopOnRun (fun x z => richReply F z x) w.2 n)

def pureScalarInstance {M : Parameters} {d : ℕ} (f : Point d → ℝ)
    (hf : Admissible (PMF.pure ()).toMeasure M f (fun _ : Unit => f) 0) :
    FiniteScalarInstance M d where
  Sample := Unit
  finite := inferInstance
  measurable := inferInstance
  singletons := inferInstance
  law := PMF.pure ()
  population := f
  sample := fun _ => f
  smooth _ := hf.population_smooth
  admissible := hf

end
end SampleReuse
