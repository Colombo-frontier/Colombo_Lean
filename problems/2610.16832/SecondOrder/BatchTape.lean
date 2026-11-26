import SecondOrder.AdaptiveAnchor
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- A coordinate of an arbitrary countable product has exactly its specified
law. The source spaces need not be finite or countably supported. -/
theorem infinitePi_eval_preimage {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {s : Set (X i)} (hs : MeasurableSet s) :
    Measure.infinitePi μ ((fun w => w i) ⁻¹' s) = μ i s := by
  let box : (j : ι) → Set (X j) := Function.update (fun _ => Set.univ) i s
  have hm : ∀ j ∈ ({i} : Finset ι), MeasurableSet (box j) := by
    intro j hj
    have hj' : j = i := Finset.mem_singleton.mp hj
    subst j
    simpa [box] using hs
  have he : Set.pi ({i} : Finset ι) box = (fun w => w i) ⁻¹' s := by
    ext w
    simp [Set.mem_pi, box]
  have hh := Measure.infinitePi_pi μ hm
  rw [he] at hh
  simpa [box] using hh

/-- A common source of randomness for every finite batch length. A local
routine reads only one coordinate: the batch selected before sampling.
Unobserved coordinates carry no oracle-query charge. -/
abbrev BatchTape (Ω : Type*) (R : ℕ) := (m : ℕ) → Draws (Draws Ω m) R

def batchTapeLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : ℕ) : Measure (BatchTape Ω R) :=
  Measure.infinitePi (fun m => drawsLaw (drawsLaw μ m) R)

instance batchTapeLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : ℕ) : IsProbabilityMeasure (batchTapeLaw μ R) := by
  unfold batchTapeLaw
  infer_instance

theorem batchTapeLaw_eval {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R m : ℕ) {s : Set (Draws (Draws Ω m) R)} (hs : MeasurableSet s) :
    batchTapeLaw μ R ((fun w => w m) ⁻¹' s) = drawsLaw (drawsLaw μ m) R s :=
  infinitePi_eval_preimage _ m hs

theorem localBatchSize_measurable {A : Type*} [MeasurableSpace A] {V : A → ℝ}
    (hV : Measurable V) (ρ : ℝ) : Measurable (fun a => localBatchSize (V a) ρ) :=
  (((hV.const_mul 36).div_const (ρ^2)).nat_ceil).add_const 1

end
end SecondOrder
