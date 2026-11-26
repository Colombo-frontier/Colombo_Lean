import Bilevel.ChiSourceQueryVectors
import Bilevel.ChiUpperNoisePrimitiveOracle

/-! The direct upper-noise query has no normal variables. Its macro,
spectator, and lower coordinates are inserted before the current coin. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyExecution
open PrimitiveGeometry ChiCarrier ChiUpperNoise PartialLegendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def upperNoiseVector {m : ℕ} (p : Queries E (Blocks m E)) : QueryVectorIndex m → E
  | Sum.inl _ => p.fst.fst
  | Sum.inr (Sum.inl j) => p.fst.snd j
  | Sum.inr (Sum.inr j) => p.snd j

def upperNoiseVectors {m : ℕ} (p : Queries E (Blocks m E))
    (k : Fin (queryVectorCount m)) : E := upperNoiseVector p ((queryVectorEnumeration m).symm k)

variable [MeasurableSpace E] [BorelSpace E]

theorem upperNoiseVector_measurable {m : ℕ}
    [MeasurableSpace (Queries E (Blocks m E))] [BorelSpace (Queries E (Blocks m E))]
    (k : QueryVectorIndex m) : Measurable (fun p : Queries E (Blocks m E) => upperNoiseVector p k) := by
  cases k with
  | inl _ => exact ((jointFstLinear.comp jointFstLinear :
      Queries E (Blocks m E) →L[ℝ] E).continuous.measurable)
  | inr k =>
    cases k with
    | inl j => exact (((PiLp.proj 2 (fun _ : Fin m => E) j).comp
        (jointSndLinear.comp jointFstLinear) :
        Queries E (Blocks m E) →L[ℝ] E).continuous.measurable)
    | inr j => exact (((PiLp.proj 2 (fun _ : Fin m => E) j).comp jointSndLinear :
        Queries E (Blocks m E) →L[ℝ] E).continuous.measurable)

theorem upperNoiseVectors_measurable {m : ℕ}
    [MeasurableSpace (Queries E (Blocks m E))] [BorelSpace (Queries E (Blocks m E))]
    (k : Fin (queryVectorCount m)) : Measurable (fun p : Queries E (Blocks m E) => upperNoiseVectors p k) :=
  upperNoiseVector_measurable _

omit [MeasurableSpace E] [BorelSpace E] in
theorem upperNoiseVectors_lower_mem {m : ℕ} (p : Queries E (Blocks m E))
    (W : Submodule ℝ E) (h : ∀ k,upperNoiseVectors p k∈W) : ∀ j,p.snd j∈W := by
  intro j
  have hj := h (queryVectorEnumeration m (Sum.inr (Sum.inr j)))
  simpa only [upperNoiseVectors,Equiv.symm_apply_apply,upperNoiseVector] using hj

omit [MeasurableSpace E] [BorelSpace E] in
theorem upperNoiseVectors_macro_mem {m : ℕ} (p : Queries E (Blocks m E))
    (W : Submodule ℝ E) (h : ∀ k,upperNoiseVectors p k∈W) : p.fst.fst∈W := by
  have hj := h (queryVectorEnumeration m (Sum.inl ()))
  simpa only [upperNoiseVectors,Equiv.symm_apply_apply,upperNoiseVector] using hj

end Bilevel.ChiHierarchyExecution

