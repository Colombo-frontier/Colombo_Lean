import Bilevel.ChiVirtualBorelReply

/-! Concrete raw vector insertions for a full original ordinary-oracle
query. Public normal coordinates need no hidden-frame insertion. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyExecution
open PrimitiveGeometry ChiCarrier ChiExtension PartialLegendre

abbrev QueryVectorIndex (m : ℕ) := Unit ⊕ (Fin m ⊕ Fin m)

def queryVectorCount (m : ℕ) := Fintype.card (QueryVectorIndex m)

def queryVectorEnumeration (m : ℕ) : QueryVectorIndex m ≃ Fin (queryVectorCount m) := Fintype.equivFin _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def originalVector {m s : ℕ} (p : FullNormalVariables E (Blocks m E) (Normals s)) : QueryVectorIndex m → E
  | Sum.inl _ => p.fst.fst
  | Sum.inr (Sum.inl j) => p.fst.snd j
  | Sum.inr (Sum.inr j) => p.snd.fst j

def originalVectors {m s : ℕ} (p : FullNormalVariables E (Blocks m E) (Normals s))
    (k : Fin (queryVectorCount m)) : E := originalVector p ((queryVectorEnumeration m).symm k)

variable [MeasurableSpace E] [BorelSpace E]

theorem originalVector_measurable {m s : ℕ}
    [MeasurableSpace (FullNormalVariables E (Blocks m E) (Normals s))]
    [BorelSpace (FullNormalVariables E (Blocks m E) (Normals s))] (k : QueryVectorIndex m) :
    Measurable (fun p : FullNormalVariables E (Blocks m E) (Normals s) => originalVector p k) := by
  cases k with
  | inl _ => exact ((jointFstLinear.comp jointFstLinear :
      FullNormalVariables E (Blocks m E) (Normals s) →L[ℝ] E).continuous.measurable)
  | inr k =>
    cases k with
    | inl j => exact (((PiLp.proj 2 (fun _ : Fin m => E) j).comp
        (jointSndLinear.comp jointFstLinear) :
        FullNormalVariables E (Blocks m E) (Normals s) →L[ℝ] E).continuous.measurable)
    | inr j => exact (((PiLp.proj 2 (fun _ : Fin m => E) j).comp
        (jointFstLinear.comp jointSndLinear) :
        FullNormalVariables E (Blocks m E) (Normals s) →L[ℝ] E).continuous.measurable)

theorem originalVectors_measurable {m s : ℕ}
    [MeasurableSpace (FullNormalVariables E (Blocks m E) (Normals s))]
    [BorelSpace (FullNormalVariables E (Blocks m E) (Normals s))] (k : Fin (queryVectorCount m)) :
    Measurable (fun p : FullNormalVariables E (Blocks m E) (Normals s) => originalVectors p k) :=
  originalVector_measurable _

omit [MeasurableSpace E] [BorelSpace E] in
theorem originalVectors_lower_mem {m s : ℕ} (p : FullNormalVariables E (Blocks m E) (Normals s))
    (W : Submodule ℝ E) (h : ∀ k, originalVectors p k∈W) : p.snd∈normalKnown (fun _ : Fin m => W) s := by
  intro j
  have hj := h (queryVectorEnumeration m (Sum.inr (Sum.inr j)))
  simpa only [originalVectors,Equiv.symm_apply_apply,originalVector] using hj

omit [MeasurableSpace E] [BorelSpace E] in
theorem originalVectors_macro_mem {m s : ℕ} (p : FullNormalVariables E (Blocks m E) (Normals s))
    (W : Submodule ℝ E) (h : ∀ k, originalVectors p k∈W) : p.fst.fst∈W := by
  have hj := h (queryVectorEnumeration m (Sum.inl ()))
  simpa only [originalVectors,Equiv.symm_apply_apply,originalVector] using hj

end Bilevel.ChiHierarchyExecution
