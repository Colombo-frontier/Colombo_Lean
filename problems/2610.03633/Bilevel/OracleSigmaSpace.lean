import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Countable tagged state spaces for concrete oracle-machine dispatch. -/
noncomputable section
open MeasureTheory
namespace Bilevel.OracleSigma
variable {I : Type*} {S : I → Type*} [∀ i,MeasurableSpace (S i)]
  {Y O : Type*} [MeasurableSpace Y] [MeasurableSpace O]

theorem mk_measurable (i : I) : Measurable (Sigma.mk i : S i → Σ j,S j) :=
  Measurable.of_le_map (iInf_le _ i)

theorem elim_measurable (f : (Σ i,S i) → Y)
    (h : ∀ i,Measurable (fun x => f ⟨i,x⟩)) : Measurable f :=
  Measurable.of_comap_le (le_iInf (fun i => MeasurableSpace.comap_le_iff_le_map.mpr (h i)))

theorem mk_embedding (i : I) : MeasurableEmbedding (Sigma.mk i : S i → Σ j,S j) where
  injective := fun x y h => by cases h; rfl
  measurable := mk_measurable i
  measurableSet_image' := by
    intro s hs
    change MeasurableSet[⨅ j,(inferInstance : MeasurableSpace (S j)).map (Sigma.mk j)] (Sigma.mk i '' s)
    rw [MeasurableSpace.measurableSet_iInf]
    intro j
    change MeasurableSet (Sigma.mk j ⁻¹' (Sigma.mk i '' s))
    by_cases hji : j=i
    · subst j
      simpa only [Set.preimage_image_eq _ (show Function.Injective (Sigma.mk i : S i → Σ j,S j) from
        fun x y h => by cases h; rfl)] using hs
    · have he : Sigma.mk j ⁻¹' (Sigma.mk i '' s)=∅ := by
        ext x
        constructor
        · rintro ⟨y,hy,he⟩
          exact (hji (congrArg Sigma.fst he).symm).elim
        · simp
      rw [he]
      exact MeasurableSet.empty

theorem prod_elim_measurable [Countable I] (f : (Σ i,S i) × O → Y)
    (h : ∀ i,Measurable (fun z : S i × O => f (⟨i,z.1⟩,z.2))) : Measurable f := by
  intro t ht
  have he : f ⁻¹' t = ⋃ i,(Prod.map (Sigma.mk i) id) ''
      ((fun z : S i × O => f (⟨i,z.1⟩,z.2)) ⁻¹' t) := by
    ext z
    rcases z with ⟨⟨i,x⟩,o⟩
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨i,(x,o),hz,rfl⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨j,y,hy,he⟩
      exact he ▸ hy
  rw [he]
  exact MeasurableSet.iUnion (fun i => ((mk_embedding i).prodMap MeasurableEmbedding.id).measurableSet_image.mpr (h i ht))

end Bilevel.OracleSigma
