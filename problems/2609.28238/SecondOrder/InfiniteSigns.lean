import SecondOrder.BatchTape
import SecondOrder.MixedSigns

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- A single infinite sequence of independent fair signs. -/
def infiniteSignLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

instance infiniteSignLaw_probability : IsProbabilityMeasure infiniteSignLaw := by
  unfold infiniteSignLaw
  infer_instance

def infiniteSignPrefix (M : ℕ) (w : ℕ → Bool) : Fin M → Bool := fun i => w i.val

theorem infiniteSignPrefix_measurable (M : ℕ) : Measurable (infiniteSignPrefix M) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)

/-- Every finite prefix has the exact finite uniform law used by the
finite execution estimates. -/
theorem infiniteSignPrefix_measurePreserving (M : ℕ) :
    MeasurePreserving (infiniteSignPrefix M) infiniteSignLaw (signLaw M) := by
  refine ⟨infiniteSignPrefix_measurable M, Measure.ext_of_singleton (fun v => ?_)⟩
  rw [Measure.map_apply (infiniteSignPrefix_measurable M) (measurableSet_singleton v)]
  let box : ℕ → Set Bool := fun i => {if hi : i < M then v ⟨i, hi⟩ else false}
  have he : infiniteSignPrefix M ⁻¹' {v} = Set.pi (Finset.range M) box := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · intro hw i hi
      have hh := congrFun hw ⟨i, hi⟩
      simpa [box, hi, infiniteSignPrefix] using hh
    · intro hw
      funext i
      simpa [box, i.isLt, infiniteSignPrefix] using hw i.val i.isLt
  rw [he, infiniteSignLaw, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp only [box, signLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp [ENNReal.inv_pow]

/-- Independent external randomness is preserved when restricting the signs. -/
theorem mixedSignPrefix_measurePreserving {Ξ : Type*} [MeasurableSpace Ξ]
    (η : Measure Ξ) [IsProbabilityMeasure η] (M : ℕ) :
    MeasurePreserving (fun w : Ξ × (ℕ → Bool) => (w.1, infiniteSignPrefix M w.2))
      (η.prod infiniteSignLaw) (η.prod (signLaw M)) :=
  (MeasurePreserving.id η).prod (infiniteSignPrefix_measurePreserving M)

end
end SecondOrder

