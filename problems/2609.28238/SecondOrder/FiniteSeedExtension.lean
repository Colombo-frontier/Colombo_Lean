import SecondOrder.FiniteDrawsLaw

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {S : Type} [MeasurableSpace S]

theorem finCons_measurePreserving (N : ℕ) (η : Fin (N+1) → Measure S)
    [∀ i, IsProbabilityMeasure (η i)] :
    MeasurePreserving (fun w : S × (Fin N → S) => Fin.cons w.1 w.2)
      ((η 0).prod (Measure.pi (fun i : Fin N => η i.succ))) (Measure.pi η) := by
  convert (measurePreserving_piFinSuccAbove η 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => S) 0) using 1
  funext w
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero']
  rfl

theorem finSnoc_measurePreserving (η : Measure S) [IsProbabilityMeasure η] (N : ℕ) :
    MeasurePreserving (fun w : (Fin N → S) × S => Fin.snoc w.1 w.2)
      ((Measure.pi (fun _ : Fin N => η)).prod η) (Measure.pi (fun _ : Fin (N+1) => η)) := by
  have hh := (drawsVector_measurePreserving η (N+1)).comp
    ((vectorDraws_measurePreserving η N).prod (MeasurePreserving.id η))
  convert hh using 1
  funext w
  rcases w with ⟨v,t⟩
  simp only [Function.comp_apply,Prod.map_apply,drawsVector,drawsVector_vectorDraws,id_eq]

end
end SecondOrder
