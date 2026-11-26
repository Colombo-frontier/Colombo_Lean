import SecondOrder.LocalSampleEnumeration
import SecondOrder.IndependentDraws

open MeasureTheory

namespace SecondOrder
noncomputable section

def drawsFlatten {Ω : Type} (k : ℕ) : (n : ℕ) → Draws (Draws Ω k) n → Draws Ω (k*n)
  | 0, _ => PUnit.unit
  | n+1, w => drawsAppend (k*n) k (drawsFlatten k n w.1) w.2

theorem drawsFlatten_measurePreserving {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (k n : ℕ) :
    MeasurePreserving (drawsFlatten k n) (drawsLaw (drawsLaw μ k) n) (drawsLaw μ (k*n)) := by
  induction n with
  | zero => exact ⟨measurable_const,Measure.map_dirac measurable_const PUnit.unit⟩
  | succ n ih =>
    exact (drawsAppend_measurePreserving μ (k*n) k).comp (ih.prod (MeasurePreserving.id (drawsLaw μ k)))

def repeatedSamplePack {A S Ω : Type} (k : ℕ) (f : A → S × Draws Ω k)
    (n : ℕ) (w : Draws A n) : (Fin n → S) × Draws Ω (k*n) :=
  let u := drawsUnzip n (drawsMap f n w)
  (drawsVector id n u.1,drawsFlatten k n u.2)

theorem repeatedSamplePack_succ {A S Ω : Type} (k : ℕ) (f : A → S × Draws Ω k)
    (n : ℕ) (w : Draws A (n+1)) :
    repeatedSamplePack k f (n+1) w=
      (Fin.snoc (repeatedSamplePack k f n w.1).1 (f w.2).1,
        drawsAppend (k*n) k (repeatedSamplePack k f n w.1).2 (f w.2).2) := rfl

theorem repeatedSamplePack_measurePreserving {A S Ω : Type}
    [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace Ω]
    (κ : Measure A) (η : Measure S) (μ : Measure Ω)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    (k : ℕ) (f : A → S × Draws Ω k)
    (hf : MeasurePreserving f κ (η.prod (drawsLaw μ k))) (n : ℕ) :
    MeasurePreserving (repeatedSamplePack k f n) (drawsLaw κ n)
      ((Measure.map (drawsVector id n) (drawsLaw η n)).prod (drawsLaw μ (k*n))) := by
  have h₁ := drawsMap_measurePreserving hf n
  have h₂ := drawsUnzip_measurePreserving η (drawsLaw μ k) n
  have hs : MeasurePreserving (drawsVector id n) (drawsLaw η n)
      (Measure.map (drawsVector id n) (drawsLaw η n)) :=
    ⟨drawsVector_measurable measurable_id n,rfl⟩
  exact (hs.prod (drawsFlatten_measurePreserving μ k n)).comp (h₂.comp h₁)

end
end SecondOrder
