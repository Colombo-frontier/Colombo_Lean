import SampleReuse.PersistentHandleLaw
import Mathlib.Probability.ProductMeasure

open MeasureTheory
namespace SampleReuse
noncomputable section

def iidSampleTapeLaw {Z : Type*} [MeasurableSpace Z] (p : PMF Z) : Measure (ℕ → Z) :=
  Measure.infinitePi (fun _ => p.toMeasure)

instance iidSampleTapeLaw_probability {Z : Type*} [MeasurableSpace Z] (p : PMF Z) :
    IsProbabilityMeasure (iidSampleTapeLaw p) := by
  unfold iidSampleTapeLaw
  infer_instance

def rangeFinEquiv (n : ℕ) : (Finset.range n) ≃ Fin n where
  toFun i := ⟨i.val,Finset.mem_range.mp i.property⟩
  invFun i := ⟨i.val,Finset.mem_range.mpr i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem iidSampleTapeLaw_prefix {Z : Type*} [MeasurableSpace Z] (p : PMF Z) (n : ℕ) :
    (iidSampleTapeLaw p).map (fun (tape : ℕ → Z) (i : Fin n) => tape i.val) =
      Measure.pi (fun _ : Fin n => p.toMeasure) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => Z) (rangeFinEquiv n)
  have hre : Measurable ((Finset.range n).restrict : (ℕ → Z) → (Finset.range n → Z)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  calc
    _ = ((iidSampleTapeLaw p).map (Finset.range n).restrict).map e := by
      rw [Measure.map_map e.measurable hre]
      rfl
    _ = (Measure.pi (fun _ : Finset.range n => p.toMeasure)).map e := by
      rw [iidSampleTapeLaw,Measure.infinitePi_map_restrict]
    _ = _ := Measure.pi_map_piCongrLeft (rangeFinEquiv n) (fun _ : Fin n => p.toMeasure)

theorem iidSampleTapeLaw_prefix_pmf {Z : Type*} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (p : PMF Z) (n : ℕ) :
    (iidSampleTapeLaw p).map (fun (tape : ℕ → Z) (i : Fin n) => tape i.val) =
      (SecondOrder.finitePiPMF (fun _ : Fin n => p)).toMeasure := by
  rw [iidSampleTapeLaw_prefix,SecondOrder.finitePiPMF_toMeasure]

end
end SampleReuse
