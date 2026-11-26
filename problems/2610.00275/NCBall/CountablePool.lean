import Mathlib.Probability.ProductMeasure

/-! # Countably many independent reusable samples and their finite prefixes -/

noncomputable section
open MeasureTheory Set
namespace NCBall

def poolPrefix {Z : Type*} (K : ℕ) (z : ℕ → Z) : Fin K → Z := fun h => z h.val

theorem poolPrefix_measurable {Z : Type*} [MeasurableSpace Z] (K : ℕ) :
    Measurable (poolPrefix (Z := Z) K) :=
  measurable_pi_lambda _ (fun h => measurable_pi_apply h.val)

theorem poolPrefix_law {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (K : ℕ) :
    MeasurePreserving (poolPrefix K)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin K => μ)) := by
  let e : ↥(Finset.range K) ≃ Fin K :=
    { toFun := fun i => ⟨i.val, Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : MeasurePreserving (Finset.range K).restrict
      (Measure.infinitePi (fun _ : ℕ => μ))
      (Measure.pi (fun _ : ↥(Finset.range K) => μ)) :=
    ⟨measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  have h2 := measurePreserving_piCongrLeft (fun _ : Fin K => μ) e
  exact h2.comp h1

end NCBall
