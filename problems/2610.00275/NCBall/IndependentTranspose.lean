import Mathlib.MeasureTheory.Constructions.Pi

/-! # Transposing a finite table of independent random variables -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NCBall

def flattenPiEquiv (ι κ E : Type*) [MeasurableSpace E] :
    (ι → κ → E) ≃ᵐ ((ι × κ) → E) where
  toFun z p := z p.1 p.2
  invFun z i k := z (i, k)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_lambda _ (fun p =>
    (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  measurable_invFun := measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun k => measurable_pi_apply (i, k)))

theorem flattenPiEquiv_law {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] :
    MeasurePreserving (flattenPiEquiv ι κ E)
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)))
      (Measure.pi (fun _ : ι × κ => μ)) := by
  classical
  refine ⟨(flattenPiEquiv ι κ E).measurable, ?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (flattenPiEquiv ι κ E).measurable (MeasurableSet.univ_pi hs)]
  have he : flattenPiEquiv ι κ E ⁻¹' pi univ s =
      pi univ (fun i => pi univ (fun k => s (i, k))) := by
    ext z
    simp only [mem_preimage, mem_univ_pi, flattenPiEquiv]
    exact Prod.forall
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => μ (s p))).symm

theorem independent_transpose_law {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : ι → κ → E => fun k i => z i k)
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)))
      (Measure.pi (fun _ : κ => Measure.pi (fun _ : ι => μ))) := by
  have h1 := flattenPiEquiv_law (ι := ι) (κ := κ) μ
  have h2 : MeasurePreserving (fun z : (ι × κ) → E => fun p : κ × ι => z (p.2, p.1))
      (Measure.pi (fun _ : ι × κ => μ)) (Measure.pi (fun _ : κ × ι => μ)) :=
    measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have h3 := (flattenPiEquiv_law (ι := κ) (κ := ι) μ).symm
  exact h3.comp (h2.comp h1)

end NCBall
