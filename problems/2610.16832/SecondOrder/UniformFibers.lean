import SecondOrder.FiniteMean
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- A finite map with equally sized nonempty fibers sends the uniform
law to the uniform law. We use explicit fiber equivalences, so no
probabilistic invariance assumption is required. -/
theorem uniformMean_of_fiber_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A → B) (b₀ : B)
    (hf : Function.Surjective f) (e : ∀ b, {a // f a = b} ≃ {a // f a = b₀})
    (X : B → ℝ) : uniformMean (fun a => X (f a)) = uniformMean X := by
  haveI : Nonempty {a // f a = b₀} := by obtain ⟨a, ha⟩ := hf b₀; exact ⟨⟨a, ha⟩⟩
  let E : A ≃ B × {a // f a = b₀} :=
    (Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd B {a // f a = b₀}))
  have hE (z : B × {a // f a = b₀}) : f (E.symm z) = z.1 := by
    exact ((e z.1).symm z.2).property
  have hh := uniformMean_equiv E.symm (fun a => X (f a))
  rw [uniformMean_prod] at hh
  simp only [hE, uniformMean_const] at hh
  exact hh.symm

theorem uniformMean_comm {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (X : A → B → ℝ) :
    uniformMean (fun a => uniformMean (fun b => X a b)) =
      uniformMean (fun b => uniformMean (fun a => X a b)) := by
  have he := uniformMean_equiv (Equiv.prodComm B A) (fun z : A × B => X z.1 z.2)
  simpa only [uniformMean_prod, Equiv.prodComm_apply] using he.symm

theorem uniformMeasure_real_indicator {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (S : Set A) :
    (PMF.uniformOfFintype A).toMeasure.real S =
      uniformMean (fun a => if a ∈ S then (1:ℝ) else 0) := by
  have hm : MeasurableSet S := (Set.toFinite S).measurableSet
  rw [show uniformMean (fun a => if a ∈ S then (1:ℝ) else 0) =
    ∫ a, S.indicator (fun _ => (1:ℝ)) a ∂(PMF.uniformOfFintype A).toMeasure from
      (PMF.integral_eq_sum _ _).symm]
  rw [integral_indicator_const _ hm]
  simp

end
end SecondOrder
