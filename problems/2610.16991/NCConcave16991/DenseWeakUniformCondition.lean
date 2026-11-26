import NCConcave16991.DenseWeakColumn
import Mathlib.Data.Fintype.Card

/-! # Conditioning an actual finite uniform law on an event -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

set_option backward.isDefEq.respectTransparency false

variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

theorem uniform_event_probability (E : Set I) [DecidablePred (· ∈ E)] :
    (uniform I).law.real E = (Fintype.card E : ℝ) / Fintype.card I := by
  rw [event_probability]
  have he : (∑ i, E.indicator (uniform I).mass i) =
      ∑ i : I, if i ∈ E then (Fintype.card I : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i ∈ E <;> simp [uniform, h]
  rw [he, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun i : I ↦ i ∈ E)).card = Fintype.card E :=
    (Fintype.card_subtype (fun i : I ↦ i ∈ E)).symm
  rw [hc]
  rfl

def eventIntersectionEquiv (E F : Set I) :
    {i : E // i.val ∈ F} ≃ ↥(E ∩ F) where
  toFun := fun i ↦ ⟨i.val.val, i.val.property, i.property⟩
  invFun := fun i ↦ ⟨⟨i.val, i.property.1⟩, i.property.2⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The conditional probability under the actual uniform law is exactly the
probability under the actual uniform law on its nonempty observation fibre. -/
theorem uniform_conditional_probability (E F : Set I)
    [DecidablePred (· ∈ E)] [DecidablePred (· ∈ F)] [Nonempty E] :
    (uniform I).law.real (E ∩ F) / (uniform I).law.real E =
      (uniform E).law.real {i : E | i.val ∈ F} := by
  rw [uniform_event_probability, uniform_event_probability, uniform_event_probability]
  have hc : Fintype.card ↥{i : E | i.val ∈ F} = Fintype.card ↥(E ∩ F) :=
    Fintype.card_congr (eventIntersectionEquiv E F)
  rw [hc]
  have hI : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hE : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  exact congrArg (fun H : Fintype ↥(E ∩ F) ↦ (@Fintype.card ↥(E ∩ F) H : ℝ)) (Subsingleton.elim _ _)

theorem uniform_event_equiv {J : Type*} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] (e : I ≃ J) (E : Set J) :
    (uniform I).law.real (e ⁻¹' E) = (uniform J).law.real E := by
  classical
  rw [event_probability, event_probability]
  have hc : Fintype.card I = Fintype.card J := Fintype.card_congr e
  simp only [uniform]
  rw [hc]
  apply Fintype.sum_equiv e
  intro i
  by_cases h : e i ∈ E <;> simp [Set.indicator_apply, h]

end NCConcave16991.DenseWeakHiding.FiniteLaw
