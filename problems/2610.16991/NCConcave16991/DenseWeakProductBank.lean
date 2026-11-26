import NCConcave16991.DenseWeakBiasColumn
import NCConcave16991.DenseWeakEventTransfer
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The actual independent static bank and its rectangular posterior

All posterior masses below are obtained by conditioning the original finite
product law. No independence of a posterior is assumed.
-/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

attribute [local instance] Classical.propDecidable

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq D]

def pi (P : D → FiniteLaw I) : FiniteLaw (D → I) where
  mass := fun x ↦ ∏ d, (P d).mass (x d)
  nonneg := fun x ↦ Finset.prod_nonneg (fun d _ ↦ (P d).nonneg (x d))
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [fun d ↦ (P d).sum_one, Finset.prod_const_one]

def condition (P : FiniteLaw I) (E : Set I) (hE : 0 < P.eventMass E) : FiniteLaw I where
  mass := fun i ↦ (if i ∈ E then P.mass i else 0) / P.eventMass E
  nonneg := fun i ↦ div_nonneg (by split_ifs; exact P.nonneg i; rfl) hE.le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self hE.ne'

theorem eventMass_eq_probability (P : FiniteLaw I) (E : Set I)
    [MeasurableSpace I] [MeasurableSingletonClass I] : P.eventMass E = P.law.real E := by
  classical
  rw [event_probability]
  simp only [eventMass, Set.indicator_apply]

theorem condition_eventMass (P : FiniteLaw I) (E F : Set I) (hE : 0 < P.eventMass E) :
    (P.condition E hE).eventMass F = P.eventMass (E ∩ F) / P.eventMass E := by
  classical
  unfold eventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ E <;> by_cases hf : i ∈ F <;> simp [condition, eventMass, hi, hf]

def rectangle (E : D → Set I) : Set (D → I) := {x | ∀ d, x d ∈ E d}

theorem rectangle_indicator (P : D → FiniteLaw I) (E : D → Set I) (x : D → I) :
    (if x ∈ rectangle E then (pi P).mass x else 0) =
      ∏ d, if x d ∈ E d then (P d).mass (x d) else 0 := by
  classical
  by_cases h : ∀ d, x d ∈ E d
  · simp [rectangle, h, pi]
  · obtain ⟨d, hd⟩ := not_forall.mp h
    have hn : x ∉ rectangle E := h
    rw [if_neg hn]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ d) (if_neg hd)

theorem pi_rectangle_eventMass (P : D → FiniteLaw I) (E : D → Set I) :
    (pi P).eventMass (rectangle E) = ∏ d, (P d).eventMass (E d) := by
  classical
  unfold eventMass
  simp_rw [rectangle_indicator]
  exact (Fintype.prod_sum (fun d i ↦ if i ∈ E d then (P d).mass i else 0)).symm

theorem pi_rectangle_condition_mass (P : D → FiniteLaw I) (E : D → Set I)
    (hE : ∀ d, 0 < (P d).eventMass (E d)) (x : D → I) :
    ((pi P).condition (rectangle E)
      (by rw [pi_rectangle_eventMass]; exact Finset.prod_pos (fun d _ ↦ hE d))).mass x =
      (pi (fun d ↦ (P d).condition (E d) (hE d))).mass x := by
  classical
  change (if x ∈ rectangle E then (pi P).mass x else 0) /
    (pi P).eventMass (rectangle E) =
      ∏ d, ((P d).condition (E d) (hE d)).mass (x d)
  rw [rectangle_indicator, pi_rectangle_eventMass]
  exact (Finset.prod_div_distrib _ _).symm

theorem pi_rectangle_positive_iff (P : D → FiniteLaw I) (E : D → Set I) :
    0 < (pi P).eventMass (rectangle E) ↔ ∀ d, 0 < (P d).eventMass (E d) := by
  rw [pi_rectangle_eventMass]
  constructor
  · intro hp d
    by_contra hd
    have hz := le_antisymm (not_lt.mp hd) (eventMass_nonneg (P d) (E d))
    have he : (∏ a, (P a).eventMass (E a)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ d) hz
    linarith
  · intro h
    exact Finset.prod_pos (fun d _ ↦ h d)

end NCConcave16991.DenseWeakHiding.FiniteLaw

namespace NCConcave16991.DenseWeakHiding

abbrev ColumnBank (n m D : ℕ) := Fin D → EncodedColumn n m

def columnBankLaw (n m D : ℕ) (hm : m ≤ n) : FiniteLaw (ColumnBank n m D) :=
  FiniteLaw.pi (fun _ ↦ biasedColumnLaw n m hm)

theorem columnBankLaw_mass (n m D : ℕ) (hm : m ≤ n) (b : ColumnBank n m D) :
    (columnBankLaw n m D hm).mass b = ∏ d, (biasedColumnLaw n m hm).mass (b d) := rfl

end NCConcave16991.DenseWeakHiding
