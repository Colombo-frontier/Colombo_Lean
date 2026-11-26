import NCConcave16991.DenseWeakFiniteLawMeasure
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

/-! # The actual uniform fixed-cardinality sign-column law -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

namespace FiniteLaw

def uniform (I : Type*) [Fintype I] [Nonempty I] : FiniteLaw I where
  mass := fun _ ↦ (Fintype.card I : ℝ)⁻¹
  nonneg := fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc]

end FiniteLaw

abbrev PositiveColumn (I : Type*) [Fintype I] (k : ℕ) := {A : Finset I // A.card = k}

variable {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}

theorem positiveColumn_nonempty (I : Type*) [Fintype I] [DecidableEq I]
    (k : ℕ) (hk : k ≤ Fintype.card I) : Nonempty (PositiveColumn I k) := by
  obtain ⟨A, _, hA⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset I)) (n := k) (by simpa using hk)
  exact ⟨⟨A, hA⟩⟩

def columnLaw (I : Type*) [Fintype I] [DecidableEq I]
    (k : ℕ) (hk : k ≤ Fintype.card I) : FiniteLaw (PositiveColumn I k) := by
  letI := positiveColumn_nonempty I k hk
  exact FiniteLaw.uniform (PositiveColumn I k)

theorem columnLaw_mass (hk : k ≤ Fintype.card I) (A : PositiveColumn I k) :
    (columnLaw I k hk).mass A = (Fintype.card (PositiveColumn I k) : ℝ)⁻¹ := rfl

def swapColumn (j l : I) (A : PositiveColumn I k) : PositiveColumn I k :=
  ⟨A.val.map (Equiv.swap j l).toEmbedding, by simpa only [Finset.card_map] using A.property⟩

theorem swapColumn_mem (j l i : I) (A : PositiveColumn I k) :
    i ∈ (swapColumn j l A).val ↔ Equiv.swap j l i ∈ A.val := by
  change i ∈ A.val.map (Equiv.swap j l).toEmbedding ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x, hx, hxi⟩
    have he : x = Equiv.swap j l i := by simpa using congrArg (Equiv.swap j l) hxi
    rwa [← he]
  · intro hi
    exact ⟨Equiv.swap j l i, hi, by simp⟩

theorem swapColumn_involutive (j l : I) : Function.Involutive (swapColumn (k := k) j l) := by
  intro A
  apply Subtype.ext
  ext i
  rw [swapColumn_mem, swapColumn_mem]
  simp

def swapColumnEquiv (j l : I) : PositiveColumn I k ≃ PositiveColumn I k where
  toFun := swapColumn j l
  invFun := swapColumn j l
  left_inv := swapColumn_involutive j l
  right_inv := swapColumn_involutive j l

def rowProbability (hk : k ≤ Fintype.card I) (j : I) : ℝ :=
  ∑ A : PositiveColumn I k, if j ∈ A.val then (columnLaw I k hk).mass A else 0

theorem rowProbability_eq (hk : k ≤ Fintype.card I) (j l : I) :
    rowProbability hk j = rowProbability hk l := by
  unfold rowProbability
  simp only [columnLaw_mass]
  apply Fintype.sum_equiv (swapColumnEquiv (k := k) j l)
  intro A
  change (if j ∈ A.val then (Fintype.card (PositiveColumn I k) : ℝ)⁻¹ else 0) =
    (if l ∈ (swapColumn j l A).val then (Fintype.card (PositiveColumn I k) : ℝ)⁻¹ else 0)
  simp only [swapColumn_mem, Equiv.swap_apply_right]

theorem rowProbability_sum (hk : k ≤ Fintype.card I) :
    (∑ j : I, rowProbability hk j) = (k : ℝ) := by
  unfold rowProbability
  rw [Finset.sum_comm]
  have hh (A : PositiveColumn I k) :
      (∑ j : I, if j ∈ A.val then (columnLaw I k hk).mass A else 0) =
        (k : ℝ) * (columnLaw I k hk).mass A := by
    rw [← Finset.sum_filter]
    have he : (Finset.univ.filter (fun j : I ↦ j ∈ A.val)) = A.val := by ext j; simp
    rw [he, Finset.sum_const, A.property, nsmul_eq_mul]
  simp_rw [hh]
  rw [← Finset.mul_sum, (columnLaw I k hk).sum_one, mul_one]

/-- Every row in the actual uniform fixed-cardinality column has exact
positive-sign probability k/card(I), obtained from actual row symmetry. -/
theorem rowProbability_exact (hk : k ≤ Fintype.card I) (j : I) :
    rowProbability hk j = (k : ℝ) / Fintype.card I := by
  haveI : Nonempty I := ⟨j⟩
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ l : I, rowProbability hk l) =
      (Fintype.card I : ℝ) * rowProbability hk j := by
    simp_rw [rowProbability_eq hk _ j]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply (eq_div_iff hc).2
  have he := rowProbability_sum hk
  nlinarith only [hs, he]

theorem columnLaw_row_probability (hk : k ≤ Fintype.card I) (j : I)
    [MeasurableSpace (PositiveColumn I k)] [MeasurableSingletonClass (PositiveColumn I k)] :
    (columnLaw I k hk).law.real {A | j ∈ A.val} = (k : ℝ) / Fintype.card I := by
  rw [FiniteLaw.event_probability]
  calc
    _ = rowProbability hk j := by
      unfold rowProbability
      apply Finset.sum_congr rfl
      intro A _
      by_cases h : j ∈ A.val <;> simp [Set.indicator_apply, h]
    _ = _ := rowProbability_exact hk j

end NCConcave16991.DenseWeakHiding
