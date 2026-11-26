import NCConcave16991.DenseWeakColumnCompletion

/-! # The exact unread-row probability in an actual column completion -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

variable {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ} {R B : Finset I}

theorem unseenRows_card (R : Finset I) :
    Fintype.card (UnseenRows R) = Fintype.card I - R.card := by
  change Fintype.card {i : I // ¬(i ∈ R)} = _
  rw [Fintype.card_subtype_compl]
  congr 1
  simp [Fintype.card_subtype]

theorem remaining_card_bound [Nonempty (ObservedColumn k R B)] :
    k - B.card ≤ Fintype.card (UnseenRows R) := by
  obtain ⟨A⟩ := ‹Nonempty (ObservedColumn k R B)›
  have h := Finset.card_le_card (Finset.subset_univ (remainingColumn A).val)
  rw [(remainingColumn A).property, Finset.card_univ] at h
  exact h

theorem observed_rowProbability (hB : B ⊆ R) (hBk : B.card ≤ k)
    [Nonempty (ObservedColumn k R B)] (j : UnseenRows R) :
    (∑ A : ObservedColumn k R B,
      if j.val ∈ A.val.val then (Fintype.card (ObservedColumn k R B) : ℝ)⁻¹ else 0) =
      ((k - B.card : ℕ) : ℝ) / Fintype.card (UnseenRows R) := by
  have hc : Fintype.card (ObservedColumn k R B) =
      Fintype.card (PositiveColumn (UnseenRows R) (k - B.card)) :=
    Fintype.card_congr (columnCompletionEquiv hB hBk)
  have hp := rowProbability_exact (remaining_card_bound (k := k) (R := R) (B := B)) j
  unfold rowProbability at hp
  simp only [columnLaw_mass] at hp
  calc
    _ = ∑ C : PositiveColumn (UnseenRows R) (k - B.card),
        if j ∈ C.val then (Fintype.card (PositiveColumn (UnseenRows R) (k - B.card)) : ℝ)⁻¹ else 0 := by
      rw [hc]
      apply Fintype.sum_equiv (columnCompletionEquiv hB hBk)
      intro A
      change (if j.val ∈ A.val.val then _ else 0) =
        (if j ∈ (remainingColumn A).val then _ else 0)
      simp only [remainingColumn_mem]
    _ = _ := hp

/-- The literal conditional completion law, represented as an actual uniform
probability measure on all consistent full columns, has this exact probability. -/
theorem observed_column_row_probability (hB : B ⊆ R) (hBk : B.card ≤ k)
    [Nonempty (ObservedColumn k R B)] (j : UnseenRows R)
    [MeasurableSpace (ObservedColumn k R B)]
    [MeasurableSingletonClass (ObservedColumn k R B)] :
    (FiniteLaw.uniform (ObservedColumn k R B)).law.real {A | j.val ∈ A.val.val} =
      ((k - B.card : ℕ) : ℝ) / ((Fintype.card I - R.card : ℕ) : ℝ) := by
  rw [FiniteLaw.event_probability]
  have he : (∑ A : ObservedColumn k R B,
      {A | j.val ∈ A.val.val}.indicator (FiniteLaw.uniform (ObservedColumn k R B)).mass A) =
      ∑ A : ObservedColumn k R B,
        if j.val ∈ A.val.val then (Fintype.card (ObservedColumn k R B) : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro A _
    by_cases h : j.val ∈ A.val.val <;> simp [FiniteLaw.uniform, h]
  rw [he, observed_rowProbability hB hBk, unseenRows_card]

/-- This is conditioning the original static column law itself, rather than
assuming a completion distribution. The nonempty fibre is the observed data. -/
theorem conditional_column_row_probability (hk : k ≤ Fintype.card I)
    (hB : B ⊆ R) (hBk : B.card ≤ k) [Nonempty (ObservedColumn k R B)] (j : UnseenRows R)
    [MeasurableSpace (PositiveColumn I k)] [MeasurableSingletonClass (PositiveColumn I k)] :
    (columnLaw I k hk).law.real {A | A.val ∩ R = B ∧ j.val ∈ A.val} /
      (columnLaw I k hk).law.real {A | A.val ∩ R = B} =
      ((k - B.card : ℕ) : ℝ) / ((Fintype.card I - R.card : ℕ) : ℝ) := by
  let E : Set (PositiveColumn I k) := {A | A.val ∩ R = B}
  let F : Set (PositiveColumn I k) := {A | j.val ∈ A.val}
  letI : Nonempty (PositiveColumn I k) := positiveColumn_nonempty I k hk
  letI : Nonempty ↥E := ‹Nonempty (ObservedColumn k R B)›
  change (FiniteLaw.uniform (PositiveColumn I k)).law.real (E ∩ F) /
    (FiniteLaw.uniform (PositiveColumn I k)).law.real E = _
  rw [FiniteLaw.uniform_conditional_probability E F]
  let e : ↥E ≃ ObservedColumn k R B := Equiv.refl _
  have he : (FiniteLaw.uniform ↥E).law.real {A : E | A.val ∈ F} =
      (FiniteLaw.uniform (ObservedColumn k R B)).law.real {A | j.val ∈ A.val.val} :=
    FiniteLaw.uniform_event_equiv e {A | j.val ∈ A.val.val}
  rw [he]
  exact observed_column_row_probability hB hBk j

end NCConcave16991.DenseWeakHiding
