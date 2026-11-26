import SecondOrder.FiniteStoppingLaw

open scoped Classical

namespace SecondOrder
noncomputable section
variable {S A : Type} [Fintype S] [Fintype A]

/-- Read every past test from one final finite history. The locality condition
means that a test before response t can only read the first t coefficients. -/
theorem finiteHistorySeen_tape_iff (a₀ : A) (E : ℕ → (ℕ → A) → Prop)
    (hE : ∀ n z z', (∀ t, t<n → z t=z' t) → (E n z ↔ E n z')) :
    ∀ n (h : FiniteHistory S A n),
    finiteHistorySeen (fun t h => E t (finiteHistoryTape a₀ t h)) n h ↔
      ∃ t, t≤n ∧ E t (finiteHistoryTape a₀ n h) := by
  intro n
  induction n with
  | zero => intro h; simp only [Nat.le_zero, exists_eq_left, finiteHistorySeen]
  | succ n ih =>
    intro h
    have he (t : ℕ) (ht : t≤n) : E t (finiteHistoryTape a₀ (n+1) h) ↔ E t (finiteHistoryTape a₀ n h.1) :=
      hE t _ _ (fun u hu => finiteHistoryTape_succ_lt a₀ n h u (by omega))
    change (_ ∨ _) ↔ _
    rw [ih]
    constructor
    · rintro (⟨t,ht,hh⟩ | hh)
      · exact ⟨t,by omega,(he t ht).mpr hh⟩
      · exact ⟨n+1,le_rfl,hh⟩
    · rintro ⟨t,ht,hh⟩
      by_cases hlast : t=n+1
      · subst t; exact Or.inr hh
      · exact Or.inl ⟨t,by omega,(he t (by omega)).mp hh⟩

end
end SecondOrder
