import SecondOrder.CurvatureRestartLocality

open scoped Classical

namespace SecondOrder
noncomputable section
variable {S A : Type} [Fintype S] [Fintype A]

theorem finiteHistoryBefore_tape_iff (a₀ : A) (E : ℕ → (ℕ → A) → Prop)
    (hE : ∀ n z z', (∀ t, t<n → z t=z' t) → (E n z ↔ E n z'))
    (n : ℕ) (h : FiniteHistory S A n) :
    finiteHistoryBefore (fun t h => E t (finiteHistoryTape a₀ t h)) n h ↔
      ∀ t, t<n → ¬E t (finiteHistoryTape a₀ n h) := by
  cases n with
  | zero => simp [finiteHistoryBefore]
  | succ n =>
    rw [finiteHistoryBefore, finiteHistorySeen_tape_iff a₀ E hE]
    constructor
    · intro hh t ht he
      exact hh ⟨t,by omega,(hE t _ _
        (fun u hu => finiteHistoryTape_succ_lt a₀ n h u (by omega))).mp he⟩
    · rintro hh ⟨t,ht,he⟩
      exact hh t (by omega) ((hE t _ _
        (fun u hu => finiteHistoryTape_succ_lt a₀ n h u (by omega))).mpr he)

/-- The marked event means that the first exit occurs before the horizon and
satisfies the success test, with every test read from the same final tape. -/
theorem finiteHistoryMarked_tape_iff (a₀ : A) (E F : ℕ → (ℕ → A) → Prop)
    (hE : ∀ n z z', (∀ t, t<n → z t=z' t) → (E n z ↔ E n z'))
    (hF : ∀ n z z', (∀ t, t<n → z t=z' t) → (F n z ↔ F n z')) :
    ∀ n (h : FiniteHistory S A n),
    finiteHistoryMarked (fun t h => E t (finiteHistoryTape a₀ t h))
        (fun t h => F t (finiteHistoryTape a₀ t h)) n h ↔
      ∃ t, t≤n ∧ (∀ u, u<t → ¬E u (finiteHistoryTape a₀ n h)) ∧
        F t (finiteHistoryTape a₀ n h) := by
  intro n
  induction n with
  | zero => simp [finiteHistoryMarked]
  | succ n ih =>
    intro h
    have he (t : ℕ) (ht : t≤n) : E t (finiteHistoryTape a₀ (n+1) h) ↔ E t (finiteHistoryTape a₀ n h.1) :=
      hE t _ _ (fun u hu => finiteHistoryTape_succ_lt a₀ n h u (by omega))
    have hf (t : ℕ) (ht : t≤n) : F t (finiteHistoryTape a₀ (n+1) h) ↔ F t (finiteHistoryTape a₀ n h.1) :=
      hF t _ _ (fun u hu => finiteHistoryTape_succ_lt a₀ n h u (by omega))
    have hb : (¬finiteHistorySeen (fun t h => E t (finiteHistoryTape a₀ t h)) n h.1) ↔
        ∀ t, t<n+1 → ¬E t (finiteHistoryTape a₀ (n+1) h) :=
      finiteHistoryBefore_tape_iff a₀ E hE (n+1) h
    rw [finiteHistoryMarked, ih, hb]
    constructor
    · rintro (⟨t,ht,hbefore,hlast⟩ | ⟨hbefore,hlast⟩)
      · exact ⟨t,by omega,fun u hu hh => hbefore u hu ((he u (by omega)).mp hh),(hf t ht).mpr hlast⟩
      · exact ⟨n+1,le_rfl,hbefore,hlast⟩
    · rintro ⟨t,ht,hbefore,hlast⟩
      by_cases hlasttime : t=n+1
      · subst t; exact Or.inr ⟨hbefore,hlast⟩
      · exact Or.inl ⟨t,by omega,fun u hu hh => hbefore u hu ((he u (by omega)).mpr hh),
          (hf t (by omega)).mp hlast⟩

end
end SecondOrder
