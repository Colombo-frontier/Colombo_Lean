import NCConcave16991.DenseWeakBankChannel

/-! # Literal fixed-row fibres behind adaptive biased-column observations -/

noncomputable section

namespace NCConcave16991.DenseWeakHiding.RowExperiment

variable {n m D r : ℕ}

/-- A realized adaptive transcript determines a fixed queried row set and a
fixed positive subset in every column. The column's entire observation fibre
is exactly the corresponding static intersection constraint. -/
theorem columnFibre_eq_observation (E : RowExperiment (Fin n) (Fin D) (Fin 2) r)
    (h : Fin r → Fin D → Fin 2) (bank : ColumnBank n m D)
    (hbank : E.run columnBit bank = h) (d : Fin D) :
    E.columnFibre (columnBit (n := n) (m := m)) h d =
      observationEvent (n := n) (m := m) (E.observedRows h) ((bank d).2.val ∩ E.observedRows h) := by
  have hw := (run_eq_iff columnBit E bank h).mp hbank d
  rw [mem_columnFibre_iff] at hw
  ext a
  rw [mem_columnFibre_iff]
  change (∀ t, columnBit a (E.pathRow h t) = h t d) ↔
    a.2.val ∩ E.observedRows h = (bank d).2.val ∩ E.observedRows h
  constructor
  · intro ha
    ext i
    simp only [Finset.mem_inter]
    by_cases hi : i ∈ E.observedRows h
    · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hi
      have he : columnBit a i = columnBit (bank d) i := by
        rw [← ht, ha t, hw t]
      exact and_congr_left (fun _ ↦ by
        rw [← columnBit_zero_iff a i, ← columnBit_zero_iff (bank d) i, he])
    · simp [hi]
  · intro he t
    have hi : E.pathRow h t ∈ E.observedRows h :=
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
    have hm : E.pathRow h t ∈ a.2.val ↔ E.pathRow h t ∈ (bank d).2.val := by
      have he' := congrArg (fun S : Finset (Fin n) ↦ E.pathRow h t ∈ S) he
      simpa only [Finset.mem_inter, hi, and_true] using Iff.of_eq he'
    rw [← hw t]
    by_cases hp : E.pathRow h t ∈ (bank d).2.val
    · simp [columnBit, hp, hm.mpr hp]
    · have ha : E.pathRow h t ∉ a.2.val := fun ha ↦ hp (hm.mp ha)
      simp [columnBit, hp, ha]

end NCConcave16991.DenseWeakHiding.RowExperiment
