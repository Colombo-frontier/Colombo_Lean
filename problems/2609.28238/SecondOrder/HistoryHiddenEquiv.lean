import SecondOrder.KernelEntryIndependence

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

def historyJoinHidden : (n : ℕ) → H × FiniteHistory S A n → FiniteHistory (H × S) A n
  | 0, h => h
  | n+1, h => (historyJoinHidden n (h.1,h.2.1),h.2.2)

theorem historyJoinHidden_initial : ∀ n (h : H × FiniteHistory S A n),
    (finiteHistoryInitial n (historyJoinHidden n h)).1=h.1 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro h; exact ih (h.1,h.2.1)

theorem historyJoinHidden_public : ∀ n (h : H × FiniteHistory S A n),
    finiteHistoryMapInitial (Prod.snd : H × S → S) n (historyJoinHidden n h)=h.2 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro h; exact Prod.ext (ih (h.1,h.2.1)) rfl

theorem historyJoinHidden_pair : ∀ n (h : FiniteHistory (H × S) A n),
    historyJoinHidden n ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)=h := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro h; exact Prod.ext (ih h.1) rfl

theorem historyJoinHidden_measurable : ∀ n, Measurable (historyJoinHidden (H := H) (S := S) (A := A) n) := by
  intro n
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd

def historyHiddenEquiv (n : ℕ) : FiniteHistory (H × S) A n ≃ᵐ H × FiniteHistory S A n where
  toFun h := ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
  invFun := historyJoinHidden n
  left_inv := historyJoinHidden_pair n
  right_inv h := Prod.ext (historyJoinHidden_initial n h) (historyJoinHidden_public n h)
  measurable_toFun := historyHiddenPair_measurable n
  measurable_invFun := historyJoinHidden_measurable n

/-- An entry product law in hidden/public coordinates is the same actual
entry measure after joining those coordinates back into a complete history. -/
theorem entryMeasure_eq_join_map (n : ℕ) (η : Measure (FiniteHistory (H × S) A n))
    (ρ : Measure H) (ν : Measure (FiniteHistory S A n))
    (hη : η.map (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h))=ρ.prod ν) :
    η=(ρ.prod ν).map (historyJoinHidden n) := by
  rw [←hη,Measure.map_map (historyJoinHidden_measurable n) (historyHiddenPair_measurable n)]
  have he : (historyJoinHidden n) ∘ (fun h : FiniteHistory (H × S) A n =>
      ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h))=id := by
    funext h
    exact historyJoinHidden_pair n h
  rw [he,Measure.map_id]

end
end SecondOrder
