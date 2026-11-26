import Bilevel.CachedOuterGoodEvent
import Bilevel.CappedAccuracy

/-! First failure is tested only at live calls. This is essential for the
literal immediate-abort algorithm, whose post-abort trace is never sampled. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedFrozenProcedure
open CachedOuterProcedure
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)

omit [CompleteSpace X] in
theorem live_prefix (Λ cap : ℝ) (x₀ : X) (G : ℕ → X) (n : ℕ)
    (hn : (CappedExecution.run Λ cap x₀ G n).stopped=false) :
    ∀ i≤n,(CappedExecution.run Λ cap x₀ G i).stopped=false := by
  induction n with
  | zero =>
    intro i hi
    have he : i=0 := by omega
    simpa only [he] using hn
  | succ n ih =>
    have hp := (CappedGoodEvent.step_live_iff Λ cap (CappedExecution.run Λ cap x₀ G n) (G n)).mp hn
    intro i hi
    by_cases he : i=n+1
    · simpa only [he] using hn
    · exact ih hp.1 i (by omega)

def liveTraceBad (Λ cap e : ℝ) (x₀ : X) (n : ℕ) : Set (State X Y) :=
  {s | ∃ i<n,(CappedExecution.run Λ cap x₀ s.1 i).stopped=false ∧
    e<‖s.1 i-gradient (P.hyperobjective P.canonicalResponse) (current Λ cap x₀ i s)‖}

def liveBad (Λ cap e rA η : ℝ) (x₀ : X) (n : ℕ) : Set (State X Y) :=
  {s | s∈liveTraceBad P Λ cap e x₀ n ∨
    ((CappedExecution.run Λ cap x₀ s.1 n).stopped=false ∧ n≠0 ∧
      ¬CachedAnchorProcedure.Certificate P s.2.1 rA η s.2.2)}

theorem liveBad_subset_bad (Λ cap e rA η : ℝ) (x₀ : X) (n : ℕ) :
    liveBad P Λ cap e rA η x₀ n⊆CachedOuterProcedure.bad P Λ cap e rA η x₀ n := by
  intro s hs
  rcases hs with ⟨i,hi,_,he⟩|⟨_,hn,hc⟩
  · exact Or.inl ⟨i,hi,he⟩
  · exact Or.inr ⟨hn,hc⟩

theorem liveBad_iff_bad_of_live (Λ cap e rA η : ℝ) (x₀ : X) (n : ℕ) (s : State X Y)
    (hs : (CappedExecution.run Λ cap x₀ s.1 n).stopped=false) :
    s∈liveBad P Λ cap e rA η x₀ n ↔ s∈CachedOuterProcedure.bad P Λ cap e rA η x₀ n := by
  constructor
  · intro hh
    exact liveBad_subset_bad P Λ cap e rA η x₀ n hh
  · rintro (⟨i,hi,he⟩|⟨hn,hc⟩)
    · exact Or.inl ⟨i,hi,live_prefix Λ cap x₀ s.1 n hs i hi.le,he⟩
    · exact Or.inr ⟨hs,hn,hc⟩

theorem liveBad_halted_succ (Λ cap e rA η : ℝ) (x₀ : X) (n : ℕ) (s : State X Y)
    (hs : (CappedExecution.run Λ cap x₀ s.1 n).stopped=true) :
    s∈liveBad P Λ cap e rA η x₀ (n+1) ↔ s∈liveBad P Λ cap e rA η x₀ n := by
  have hs' : (CappedExecution.run Λ cap x₀ s.1 (n+1)).stopped=true := by
    simp only [CappedExecution.run,CappedExecution.step,hs,ite_true]
  constructor
  · rintro (⟨i,hi,hl,he⟩|⟨hl,_,_⟩)
    · left
      refine ⟨i,?_,hl,he⟩
      by_contra hni
      have hi' : i=n := by omega
      rw [hi',hs] at hl
      cases hl
    · rw [hs'] at hl
      cases hl
  · rintro (⟨i,hi,hl,he⟩|⟨hl,_,_⟩)
    · exact Or.inl ⟨i,by omega,hl,he⟩
    · rw [hs] at hl
      cases hl

theorem initial_not_liveBad (Λ cap e rA η : ℝ) (x₀ : X) :
    initialState (Y:=Y) x₀∉liveBad P Λ cap e rA η x₀ 0 := by
  simp [liveBad,liveTraceBad]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

omit [BorelSpace Y] [SecondCountableTopology Y] in
theorem liveTraceBad_measurable (Λ cap e : ℝ) (x₀ : X) (n : ℕ) :
    MeasurableSet (liveTraceBad P Λ cap e x₀ n) := by
  unfold liveTraceBad
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i<n
  · simp only [hi,true_and]
    have hs := (CappedExecution.run_measurable Λ cap x₀ (fun j (s : State X Y) => s.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst) i).2.2
    exact (hs (measurableSet_singleton false)).inter
      (measurableSet_lt measurable_const (((measurable_pi_apply i).comp measurable_fst).sub
        ((P.gradient_hyperobjective_lipschitz P.canonicalResponse).continuous.measurable.comp
          (current_measurable Λ cap x₀ i))).norm)
  · simp only [hi,false_and,Set.setOf_false]
    exact MeasurableSet.empty

theorem liveBad_measurable (Λ cap e rA η : ℝ) (x₀ : X) (n : ℕ) :
    MeasurableSet (liveBad P Λ cap e rA η x₀ n) := by
  unfold liveBad
  apply (liveTraceBad_measurable P Λ cap e x₀ n).union
  have hs := (CappedExecution.run_measurable Λ cap x₀ (fun j (s : State X Y) => s.1 j)
    (fun j => (measurable_pi_apply j).comp measurable_fst) n).2.2
  apply (hs (measurableSet_singleton false)).inter
  by_cases hn : n=0
  · simp only [hn,ne_eq,not_true_eq_false,false_and,Set.setOf_false]
    exact MeasurableSet.empty
  · simp only [hn,ne_eq,not_false_eq_true,true_and]
    exact ((CachedAnchorProcedure.certificate_joint_measurable P rA η).preimage measurable_snd).compl

end Bilevel.PolishedFrozenProcedure
