import MatchingBounds1005.AccessibleReferenceCompiler
import MatchingBounds1005.ScheduledHaarPrefix
import MatchingBounds1005.ReadoutCalendar

/-! The analyst inverse-query trace of the actual accessible compiler. The
private state never receives these inverse answers. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations

namespace MatchingBounds1005.ScheduledHaar
universe u
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
theorem RoundPolicy.seed_run (n : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : RoundPolicy E n H) (Q U : E →L[ℝ] E) (h : H) :
    ActionHistory.seed E (actionCount n) (plan.run n Q U h) = h := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih =>
      simp only [RoundPolicy.run, actionCount, ActionHistory.seed, ih]

omit [BorelSpace E] in
theorem RoundPolicy.roundQueryTrace_run_succ (n : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : RoundPolicy E (n + 1) H) (Q U : E →L[ℝ] E) (h : H) :
    roundQueryTrace E (n + 1) (plan.run (n + 1) Q U h) =
      Fin.cons (U.adjoint (plan.1.query (h, U plan.1.column)))
        (roundQueryTrace E n (plan.2.run n Q U
          (((h, U plan.1.column), U.adjoint (plan.1.query (h, U plan.1.column))),
            U (Q (U.adjoint (plan.1.query (h, U plan.1.column))))))) := by
  simp only [roundQueryTrace, RoundPolicy.run, ActionHistory.seed, RoundPolicy.seed_run]

theorem RoundPolicy.roundQueryTrace_reseed (n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : RoundPolicy E n H)
    (f : Ω → H) (hf : Measurable f) (Q U : E →L[ℝ] E) (h : Ω) :
    roundQueryTrace E n ((plan.reseed n f hf).run n Q U h) =
      roundQueryTrace E n (plan.run n Q U (f h)) := by
  induction n generalizing H Ω with
  | zero => rfl
  | succ n ih =>
      rw [RoundPolicy.roundQueryTrace_run_succ, RoundPolicy.roundQueryTrace_run_succ]
      simp only [RoundPolicy.reseed]
      have he := ih plan.2 (Prod.map (Prod.map (Prod.map f id) id) id)
        (((hf.prodMap measurable_id).prodMap measurable_id).prodMap measurable_id)
        (((h, U plan.1.column), U.adjoint (plan.1.query (f h, U plan.1.column))),
          U (Q (U.adjoint (plan.1.query (f h, U plan.1.column)))))
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun he j

end MatchingBounds1005.ScheduledHaar

namespace MatchingBounds1005.AccessibleReferenceCompiler
open ScheduledHaar
universe u
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type u} [MeasurableSpace S]

def inverseTrace : (w : List SourceKind) → Machine (E := E) (S := S) w →
    (E →L[ℝ] E) → (E →L[ℝ] E) → S → Fin w.length → E
  | [], _, _, _, _ => Fin.elim0
  | .disclose :: w, M, Q, U, s => Fin.cons 0
      (inverseTrace w M.2 Q U (M.1.2.next (s, U M.1.1)))
  | .query :: w, M, Q, U, s => Fin.cons (U.adjoint (M.1.1.point s))
      (inverseTrace w M.2 Q U (M.1.2.next (s, U (Q (U.adjoint (M.1.1.point s))))))
  | .candidate :: w, M, Q, U, s => Fin.cons (U.adjoint (M.1.1.point s))
      (inverseTrace w M.2 Q U (M.1.2.next (s, M.1.1.point s)))

/-- Exact pathwise inverse-query trace of both compiler layers. Candidate
coordinates occur only in this analyst trace, after the output is frozen. -/
theorem compile_inverseTrace (w : List SourceKind) (M : Machine (E := E) (S := S) w)
    {H : Type u} [MeasurableSpace H] (view : H → S) (hv : Measurable view)
    (Q U : E →L[ℝ] E) (h : H) :
    roundQueryTrace E w.length (((compile w M view hv).compile w).run w.length Q U h) =
      inverseTrace w M Q U (view h) := by
  induction w generalizing H with
  | nil => rfl
  | cons kind w ih =>
      have hr := RoundPolicy.roundQueryTrace_run_succ w.length
        ((compile (kind :: w) M view hv).compile (kind :: w)) Q U h
      cases kind <;>
        simpa only [compile, SourcePolicy.compile, inverseTrace,
          RoundPolicy.roundQueryTrace_reseed, map_zero, ih] using hr

end MatchingBounds1005.AccessibleReferenceCompiler

namespace MatchingBounds1005.ReadoutCalendar
open ScheduledHaar AccessibleReferenceCompiler GaussianVector
universe u
variable {S : Type u} [MeasurableSpace S] {d N : ℕ}

theorem inverseTrace_prepend (b : Fin N → Vec d) (update : Fin N → Update (E := Vec d) S)
    (xs : List (Fin N)) (w : List SourceKind) (M : Machine (E := Vec d) (S := S) w)
    (Q U : Vec d →L[ℝ] Vec d) (s : S) (j : Fin w.length) :
    inverseTrace (prependKinds xs w) (prependMachine b update xs w M) Q U s
      ⟨xs.length + j.val, by simp only [prependKinds, List.length_append, List.length_map]; omega⟩ =
        inverseTrace w M Q U (revealState b update U xs s) j := by
  induction xs generalizing s with
  | nil => simp only [prependKinds, prependMachine, revealState, List.length_nil, Nat.zero_add,
      List.map_nil, List.nil_append]
  | cons i xs ih =>
      have he : (⟨(i :: xs).length + j.val, by
          simp only [prependKinds, List.length_append, List.length_map]; omega⟩ :
          Fin (prependKinds (i :: xs) w).length) =
          (⟨xs.length + j.val, by
            simp only [prependKinds, List.length_append, List.length_map]; omega⟩ :
              Fin (prependKinds xs w).length).succ := by
        apply Fin.ext
        simp only [List.length_cons, Fin.val_succ]
        omega
      rw [he]
      exact ih ((update i).next (s, U (b i)))

end MatchingBounds1005.ReadoutCalendar
