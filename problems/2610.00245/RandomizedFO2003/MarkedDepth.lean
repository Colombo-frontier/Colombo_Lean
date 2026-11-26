import RandomizedFO2003.MarkedLegality

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

def markedOperations : (t : ℕ) → (Fin t → Bool) → Fin (markedActionCount t) → LatentOperation
  | 0, _ => Fin.elim0
  | t + 1, a => Fin.cons (.mark (a 0))
      (Fin.cons .query (Fin.cons .matrix (markedOperations t (fun i => a i.succ))))

def markedDepth (t : ℕ) (a : Fin t → Bool) (m : ℕ) : ℕ :=
  LatentOperation.finalDepth (markedActionCount t) (markedOperations t a) m

@[simp] theorem markedDepth_zero (a : Fin 0 → Bool) (m : ℕ) : markedDepth 0 a m = m := rfl

theorem markedDepth_succ (t : ℕ) (a : Fin (t + 1) → Bool) (m : ℕ) :
    markedDepth (t + 1) a m = markedDepth t (fun i => a i.succ)
      (LatentOperation.matrix.nextDepth ((LatentOperation.mark (a 0)).nextDepth m)) := rfl

theorem markedDepth_positive (t : ℕ) (a : Fin t → Bool) (m : ℕ) (hm : 0 < m) :
    markedDepth t a m = m + t := by
  induction t generalizing m with
  | zero => simp
  | succ t ih =>
    have hs : LatentOperation.matrix.nextDepth ((LatentOperation.mark (a 0)).nextDepth m) = m + 1 := by
      cases m with
      | zero => omega
      | succ m => cases a 0 <;> simp [LatentOperation.nextDepth]
    rw [markedDepth_succ, hs, ih _ (m + 1) (by omega)]
    omega

theorem markedDepth_unauthorized (t : ℕ) (a : Fin t → Bool) (ha : ∀ i, a i = false) :
    markedDepth t a 0 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [markedDepth_succ, ha 0]
    exact ih (fun i => a i.succ) (fun i => ha i.succ)

/-- If the first authorization is at zero-based round `τ`, the final exposed
space contains exactly `t - τ + 1` marked powers. This includes the last matrix
response, which comes after that round's query. -/
theorem markedDepth_first_authorization (t : ℕ) (a : Fin t → Bool) (τ : Fin t)
    (hfirst : a τ = true) (hearlier : ∀ i : Fin t, i.val < τ.val → a i = false) :
    markedDepth t a 0 = t - τ.val + 1 := by
  induction t with
  | zero => exact τ.elim0
  | succ t ih =>
    revert hfirst hearlier
    refine Fin.cases ?_ (fun k => ?_) τ
    · intro hfirst hearlier
      rw [markedDepth_succ, hfirst]
      change markedDepth t (fun i => a i.succ) 2 = _
      rw [markedDepth_positive t _ 2 (by omega)]
      simp
      omega
    · intro hfirst hearlier
      have hzero : a 0 = false := hearlier 0 (by simp)
      rw [markedDepth_succ, hzero]
      change markedDepth t (fun i => a i.succ) 0 = _
      rw [ih (fun i => a i.succ) k hfirst (fun i hi => hearlier i.succ (by simpa using hi))]
      simp only [Fin.val_succ]
      omega

theorem markedDepth_le (t : ℕ) (a : Fin t → Bool) : markedDepth t a 0 ≤ t + 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [markedDepth_succ]
    cases h : a 0 with
    | false =>
      change markedDepth t (fun i => a i.succ) 0 ≤ t + 1 + 1
      exact (ih _).trans (by omega)
    | true =>
      change markedDepth t (fun i => a i.succ) 2 ≤ t + 1 + 1
      rw [markedDepth_positive t _ 2 (by omega)]
      omega

variable {E : Type} [MeasurableSpace E]

/-- Authorization decisions are recoverable from the actual ordinary
transcript, so the first-authorization event is a genuine history event. -/
def MarkedProgram.authorizationTrace : (t : ℕ) → {H : Type u} → [MeasurableSpace H] →
    MarkedProgram E t H → ActionHistory E (markedActionCount t) H → Fin t → Bool
  | 0, _, _, _, _ => Fin.elim0
  | t + 1, _, _, plan, p =>
      Fin.cons (plan.1.authorized (ActionHistory.seed E (markedActionCount (t + 1)) p))
        (authorizationTrace t plan.2 p)

theorem MarkedProgram.authorizationTrace_measurable (t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E t H) (i : Fin t) :
    Measurable (fun p => plan.authorizationTrace t p i) := by
  induction t generalizing H with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact plan.1.measurable_authorized.comp (ActionHistory.seed_measurable _)
    · exact ih plan.2 j

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

/-- The pathwise labels used by the legality proof agree with the measurable
authorization decisions extracted from the actual simulated transcript. -/
theorem MarkedProgram.ambientOperations_eq (d t : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : MarkedProgram E t H)
    (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (F : Ω → ExposureFrame (Coordinates (d + markedActionCount t)) E) (history : Ω → H)
    (p : AmbientPairHistory E (markedActionCount t) Ω) :
    plan.ambientOperations A d t mark hm F history p =
      markedOperations t (plan.authorizationTrace t
        ((plan.compile A t mark hm).directAmbientTranscript d (markedActionCount t) F history p)) := by
  induction t generalizing H Ω with
  | zero => rfl
  | succ t ih =>
    let round := plan.1.program A mark hm
    let F' := round.directAmbientFinalFrame (d + markedActionCount t) 3 F history
    let H' := round.directAmbientTranscript (d + markedActionCount t) 3 F history
    have hs := (plan.compile A (t + 1) mark hm).directAmbientTranscript_seed
      d (markedActionCount (t + 1)) F history p
    have ht := ih plan.2 (mark ∘ ActionHistory.seed E 3)
      (hm.comp (ActionHistory.seed_measurable 3)) F' H' p
    simp only [MarkedProgram.ambientOperations, MarkedProgram.authorizationTrace, markedOperations,
      Fin.cons_zero, Fin.cons_succ]
    rw [hs]
    exact congrArg (Fin.cons _) (congrArg (Fin.cons _) (congrArg (Fin.cons _) ht))

end RandomizedFO2003.Rotations
