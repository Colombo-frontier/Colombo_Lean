import RandomizedFO2003.MatrixRequests

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable (E : Type) [MeasurableSpace E]

/-- A round decides authorization from the preceding history and chooses its
physical query after receiving the authorized (or zero) marked response. -/
structure MarkedRoundPolicy (H : Type u) [MeasurableSpace H] where
  authorized : H → Bool
  measurable_authorized : Measurable authorized
  query : H × E → E
  measurable_query : Measurable query

abbrev MarkedRoundHistory (H : Type u) := ActionHistory E 3 H
abbrev MarkedRoundAmbient (Ω : Type u) := AmbientPairHistory E 3 Ω

def markedActionCount : ℕ → ℕ
  | 0 => 0
  | t + 1 => markedActionCount t + 3

theorem markedActionCount_eq (t : ℕ) : markedActionCount t = 3 * t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [markedActionCount, ih, Nat.mul_add]

/-- A full finite adaptive policy. Its continuation sees all three actual
responses from the preceding round, as well as the entire older transcript. -/
def MarkedProgram : (t : ℕ) → (H : Type u) → [MeasurableSpace H] → Type u
  | 0, _, _ => PUnit
  | t + 1, H, _ => MarkedRoundPolicy E H × MarkedProgram t (MarkedRoundHistory E H)

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E]

noncomputable def markedVectorRequest {H : Type u} [MeasurableSpace H]
    (mark : H → E) (hm : Measurable mark) (policy : MarkedRoundPolicy E H) : ExposureRequest H E :=
  ⟨.response, fun h => if policy.authorized h = true then mark h else 0,
    hm.ite (policy.measurable_authorized (measurableSet_singleton true)) measurable_const⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem markedVectorRequest_legal {H : Type u} [MeasurableSpace H]
    (mark : H → E) (hm : Measurable mark) (policy : MarkedRoundPolicy E H)
    (A : Module.End ℝ E) (W : Submodule ℝ E) (h : H) :
    (LatentOperation.mark (policy.authorized h)).Legal A (mark h) W
      ((markedVectorRequest mark hm policy).vector h) := by
  cases hb : policy.authorized h <;>
    simp [markedVectorRequest, hb, LatentOperation.Legal, Submodule.mem_span_singleton_self]

noncomputable def MarkedRoundPolicy.program {H : Type u} [MeasurableSpace H]
    (policy : MarkedRoundPolicy E H) (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark) :
    ActionProgram E 3 H :=
  (markedVectorRequest mark hm policy,
    ⟨.query, policy.query, policy.measurable_query⟩, matrixResponseRequest A, PUnit.unit)

def MarkedRoundPolicy.operations {H : Type u} [MeasurableSpace H]
    (policy : MarkedRoundPolicy E H) (h : H) : Fin 3 → LatentOperation :=
  Fin.cons (.mark (policy.authorized h)) (Fin.cons .query (Fin.cons .matrix Fin.elim0))

noncomputable def MarkedProgram.compile (A : E →L[ℝ] E) : (t : ℕ) →
    {H : Type u} → [MeasurableSpace H] → MarkedProgram E t H →
    (mark : H → E) → Measurable mark → ActionProgram E (markedActionCount t) H
  | 0, _, _, _, _, _ => PUnit.unit
  | t + 1, _, _, plan, mark, hm =>
      (markedVectorRequest mark hm plan.1,
        ⟨.query, plan.1.query, plan.1.measurable_query⟩, matrixResponseRequest A,
        compile A t plan.2 (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3)))

theorem MarkedProgram.compile_succ {t : ℕ} {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E (t + 1) H) (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (U : E →L[ℝ] E) (h : H) :
    (plan.compile A (t + 1) mark hm).run (markedActionCount (t + 1)) U h =
      (plan.2.compile A t (mark ∘ ActionHistory.seed E 3)
        (hm.comp (ActionHistory.seed_measurable 3))).run (markedActionCount t) U
        ((plan.1.program A mark hm).run 3 U h) := rfl

/-- After a whole round the carried mark still has its original value. -/
theorem MarkedRoundPolicy.mark_preserved {H Ω : Type u} [MeasurableSpace H] [MeasurableSpace Ω]
    (policy : MarkedRoundPolicy E H) (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (d : ℕ) (F : Ω → ExposureFrame (Coordinates (d + 3)) E) (history : Ω → H)
    (p : MarkedRoundAmbient E Ω) :
    (mark ∘ ActionHistory.seed E 3)
      ((policy.program A mark hm).directAmbientTranscript d 3 F history p) =
        mark (history (AmbientPairHistory.seed E 3 p)) := by
  exact congrArg mark ((policy.program A mark hm).directAmbientTranscript_seed d 3 F history p)

noncomputable def MarkedProgram.ambientOperations (A : E →L[ℝ] E) (d : ℕ) :
    (t : ℕ) → {H Ω : Type u} → [MeasurableSpace H] → [MeasurableSpace Ω] →
    MarkedProgram E t H → (mark : H → E) → Measurable mark →
    (Ω → ExposureFrame (Coordinates (d + markedActionCount t)) E) → (Ω → H) →
    AmbientPairHistory E (markedActionCount t) Ω → Fin (markedActionCount t) → LatentOperation
  | 0, _, _, _, _, _, _, _, _, _, _ => Fin.elim0
  | t + 1, _, _, _, _, plan, mark, hm, F, history, p =>
      Fin.cons (.mark (plan.1.authorized (history (AmbientPairHistory.seed E (markedActionCount (t + 1)) p))))
        (Fin.cons .query (Fin.cons .matrix
          (ambientOperations A d t plan.2 (mark ∘ ActionHistory.seed E 3)
            (hm.comp (ActionHistory.seed_measurable 3))
            ((plan.1.program A mark hm).directAmbientFinalFrame (d + markedActionCount t) 3 F history)
            ((plan.1.program A mark hm).directAmbientTranscript (d + markedActionCount t) 3 F history) p)))

end RandomizedFO2003.Rotations
