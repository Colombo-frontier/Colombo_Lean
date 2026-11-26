import RandomizedFO2003.MarkedReadoutEvent
import RandomizedFO2003.MarkedPrefixGate

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [MeasurableSpace E]

/-- The added round reveals no new mark and queries the arbitrary terminal
output computed from the original complete history. -/
noncomputable def terminalRound {H : Type u} [MeasurableSpace H] (output : H → E) (ho : Measurable output) :
    MarkedRoundPolicy E H where
  authorized := fun _ => false
  measurable_authorized := measurable_const
  query := fun p => output p.1
  measurable_query := ho.comp measurable_fst

noncomputable def MarkedProgram.withTerminal : (t : ℕ) → {H : Type u} → [MeasurableSpace H] →
    MarkedProgram E t H → (output : ActionHistory E (markedActionCount t) H → E) →
      Measurable output → MarkedProgram E (t + 1) H
  | 0, _, _, _, output, ho => (terminalRound output ho, PUnit.unit)
  | t + 1, _, _, plan, output, ho => (plan.1, withTerminal t plan.2 output ho)

theorem MarkedProgram.withTerminal_last_unauthorized (t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E t H) (output : ActionHistory E (markedActionCount t) H → E)
    (ho : Measurable output) (p : ActionHistory E (markedActionCount (t + 1)) H) :
    (plan.withTerminal t output ho).authorizationTrace (t + 1) p (Fin.last t) = false := by
  induction t generalizing H with
  | zero => rfl
  | succ t ih => exact ih plan.2 output ho p

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

omit [BorelSpace E] in
theorem ActionProgram.run_seed (n : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : ActionProgram E n H) (U : E →L[ℝ] E) (h : H) :
    ActionHistory.seed E n (plan.run n U h) = h := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih => exact congrArg Prod.fst (ih plan.2 (h, plan.1.kind.action U (plan.1.vector h)))

/-- The recorded last latent query is exactly the inverse action on the
original arbitrary output. Earlier rounds retain their original policy. -/
theorem MarkedProgram.withTerminal_last_query (t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E t H) (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (output : ActionHistory E (markedActionCount t) H → E) (ho : Measurable output)
    (U : E →L[ℝ] E) (h : H) :
    markedQueryTrace E (t + 1)
      (((plan.withTerminal t output ho).compile A (t + 1) mark hm).run (markedActionCount (t + 1)) U h)
      (Fin.last t) = U.adjoint (output ((plan.compile A t mark hm).run (markedActionCount t) U h)) := by
  induction t generalizing H with
  | zero => rfl
  | succ t ih =>
    exact ih plan.2 (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3)) output ho
      ((plan.1.program A mark hm).run 3 U h)

open SpectralCoordinates Primitives

/-- Apply the simultaneous prefix event to the arbitrary terminal output,
without requiring that the output was an earlier query or had bounded norm. -/
theorem MarkedProgram.withTerminal_flat_output {J : ℕ} (K : Fin J → ℕ)
    (node r : Fin J → ℝ) (m t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram (BlockSpace K) t H) (mark : H → BlockSpace K) (hm : Measurable mark)
    (output : ActionHistory (BlockSpace K) (markedActionCount t) H → BlockSpace K)
    (ho : Measurable output) (U : BlockSpace K →L[ℝ] BlockSpace K) (h : H) (B α : ℝ)
    (hp : ((plan.withTerminal t output ho).compile (continuousDiagonal K node) (t + 1) mark hm).run
      (markedActionCount (t + 1)) U h ∈
        (plan.withTerminal t output ho).prefixFlatEvent K r m (t + 1) mark B α)
    (hdepth : markedQueryDepth (t + 1)
      ((plan.withTerminal t output ho).authorizationTrace (t + 1)
        (((plan.withTerminal t output ho).compile (continuousDiagonal K node) (t + 1) mark hm).run
          (markedActionCount (t + 1)) U h)) 0 (Fin.last t) ≤ m) :
    |radialReadout (direction K (mark h) r) B α
      (U.adjoint (output ((plan.compile (continuousDiagonal K node) t mark hm).run (markedActionCount t) U h)))| ≤
        1 / 4 := by
  have hq := hp (Fin.last t) hdepth
  rw [ActionProgram.run_seed, plan.withTerminal_last_query] at hq
  exact hq

end RandomizedFO2003.Rotations
