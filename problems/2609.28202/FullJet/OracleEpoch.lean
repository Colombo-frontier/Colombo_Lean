import FullJet.OracleProgram
import FullJet.TrustRegionEpoch

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n B : ℕ}

/-- Fix the next model point using stored data, then read both batches of
component replies. Each batch entry costs one oracle call. -/
noncomputable def epochStepProgram (hp : 1 ≤ p) (S : Fin n → JetPacket p E)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (batch : Fin B → Fin n) (state : EpochState E) :
    OracleProgram (Fin n × E) (JetPacket p E) (EpochState E) :=
  let b := state.offset + epochModelStep hp S M r hr state
  (OracleProgram.collect B (fun j => (batch j, center + state.offset))).bind fun oldReplies =>
    (OracleProgram.collect B (fun j => (batch j, center + b))).bind fun newReplies =>
      .done ⟨b, recursiveGradientUpdate hp S state.offset b state.gradient batch oldReplies newReplies⟩

theorem epochStepProgram_uses (hp : 1 ≤ p) (S : Fin n → JetPacket p E)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (batch : Fin B → Fin n) (state : EpochState E) :
    (epochStepProgram hp S center M r hr batch state).Uses (2 * B) := by
  unfold epochStepProgram
  rw [show 2 * B = B + (B + 0) by omega]
  apply OracleProgram.uses_bind (OracleProgram.collect_uses B _) _
  intro oldReplies
  exact OracleProgram.uses_bind (OracleProgram.collect_uses B _) _
    (fun newReplies => OracleProgram.Uses.done _)

theorem eval_epochStepProgram (hp : 1 ≤ p) (S : Fin n → JetPacket p E)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (batch : Fin B → Fin n) (state : EpochState E)
    (oracle : Fin n × E → JetPacket p E) :
    (epochStepProgram hp S center M r hr batch state).eval oracle =
      let b := state.offset + epochModelStep hp S M r hr state
      (⟨b, recursiveGradientUpdate hp S state.offset b state.gradient batch
        (fun j => oracle (batch j, center + state.offset))
        (fun j => oracle (batch j, center + b))⟩ : EpochState E) := by
  simp only [epochStepProgram, OracleProgram.eval_bind, OracleProgram.eval_collect, OracleProgram.eval]

/-- A sequence of model steps reuses the same saved snapshot. -/
noncomputable def epochStepsProgram (hp : 1 ≤ p) (S : Fin n → JetPacket p E)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) :
    (t : ℕ) → (Fin t → Fin B → Fin n) → OracleProgram (Fin n × E) (JetPacket p E) (EpochState E)
  | 0, _ => .done ⟨0, (n : ℝ)⁻¹ • ∑ i, packetGradient hp (S i)⟩
  | t + 1, samples => (epochStepsProgram hp S center M r hr t (Fin.init samples)).bind
      (epochStepProgram hp S center M r hr (samples (Fin.last t)))

theorem epochStepsProgram_uses (hp : 1 ≤ p) (S : Fin n → JetPacket p E)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    (epochStepsProgram hp S center M r hr t samples).Uses (t * (2 * B)) := by
  induction t with
  | zero =>
    simp only [Nat.zero_mul, epochStepsProgram]
    exact OracleProgram.Uses.done _
  | succ t ih =>
    simpa only [epochStepsProgram, Nat.add_mul, Nat.one_mul] using
      OracleProgram.uses_bind (ih (Fin.init samples)) _
        (fun state => epochStepProgram_uses hp S center M r hr _ state)

theorem eval_epochStepsProgram (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    (epochStepsProgram hp (fun i => fullJet p (f i) center) center M r hr t samples).eval
      (fun q => fullJet p (f q.1) q.2) = modelEpochRun hp f center M r hr t samples := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [epochStepsProgram, OracleProgram.eval_bind, ih, eval_epochStepProgram, modelEpochRun]

/-- One snapshot followed by t batches of actual two-point updates. No
component function is supplied to the program. -/
noncomputable def epochProgram (hp : 1 ≤ p) (center : E) (M r : ℝ) (hr : 0 ≤ r)
    (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    OracleProgram (Fin n × E) (JetPacket p E) (EpochState E) :=
  (OracleProgram.collect n (fun i => (i, center))).bind fun S =>
    epochStepsProgram hp S center M r hr t samples

def epochQueryCost (n m B : ℕ) : ℕ := n + m * (2 * B)

theorem epochProgram_uses (hp : 1 ≤ p) (center : E) (M r : ℝ) (hr : 0 ≤ r)
    (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    (epochProgram hp center M r hr t samples).Uses (epochQueryCost n t B) :=
  OracleProgram.uses_bind (OracleProgram.collect_uses n _) _
    (fun S => epochStepsProgram_uses hp S center M r hr t samples)

theorem eval_epochProgram (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (t : ℕ) (samples : Fin t → Fin B → Fin n) :
    (epochProgram hp center M r hr t samples).eval (fun q => fullJet p (f q.1) q.2) =
      modelEpochRun hp f center M r hr t samples := by
  simp only [epochProgram, OracleProgram.eval_bind, OracleProgram.eval_collect, eval_epochStepsProgram]

end FullJet
