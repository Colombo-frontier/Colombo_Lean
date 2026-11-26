import LowRank.BoundedTwoSidedPolicy

/-! Pad a stopping two-sided policy to its budget on a symmetric matrix.
The output decoder ignores all replies after the first stopping decision. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

def padSymmetricPolicy (d : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
      BoundedTwoSidedPolicy d O n S → AmbientOraclePolicy d n S
  | 0, _, _, _ => PUnit.unit
  | n + 1, _, _, policy =>
      (⟨fun x => (policy.1.query.1 x).2, policy.1.query.2.snd⟩,
        padSymmetricPolicy d n policy.2)

def readPaddedSymmetricOutput (d : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
      BoundedTwoSidedPolicy d O n S → OracleHistory d n S → O
  | 0, _, _, policy, h => policy.1 h
  | n + 1, _, _, policy, h =>
      if policy.1.stop.1 (oracleHistorySeed d (n + 1) h) then
        policy.1.output.1 (oracleHistorySeed d (n + 1) h)
      else readPaddedSymmetricOutput d n policy.2 h

theorem measurable_readPaddedSymmetricOutput (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S) :
    Measurable (readPaddedSymmetricOutput d n policy) := by
  induction n generalizing S with
  | zero => exact policy.2
  | succ n ih =>
      change Measurable (fun h => if policy.1.stop.1 (oracleHistorySeed d (n + 1) h) then
        policy.1.output.1 (oracleHistorySeed d (n + 1) h)
        else readPaddedSymmetricOutput d n policy.2 h)
      have hm := measurable_oracleHistorySeed d (n + 1) S
      exact Measurable.ite ((measurableSet_singleton true).preimage (policy.1.stop.2.comp hm))
        (policy.1.output.2.comp hm) (ih policy.2)

theorem readPaddedSymmetricOutput_property (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S)
    (P : O → Prop) (hp : policy.Outputs d P n) (h : OracleHistory d n S) :
    P (readPaddedSymmetricOutput d n policy h) := by
  induction n generalizing S with
  | zero => exact hp h
  | succ n ih =>
      simp only [readPaddedSymmetricOutput]
      split
      · rename_i hs
        exact hp.1 _ hs
      · exact ih policy.2 hp.2 h

theorem padSymmetricPolicy_simulates (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S)
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W) (x : S) :
    readPaddedSymmetricOutput d n policy
      (runAmbientOracle d n (padSymmetricPolicy d n policy) W x) =
        runBoundedTwoSided d n policy W x := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      rw [readPaddedSymmetricOutput, oracleHistorySeed_runAmbientOracle, runBoundedTwoSided_step]
      split
      · rfl
      · simpa only [padSymmetricPolicy, runAmbientOracle, symmetric_twoSidedOracle hW] using
          ih policy.2 (x, W *ᵥ (policy.1.query.1 x).2)

theorem padSymmetricPolicy_calls (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S)
    (W : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    ((padSymmetricPolicy d n policy).toProgram d n x).calls (fun v => W *ᵥ v) = n :=
  AmbientOraclePolicy.calls_toProgram _ _ _ _ _

end
end LowRank
