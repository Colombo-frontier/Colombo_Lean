import LowRank.BoundedTwoSidedPolicy

/-! A measurable, fixed-budget Gram simulation of stopping two-sided queries
to H = I - W/L. Padding replies after the first stop do not affect the output. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

def advanceHardMemory {d : ℕ} {S T : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O] (L : ℝ)
    (stage : StoppingOracleStage d T O) (mem : MeasurableStateMap S T) :
    MeasurableStateMap (S × (Fin d → ℝ)) (T × (Fin d → ℝ)) :=
  ⟨fun p => (mem.1 p.1, (stage.query.1 (mem.1 p.1)).2 - L⁻¹ • p.2),
    (mem.2.comp measurable_fst).prodMk
      (((stage.query.2.comp (mem.2.comp measurable_fst)).snd).sub (measurable_const.smul measurable_snd))⟩

def padHardPolicy (d : ℕ) (L : ℝ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S T : Type u} → [MeasurableSpace S] → [MeasurableSpace T] →
      BoundedTwoSidedPolicy d O n T → MeasurableStateMap S T → AmbientOraclePolicy d n S
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n + 1, _, _, _, _, policy, mem =>
      (⟨fun x => (policy.1.query.1 (mem.1 x)).2, (policy.1.query.2.comp mem.2).snd⟩,
        padHardPolicy d L n policy.2 (advanceHardMemory L policy.1 mem))

def readPaddedHardOutput (d : ℕ) (L : ℝ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S T : Type u} → [MeasurableSpace S] → [MeasurableSpace T] →
      BoundedTwoSidedPolicy d O n T → MeasurableStateMap S T → OracleHistory d n S → O
  | 0, _, _, _, _, policy, mem, h => policy.1 (mem.1 h)
  | n + 1, _, _, _, _, policy, mem, h =>
      if policy.1.stop.1 (mem.1 (oracleHistorySeed d (n + 1) h)) then
        policy.1.output.1 (mem.1 (oracleHistorySeed d (n + 1) h))
      else readPaddedHardOutput d L n policy.2 (advanceHardMemory L policy.1 mem) h

theorem measurable_readPaddedHardOutput (d n : ℕ) (L : ℝ) {S T : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedTwoSidedPolicy d O n T) (mem : MeasurableStateMap S T) :
    Measurable (readPaddedHardOutput d L n policy mem) := by
  induction n generalizing S T with
  | zero => exact policy.2.comp mem.2
  | succ n ih =>
      change Measurable (fun h => if policy.1.stop.1 (mem.1 (oracleHistorySeed d (n + 1) h)) then
        policy.1.output.1 (mem.1 (oracleHistorySeed d (n + 1) h))
        else readPaddedHardOutput d L n policy.2 (advanceHardMemory L policy.1 mem) h)
      have hm := mem.2.comp (measurable_oracleHistorySeed d (n + 1) S)
      exact Measurable.ite ((measurableSet_singleton true).preimage (policy.1.stop.2.comp hm))
        (policy.1.output.2.comp hm) (ih policy.2 (advanceHardMemory L policy.1 mem))

theorem readPaddedHardOutput_property (d n : ℕ) (L : ℝ) {S T : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedTwoSidedPolicy d O n T) (mem : MeasurableStateMap S T) (P : O → Prop)
    (hp : policy.Outputs d P n) (h : OracleHistory d n S) :
    P (readPaddedHardOutput d L n policy mem h) := by
  induction n generalizing S T with
  | zero => exact hp (mem.1 h)
  | succ n ih =>
      simp only [readPaddedHardOutput]
      split
      · rename_i hs
        exact hp.1 _ hs
      · exact ih policy.2 (advanceHardMemory L policy.1 mem) hp.2 h

theorem padHardPolicy_simulates (d n : ℕ) (L : ℝ) {S T : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedTwoSidedPolicy d O n T) (mem : MeasurableStateMap S T)
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W) (x : S) :
    readPaddedHardOutput d L n policy mem (runAmbientOracle d n (padHardPolicy d L n policy mem) W x) =
      runBoundedTwoSided d n policy (hardMatrix L W) (mem.1 x) := by
  induction n generalizing S T with
  | zero => rfl
  | succ n ih =>
      rw [readPaddedHardOutput, oracleHistorySeed_runAmbientOracle, runBoundedTwoSided_step]
      split
      · rfl
      · simpa only [padHardPolicy, runAmbientOracle, advanceHardMemory,
          symmetric_twoSidedOracle (hardMatrix_symmetric L hW), hardMatrix_matvec] using
          ih policy.2 (advanceHardMemory L policy.1 mem) (x, W *ᵥ (policy.1.query.1 (mem.1 x)).2)

theorem padHardPolicy_calls (d n : ℕ) (L : ℝ) {S T : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedTwoSidedPolicy d O n T) (mem : MeasurableStateMap S T)
    (W : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    ((padHardPolicy d L n policy mem).toProgram d n x).calls (fun v => W *ᵥ v) = n :=
  AmbientOraclePolicy.calls_toProgram _ _ _ _ _

end
end LowRank

