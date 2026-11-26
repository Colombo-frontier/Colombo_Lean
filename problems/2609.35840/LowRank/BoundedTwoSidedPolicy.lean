import LowRank.FixedBudgetPrograms

/-! Measurable square-matrix algorithms with adaptive stopping and a uniform
query budget. A Boolean query tag selects A or its transpose. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

structure StoppingOracleStage (d : ℕ) (S : Type u) (O : Type v)
    [MeasurableSpace S] [MeasurableSpace O] where
  stop : MeasurableStateMap S Bool
  output : MeasurableStateMap S O
  query : MeasurableStateMap S (Bool × (Fin d → ℝ))

def BoundedTwoSidedPolicy (d : ℕ) (O : Type v) [MeasurableSpace O] :
    ℕ → (S : Type u) → [MeasurableSpace S] → Type (max u v)
  | 0, S, _ => MeasurableStateMap S O
  | n + 1, S, _ => StoppingOracleStage d S O × BoundedTwoSidedPolicy d O n (S × (Fin d → ℝ))

def BoundedTwoSidedPolicy.toProgram (d : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] → BoundedTwoSidedPolicy d O n S →
      S → OracleProgram (Bool × (Fin d → ℝ)) (Fin d → ℝ) O
  | 0, _, _, policy, x => .done (policy.1 x)
  | n + 1, _, _, policy, x =>
      if policy.1.stop.1 x then .done (policy.1.output.1 x)
      else .ask (policy.1.query.1 x) (fun reply => policy.2.toProgram d n (x, reply))

def runBoundedTwoSided (d : ℕ) {O : Type v} [MeasurableSpace O] (n : ℕ)
    {S : Type u} [MeasurableSpace S] (policy : BoundedTwoSidedPolicy d O n S)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : S) : O :=
  (policy.toProgram d n x).eval (twoSidedOracle A)

theorem runBoundedTwoSided_step (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O (n + 1) S)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    runBoundedTwoSided d (n + 1) policy A x =
      if policy.1.stop.1 x then policy.1.output.1 x
      else runBoundedTwoSided d n policy.2 A (x, twoSidedOracle A (policy.1.query.1 x)) := by
  cases h : policy.1.stop.1 x <;>
    simp [runBoundedTwoSided, BoundedTwoSidedPolicy.toProgram, h, OracleProgram.eval]

theorem BoundedTwoSidedPolicy.budget_toProgram (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S) (x : S) :
    (policy.toProgram d n x).HasBudget n := by
  induction n generalizing S with
  | zero => trivial
  | succ n ih =>
      simp only [toProgram]
      split
      · trivial
      · exact fun reply => ih policy.2 (x, reply)

theorem BoundedTwoSidedPolicy.calls_le (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    (policy.toProgram d n x).calls (twoSidedOracle A) ≤ n :=
  OracleProgram.calls_le_budget _ (policy.budget_toProgram d n x)

theorem measurable_twoSidedOracle (d : ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × (Bool × (Fin d → ℝ)) =>
      twoSidedOracle p.1 p.2) := by
  unfold twoSidedOracle
  apply Measurable.ite
  · exact (measurableSet_singleton true).preimage measurable_snd.fst
  · apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    fun_prop
  · apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

theorem measurable_runBoundedTwoSided (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × S => runBoundedTwoSided d n policy p.1 p.2) := by
  induction n generalizing S with
  | zero => exact policy.2.comp measurable_snd
  | succ n ih =>
      simp only [runBoundedTwoSided_step]
      apply Measurable.ite
      · exact (measurableSet_singleton true).preimage (policy.1.stop.2.comp measurable_snd)
      · exact policy.1.output.2.comp measurable_snd
      · exact (ih policy.2).comp (measurable_fst.prodMk (measurable_snd.prodMk
          ((measurable_twoSidedOracle d).comp (measurable_fst.prodMk
            (policy.1.query.2.comp measurable_snd)))))

/-- A property required only of outputs on branches that actually stop. -/
def BoundedTwoSidedPolicy.Outputs (d : ℕ) {O : Type v} [MeasurableSpace O] (P : O → Prop) :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] → BoundedTwoSidedPolicy d O n S → Prop
  | 0, _, _, policy => ∀ x, P (policy.1 x)
  | n + 1, _, _, policy =>
      (∀ x, policy.1.stop.1 x = true → P (policy.1.output.1 x)) ∧
        BoundedTwoSidedPolicy.Outputs d P n policy.2

def oracleHistorySeed (d : ℕ) : (n : ℕ) → {S : Type u} → OracleHistory d n S → S
  | 0, _, h => h
  | n + 1, _, h => (oracleHistorySeed d n h).1

theorem BoundedTwoSidedPolicy.Outputs.mono (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S)
    {P Q : O → Prop} (hp : policy.Outputs d P n) (hPQ : ∀ o, P o → Q o) :
    policy.Outputs d Q n := by
  induction n generalizing S with
  | zero => exact fun x => hPQ _ (hp x)
  | succ n ih => exact ⟨fun x hx => hPQ _ (hp.1 x hx), ih policy.2 hp.2⟩

theorem runBoundedTwoSided_property (d n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy d O n S)
    (P : O → Prop) (hp : policy.Outputs d P n) (A : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    P (runBoundedTwoSided d n policy A x) := by
  induction n generalizing S with
  | zero => exact hp x
  | succ n ih =>
      rw [runBoundedTwoSided_step]
      split
      · rename_i hs
        exact hp.1 x hs
      · exact ih policy.2 hp.2 _

theorem measurable_oracleHistorySeed (d n : ℕ) (S : Type u) [MeasurableSpace S] :
    Measurable (oracleHistorySeed d n (S := S)) := by
  induction n generalizing S with
  | zero => exact measurable_id
  | succ n ih => exact (ih (S × (Fin d → ℝ))).fst

theorem oracleHistorySeed_runAmbientOracle (d n : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : AmbientOraclePolicy d n S) (W : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    oracleHistorySeed d n (runAmbientOracle d n policy W x) = x := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => exact congrArg Prod.fst (ih policy.2 (x, W *ᵥ policy.1.1 x))

end
end LowRank

