import LowRank.RectangularOracle

/-! Measurable rectangular matrix algorithms with adaptive two-sided
queries, early stopping, and a uniform upper bound on the query count. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

structure StoppingRectangularStage (a b : ℕ) (S : Type u) (O : Type v)
    [MeasurableSpace S] [MeasurableSpace O] where
  stop : MeasurableStateMap S Bool
  output : MeasurableStateMap S O
  query : MeasurableStateMap S (RectangularQuery a b)

def BoundedRectangularPolicy (a b : ℕ) (O : Type v) [MeasurableSpace O] :
    ℕ → (S : Type u) → [MeasurableSpace S] → Type (max u v)
  | 0, S, _ => MeasurableStateMap S O
  | n + 1, S, _ => StoppingRectangularStage a b S O ×
      BoundedRectangularPolicy a b O n (S × RectangularReply a b)

def BoundedRectangularPolicy.toProgram (a b : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] → BoundedRectangularPolicy a b O n S →
      S → OracleProgram (RectangularQuery a b) (RectangularReply a b) O
  | 0, _, _, policy, x => .done (policy.1 x)
  | n + 1, _, _, policy, x =>
      if policy.1.stop.1 x then .done (policy.1.output.1 x)
      else .ask (policy.1.query.1 x) (fun reply => policy.2.toProgram a b n (x, reply))

def runBoundedRectangular (a b : ℕ) {O : Type v} [MeasurableSpace O] (n : ℕ)
    {S : Type u} [MeasurableSpace S] (policy : BoundedRectangularPolicy a b O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) : O :=
  (policy.toProgram a b n x).eval (rectangularOracle A)

theorem runBoundedRectangular_step (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedRectangularPolicy a b O (n + 1) S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    runBoundedRectangular a b (n + 1) policy A x =
      if policy.1.stop.1 x then policy.1.output.1 x
      else runBoundedRectangular a b n policy.2 A (x, rectangularOracle A (policy.1.query.1 x)) := by
  cases h : policy.1.stop.1 x <;>
    simp [runBoundedRectangular, BoundedRectangularPolicy.toProgram, h, OracleProgram.eval]

theorem BoundedRectangularPolicy.budget_toProgram (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedRectangularPolicy a b O n S) (x : S) :
    (policy.toProgram a b n x).HasBudget n := by
  induction n generalizing S with
  | zero => trivial
  | succ n ih =>
      simp only [toProgram]
      split
      · trivial
      · exact fun reply => ih policy.2 (x, reply)

theorem BoundedRectangularPolicy.calls_le (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedRectangularPolicy a b O n S)
    (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    (policy.toProgram a b n x).calls (rectangularOracle A) ≤ n :=
  OracleProgram.calls_le_budget _ (policy.budget_toProgram a b n x)

theorem measurable_runBoundedRectangular (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedRectangularPolicy a b O n S) :
    Measurable (fun p : Matrix (Fin a) (Fin b) ℝ × S => runBoundedRectangular a b n policy p.1 p.2) := by
  induction n generalizing S with
  | zero => exact policy.2.comp measurable_snd
  | succ n ih =>
      simp only [runBoundedRectangular_step]
      apply Measurable.ite
      · exact (measurableSet_singleton true).preimage (policy.1.stop.2.comp measurable_snd)
      · exact policy.1.output.2.comp measurable_snd
      · exact (ih policy.2).comp (measurable_fst.prodMk (measurable_snd.prodMk
          ((measurable_rectangularOracle a b).comp (measurable_fst.prodMk
            (policy.1.query.2.comp measurable_snd)))))

def BoundedRectangularPolicy.Outputs (a b : ℕ) {O : Type v} [MeasurableSpace O] (P : O → Prop) :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] → BoundedRectangularPolicy a b O n S → Prop
  | 0, _, _, policy => ∀ x, P (policy.1 x)
  | n + 1, _, _, policy =>
      (∀ x, policy.1.stop.1 x = true → P (policy.1.output.1 x)) ∧
        BoundedRectangularPolicy.Outputs a b P n policy.2

theorem BoundedRectangularPolicy.Outputs.mono (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedRectangularPolicy a b O n S)
    {P Q : O → Prop} (hp : policy.Outputs a b P n) (hPQ : ∀ o, P o → Q o) :
    policy.Outputs a b Q n := by
  induction n generalizing S with
  | zero => exact fun x => hPQ _ (hp x)
  | succ n ih => exact ⟨fun x hx => hPQ _ (hp.1 x hx), ih policy.2 hp.2⟩

theorem runBoundedRectangular_property (a b n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedRectangularPolicy a b O n S)
    (P : O → Prop) (hp : policy.Outputs a b P n) (A : Matrix (Fin a) (Fin b) ℝ) (x : S) :
    P (runBoundedRectangular a b n policy A x) := by
  induction n generalizing S with
  | zero => exact hp x
  | succ n ih =>
      rw [runBoundedRectangular_step]
      split
      · rename_i hs
        exact hp.1 x hs
      · exact ih policy.2 hp.2 _

end
end LowRank
