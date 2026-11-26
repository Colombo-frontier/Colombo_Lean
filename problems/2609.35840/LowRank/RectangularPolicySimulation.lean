import LowRank.BoundedRectangularPolicy

/-! Compile a measurable rectangular stopping policy into a square policy
on the embedded input. The compiler receives only fixed embeddings and
observable history; its oracle program is exactly the one-call simulation. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v

def advanceRectangularMemory {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ)
    {S T : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (stage : StoppingRectangularStage a b T O) (mem : MeasurableStateMap S T) :
    MeasurableStateMap (S × (Fin d → ℝ)) (T × RectangularReply a b) :=
  ⟨fun x => (mem.1 x.1, decodeEmbeddedReply L R (stage.query.1 (mem.1 x.1)) x.2),
    (mem.2.comp measurable_fst).prodMk
      ((measurable_decodeEmbeddedReply L R).comp
        ((stage.query.2.comp (mem.2.comp measurable_fst)).prodMk measurable_snd))⟩

def compileRectangularPolicy {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ)
    {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S T : Type u} → [MeasurableSpace S] → [MeasurableSpace T] →
      BoundedRectangularPolicy a b O n T → MeasurableStateMap S T → BoundedTwoSidedPolicy d O n S
  | 0, _, _, _, _, policy, mem => ⟨fun x => policy.1 (mem.1 x), policy.2.comp mem.2⟩
  | n + 1, _, _, _, _, policy, mem =>
      ({stop := ⟨fun x => policy.1.stop.1 (mem.1 x), policy.1.stop.2.comp mem.2⟩
        output := ⟨fun x => policy.1.output.1 (mem.1 x), policy.1.output.2.comp mem.2⟩
        query := ⟨fun x => encodeEmbeddedQuery L R (policy.1.query.1 (mem.1 x)),
          (measurable_encodeEmbeddedQuery L R).comp (policy.1.query.2.comp mem.2)⟩},
       compileRectangularPolicy L R n policy.2 (advanceRectangularMemory L R policy.1 mem))

theorem compileRectangularPolicy_toProgram {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S T : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy a b O n T) (mem : MeasurableStateMap S T) (x : S) :
    (compileRectangularPolicy L R n policy mem).toProgram d n x =
      (policy.toProgram a b n (mem.1 x)).simulate (encodeEmbeddedQuery L R) (decodeEmbeddedReply L R) := by
  induction n generalizing S T with
  | zero => rfl
  | succ n ih =>
      simp only [compileRectangularPolicy, BoundedTwoSidedPolicy.toProgram,
        BoundedRectangularPolicy.toProgram]
      split_ifs
      · rfl
      · simp only [OracleProgram.simulate]
        congr 1
        funext reply
        exact ih policy.2 (advanceRectangularMemory L R policy.1 mem) (x, reply)

theorem compileRectangularPolicy_simulates {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S T : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy a b O n T) (mem : MeasurableStateMap S T)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    runBoundedTwoSided d n (compileRectangularPolicy L R n policy mem) A x =
      runBoundedRectangular a b n policy (L * A * Rᵀ) (mem.1 x) := by
  unfold runBoundedTwoSided runBoundedRectangular
  rw [compileRectangularPolicy_toProgram]
  exact OracleProgram.eval_simulate _ _ _ _ (embeddedOracle_reply L R A) _

theorem compileRectangularPolicy_calls {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S T : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy a b O n T) (mem : MeasurableStateMap S T)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    ((compileRectangularPolicy L R n policy mem).toProgram d n x).calls (twoSidedOracle A) =
      (policy.toProgram a b n (mem.1 x)).calls (rectangularOracle (L * A * Rᵀ)) := by
  rw [compileRectangularPolicy_toProgram]
  exact OracleProgram.calls_simulate _ _ _ _ (embeddedOracle_reply L R A) _

theorem compileRectangularPolicy_budget {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S T : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy a b O n T) (mem : MeasurableStateMap S T) (x : S) :
    ((compileRectangularPolicy L R n policy mem).toProgram d n x).HasBudget n := by
  rw [compileRectangularPolicy_toProgram]
  exact OracleProgram.budget_simulate _ _ (policy.budget_toProgram a b n (mem.1 x))

theorem compileRectangularPolicy_outputs {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S T : Type u} {O : Type v} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (policy : BoundedRectangularPolicy a b O n T) (mem : MeasurableStateMap S T)
    (P : O → Prop) (hP : policy.Outputs a b P n) :
    (compileRectangularPolicy L R n policy mem).Outputs d P n := by
  induction n generalizing S T with
  | zero => exact fun x => hP (mem.1 x)
  | succ n ih =>
      exact ⟨fun x hx => hP.1 (mem.1 x) hx,
        ih policy.2 (advanceRectangularMemory L R policy.1 mem) hP.2⟩

end
end LowRank
