import SampleReuse.OracleRootBatch

/-! Syntactic access invariants of reply-driven programs imply invariants of
their actual compiled oracle traces. This verifies reserved-block access and
the separate gradient/Hessian call accounting for all batch branches. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

inductive QueriesSatisfy {Q Y O : Type*} (good : Q → Prop) : OracleProgram Q Y O → Prop
  | done (o : O) : QueriesSatisfy good (.done o)
  | request (q : Q) (k : Y → OracleProgram Q Y O) (hq : good q)
      (hk : ∀ y, QueriesSatisfy good (k y)) : QueriesSatisfy good (.request q k)

theorem QueriesSatisfy.advance {Q Y O : Type*} {good : Q → Prop}
    {p : OracleProgram Q Y O} (h : QueriesSatisfy good p) (y : Y) :
    QueriesSatisfy good (OracleProgram.advance p y) := by
  cases h with
  | done o => exact .done o
  | request q k hq hk => exact hk y

theorem QueriesSatisfy.run {Q Y O Z : Type*} {good : Q → Prop}
    {p : OracleProgram Q Y O} (h : QueriesSatisfy good p)
    (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z) (n : ℕ) :
    QueriesSatisfy good (OracleProgram.run q₀ reply zs p n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.advance _

theorem QueriesSatisfy.query {Q Y O : Type*} {good : Q → Prop}
    {p : OracleProgram Q Y O} (h : QueriesSatisfy good p) (q₀ : Q)
    (hunfinished : OracleProgram.finished p = false) : good (OracleProgram.query q₀ p) := by
  cases h with
  | done o => simp [OracleProgram.finished] at hunfinished
  | request q k hq hk => exact hq

theorem batch_queriesSatisfy {Q Y O : Type} (good : Q → Prop)
    (n : ℕ) (qs : Fin n → Q) (finish : (Fin n → Y) → O) (hq : ∀ i, good (qs i)) :
    QueriesSatisfy good (OracleProgram.batch n qs finish) := by
  induction n with
  | zero => exact .done _
  | succ n ih => exact .request _ _ (hq 0) (fun _ => ih _ _ (fun i => hq i.succ))

theorem compiled_query_satisfies {Ω : Type} {H d N : ℕ}
    {O : Type} (q₀ : PersistentQuery H d) (y₀ : PersistentReply d) (o₀ : O)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (p : OracleProgram (PersistentQuery H d) (PersistentReply d) O)
    (good : PersistentQuery H d → Prop) (hp : QueriesSatisfy good p)
    (hexact : OracleProgram.UsesExactly N p) (k : ℕ) (hk : k < N) :
    let alg := OracleProgram.algorithm q₀ y₀ o₀ p
    good (alg.query k (persistentRun alg.toQueryPolicy F tape k)) := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change good (OracleProgram.query q₀ (OracleProgram.readAnswers p _ k))
  rw [OracleProgram.algorithm_run]
  exact (hp.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape) k).query q₀
    ((hexact.run q₀ _ (fun _ => tape) k hk.le).finished_false (by omega))

theorem gradientBatchProgram_access {H d b : ℕ} (handles : Fin b → Fin H) (x y : Point d) :
    QueriesSatisfy (fun q : PersistentQuery H d => q.1 = true ∧ q.2.1 ∈ Set.range handles)
      (gradientBatchProgram handles x y) := by
  apply batch_queriesSatisfy
  intro i
  exact ⟨rfl, ⟨_, rfl⟩⟩

theorem hessianBatchProgram_access {H d b : ℕ} (handles : Fin b → Fin H) (x y : Point d) :
    QueriesSatisfy (fun q : PersistentQuery H d => q.1 = false ∧ q.2.1 ∈ Set.range handles)
      (hessianBatchProgram handles x y) := by
  apply batch_queriesSatisfy
  intro i
  exact ⟨rfl, ⟨_, rfl⟩⟩

theorem gradientRootProgram_access {H d b : ℕ} (handles : Fin b → Fin H) (x : Point d) :
    QueriesSatisfy (fun q : PersistentQuery H d => q.1 = true ∧ q.2.1 ∈ Set.range handles)
      (gradientRootProgram handles x) := by
  apply batch_queriesSatisfy
  intro i
  exact ⟨rfl, ⟨i, rfl⟩⟩

theorem hessianRootProgram_access {H d b : ℕ} (handles : Fin b → Fin H) (x : Point d) :
    QueriesSatisfy (fun q : PersistentQuery H d => q.1 = false ∧ q.2.1 ∈ Set.range handles)
      (hessianRootProgram handles x) := by
  apply batch_queriesSatisfy
  intro i
  exact ⟨rfl, ⟨i, rfl⟩⟩

theorem gradient_call_count_of_trace {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (N : ℕ)
    (htrace : ∀ k < N, (P.query k (persistentRun P F tape k)).1 = true) :
    gradientCallCount P F tape N = N ∧ hessianCallCount P F tape N = 0 := by
  have hg : gradientCallCount P F tape N = N := by
    unfold gradientCallCount
    trans ∑ k ∈ Finset.range N, (1 : ℕ)
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [htrace k (Finset.mem_range.mp hk), Bool.true_eq, if_true]
    · simp
  have hc := derivative_call_counts P F tape N
  exact ⟨hg, by omega⟩

theorem hessian_call_count_of_trace {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (N : ℕ)
    (htrace : ∀ k < N, (P.query k (persistentRun P F tape k)).1 = false) :
    gradientCallCount P F tape N = 0 ∧ hessianCallCount P F tape N = N := by
  have hg : gradientCallCount P F tape N = 0 := by
    unfold gradientCallCount
    apply Finset.sum_eq_zero
    intro k hk
    simp only [htrace k (Finset.mem_range.mp hk), Bool.false_eq_true, if_false]
  have hc := derivative_call_counts P F tape N
  exact ⟨hg, by omega⟩

theorem gradientBatchProgram_call_counts {Ω : Type} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x y : Point d) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (gradientBatchProgram handles x y)
    gradientCallCount alg.toQueryPolicy F tape (2*b) = 2*b ∧
      hessianCallCount alg.toQueryPolicy F tape (2*b) = 0 := by
  apply gradient_call_count_of_trace
  intro k hk
  exact (compiled_query_satisfies q₀ (0, 0) 0 F tape _ _
    (gradientBatchProgram_access handles x y) (gradientBatchProgram_exact_calls handles x y) k hk).1

theorem hessianBatchProgram_call_counts {Ω : Type} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x y : Point d) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (hessianBatchProgram handles x y)
    gradientCallCount alg.toQueryPolicy F tape (2*b) = 0 ∧
      hessianCallCount alg.toQueryPolicy F tape (2*b) = 2*b := by
  apply hessian_call_count_of_trace
  intro k hk
  exact (compiled_query_satisfies q₀ (0, 0) 0 F tape _ _
    (hessianBatchProgram_access handles x y) (hessianBatchProgram_exact_calls handles x y) k hk).1

end
end SampleReuse
