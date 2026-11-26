import Bilevel.PolishedFrozenCalls

/-! Immediate abort of the literal frozen code: the normalized remainder
keeps exactly the same result, call count and unused response stream. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenCode
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure CachedOracleCode

section Deterministic
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem stopped_after (Λ cap : ℝ) (x₀ : X) (G : ℕ → X) (n : ℕ)
    (hs : (CappedExecution.run Λ cap x₀ G n).stopped=true) (k : ℕ) :
    (CappedExecution.run Λ cap x₀ G (n+k)).stopped=true := by
  induction k with
  | zero => simpa only [Nat.add_zero] using hs
  | succ k ih =>
      change (CappedExecution.step Λ cap (CappedExecution.run Λ cap x₀ G (n+k)) (G (n+k))).stopped=true
      rw [CappedExecution.step,if_pos ih]
      exact ih

end Deterministic

variable {X Y Seed : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  (response : (X×Y) → Seed → FullResponse X Y)

/-- The actual oracle execution has already returned on an aborted prefix;
all finite syntactic suffixes perform zero further original calls. -/
theorem run_aborted_suffix (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n k : ℕ) (stream : ℕ → Seed)
    (hstop : (CappedExecution.run Λ cap x₀
      (eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)).1.1.1 n).stopped=true) :
    eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) ((),stream)=
      eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream) := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
      let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)
      have hs : (CappedExecution.run Λ cap x₀ z.1.1.1 (n+k)).stopped=true :=
        stopped_after Λ cap x₀ z.1.1.1 n hstop k
      have ha := iteration_aborted response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit
        (n+k) z.1.1 z.2 hs
      change (Procedure.combine
        ((eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) ((),stream)).1,
          (eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k))
            ((eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) ((),stream)).1.1,
              (eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) ((),stream)).2)).1),
        (eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k))
          ((eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) ((),stream)).1.1,
            (eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) ((),stream)).2)).2)=z
      rw [ih]
      change (Procedure.combine (z.1,(eval response
        (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) (z.1.1,z.2)).1),
          (eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit (n+k)) (z.1.1,z.2)).2)=z
      rw [ha]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact Prod.ext (Subsingleton.elim _ _) (Nat.add_zero _)
      · rfl

end Bilevel.PolishedFrozenCode
