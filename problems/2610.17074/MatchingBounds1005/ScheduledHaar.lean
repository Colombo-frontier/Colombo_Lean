import RandomizedFO2003.AmbientExposure

/-!
# Actual scheduled Haar transcripts

A round discloses one deterministic canonical column, accepts an arbitrary
measurable physical query, and returns its latent coordinates together with
the rotated quadratic matrix-vector product. The simulation below starts
from the actual Haar measure of one fixed rotation. It proves a product-law
representation; conditional invariance is not an assumption.

Several column disclosures at one manuscript time can be represented by
rounds with zero physical query. A round needing no disclosure uses column
zero. These syntactic conventions do not yet prove the scheduled-span
invariant, Gaussian-start representation, or the quantitative angle bound.
The independent starts in this module have the concrete spherical law.
-/

namespace MatchingBounds1005.ScheduledHaar

open MeasureTheory RandomizedFO2003.Rotations

universe u

def actionCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => actionCount n + 3

theorem actionCount_eq (n : ℕ) : actionCount n = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [actionCount, ih, Nat.mul_succ]

variable (E : Type) [MeasurableSpace E]

/-- A fixed canonical disclosure and a full-history measurable query after
that disclosure. The column itself does not depend on the realized history. -/
structure RoundRequest (H : Type u) [MeasurableSpace H] where
  column : E
  query : H × E → E
  measurable_query : Measurable query

def RoundPolicy : (n : ℕ) → (H : Type u) → [MeasurableSpace H] → Type u
  | 0, _, _ => PUnit
  | n + 1, H, _ => RoundRequest E H × RoundPolicy n (((H × E) × E) × E)

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- Direct execution of the specified scheduled oracle. In a round the
three appended responses are `U c`, `Uᵀ x`, and `U Q₀ Uᵀ x`. -/
noncomputable def RoundPolicy.run : (n : ℕ) → {H : Type u} → [MeasurableSpace H] →
    RoundPolicy E n H → (E →L[ℝ] E) → (E →L[ℝ] E) → H →
      ActionHistory E (actionCount n) H
  | 0, _, _, _, _, _, h => h
  | n + 1, _, _, plan, Q, U, h =>
      let h₁ := (h, U plan.1.column)
      let ξ := U.adjoint (plan.1.query h₁)
      run n plan.2 Q U ((h₁, ξ), U (Q ξ))

/-- Compile the concrete quadratic query into an inverse exposure followed
by a forward exposure of the already observed latent vector after `Q₀`. -/
noncomputable def RoundPolicy.compile (Q : E →L[ℝ] E) : (n : ℕ) →
    {H : Type u} → [MeasurableSpace H] → RoundPolicy E n H →
      ActionProgram E (actionCount n) H
  | 0, _, _, _ => PUnit.unit
  | n + 1, _, _, plan =>
      (⟨.response, fun _ => plan.1.column, measurable_const⟩,
        (⟨.query, plan.1.query, plan.1.measurable_query⟩,
          (⟨.response, fun h => Q h.2, Q.continuous.measurable.comp measurable_snd⟩,
            compile Q n plan.2)))

/-- Pointwise equality, not merely equality in distribution. It includes
zero and repeated queries and uses the same fixed operator throughout. -/
theorem RoundPolicy.run_eq_compiled (n : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : RoundPolicy E n H) (Q U : E →L[ℝ] E) (h : H) :
    plan.run n Q U h = (plan.compile Q n).run (actionCount n) U h := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih =>
      exact ih plan.2 (((h, U plan.1.column),
        U.adjoint (plan.1.query (h, U plan.1.column))),
          U (Q (U.adjoint (plan.1.query (h, U plan.1.column)))))

/-- Arbitrary full-history scheduled quadratic queries driven by one Haar
rotation have a concrete simulation by independent ambient sphere vectors.
The initial seed retains its arbitrary distribution. -/
theorem RoundPolicy.ambient_sphere_representation (d n : ℕ) {H : Type u}
    [MeasurableSpace H] (μ : Measure H) [SFinite μ]
    (Q : Coordinates (d + actionCount n) →L[ℝ] Coordinates (d + actionCount n))
    (plan : RoundPolicy (Coordinates (d + actionCount n)) n H) :
    ∃ transcript : ActionHistory (Coordinates (d + actionCount n)) (actionCount n) H →
        ActionHistory (Coordinates (d + actionCount n)) (actionCount n) H,
      Measurable transcript ∧
      (μ.prod (haarLaw (Coordinates (d + actionCount n)))).map
        (fun p => plan.run n Q (p.2 : Coordinates (d + actionCount n) →L[ℝ]
          Coordinates (d + actionCount n)) p.1) =
      (ambientHistoryLaw (Coordinates (d + actionCount n)) (actionCount n) μ).map transcript := by
  simpa only [RoundPolicy.run_eq_compiled] using
    (plan.compile Q n).ambient_transcript_representation d (actionCount n) μ

/-- The unused residual rotation is independent Haar after the actual
scheduled transcript. This is an exact measure-preserving decomposition. -/
theorem RoundPolicy.residual_haar_representation (d n : ℕ) {H : Type u}
    [MeasurableSpace H] (μ : Measure H) [SFinite μ]
    (Q : Coordinates (d + actionCount n) →L[ℝ] Coordinates (d + actionCount n))
    (plan : RoundPolicy (Coordinates (d + actionCount n)) n H) :
    ∃ (transcript : ExposureHistory d (actionCount n) H →
        ActionHistory (Coordinates (d + actionCount n)) (actionCount n) H)
      (residual : H × Rotation (Coordinates (d + actionCount n)) → Rotation (Coordinates d)),
      Measurable transcript ∧ Measurable residual ∧
      MeasurePreserving
        (fun p => (plan.run n Q (p.2 : Coordinates (d + actionCount n) →L[ℝ]
          Coordinates (d + actionCount n)) p.1, residual p))
        (μ.prod (haarLaw (Coordinates (d + actionCount n))))
        (((exposureHistoryLaw d (actionCount n) μ).map transcript).prod
          (haarLaw (Coordinates d))) := by
  simpa only [RoundPolicy.run_eq_compiled] using
    (plan.compile Q n).haar_transcript_representation d (actionCount n) μ

theorem RoundPolicy.run_measurable (d n : ℕ) {H : Type u} [MeasurableSpace H]
    (Q : Coordinates (d + actionCount n) →L[ℝ] Coordinates (d + actionCount n))
    (plan : RoundPolicy (Coordinates (d + actionCount n)) n H) :
    Measurable (fun p : H × Rotation (Coordinates (d + actionCount n)) =>
      plan.run n Q (p.2 : Coordinates (d + actionCount n) →L[ℝ]
        Coordinates (d + actionCount n)) p.1) := by
  obtain ⟨_, _, _, _, hp⟩ := plan.residual_haar_representation d n (0 : Measure H) Q
  exact hp.measurable.fst

/-- The simulation also preserves any measurable unqueried terminal output.
No oracle observation at the terminal candidate is inserted. -/
theorem RoundPolicy.terminal_output_representation (d n : ℕ) {H O : Type u}
    [MeasurableSpace H] [MeasurableSpace O] (μ : Measure H) [SFinite μ]
    (Q : Coordinates (d + actionCount n) →L[ℝ] Coordinates (d + actionCount n))
    (plan : RoundPolicy (Coordinates (d + actionCount n)) n H)
    (output : ActionHistory (Coordinates (d + actionCount n)) (actionCount n) H → O)
    (hout : Measurable output) :
    ∃ sample : ActionHistory (Coordinates (d + actionCount n)) (actionCount n) H → O,
      Measurable sample ∧
      (μ.prod (haarLaw (Coordinates (d + actionCount n)))).map
        (fun p => output (plan.run n Q (p.2 : Coordinates (d + actionCount n) →L[ℝ]
          Coordinates (d + actionCount n)) p.1)) =
      (ambientHistoryLaw (Coordinates (d + actionCount n)) (actionCount n) μ).map sample := by
  obtain ⟨tr, htr, heq⟩ := plan.ambient_sphere_representation d n μ Q
  refine ⟨output ∘ tr, hout.comp htr, ?_⟩
  have hp := congrArg (fun ν => ν.map output) heq
  dsimp only at hp
  rw [Measure.map_map hout (plan.run_measurable d n Q), Measure.map_map hout htr] at hp
  exact hp

end MatchingBounds1005.ScheduledHaar
