import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Data.Fin.Tuple.Basic

/-! The precise algorithm model and target statement. `MainLowerBound` below
is a proposition definition. Its proof is `Model.main_lower_bound` in
`MainLowerBound.lean`; no axiom or placeholder is used. -/

namespace RandomizedFO2003.Model

open MeasureTheory
open scoped ENNReal

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Response (d : ℕ) := ℝ × Space d

noncomputable def oracle {d : ℕ} (f : Space d → ℝ) (x : Space d) : Response d :=
  (f x, gradient f x)

/-- The pairwise lower bound is equivalent to the initial-gap condition for
a real-valued function on this nonempty space, and also ensures a finite infimum. -/
def InFunctionClass {d : ℕ} (f : Space d → ℝ) (Δ L₁ L₂ : ℝ) : Prop :=
  ContDiff ℝ 2 f ∧
  (∀ x, f 0 - f x ≤ Δ) ∧
  (∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) ∧
  (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ L₂ * ‖x - y‖)

/-- All private randomness is sampled as a seed. Both queries and the terminal
output may be arbitrary measurable functions of it and of the complete history. -/
structure Algorithm (d : ℕ) (Seed : Type) [MeasurableSpace Seed] where
  query : (t : ℕ) → Seed → (Fin t → Response d) → Space d
  output : (t : ℕ) → Seed → (Fin t → Response d) → Space d
  query_measurable : ∀ t, Measurable (Function.uncurry (query t))
  output_measurable : ∀ t, Measurable (Function.uncurry (output t))

noncomputable def transcript {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (f : Space d → ℝ) (seed : Seed) :
    (t : ℕ) → Fin t → Response d
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (transcript A f seed t)
      (oracle f (A.query t seed (transcript A f seed t)))

def Success {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (f : Space d → ℝ) (ε : ℝ) (T : ℕ) : Set Seed :=
  {seed | ‖gradient f (A.output T seed (transcript A f seed T))‖ ≤ ε}

noncomputable def rate (ε Δ L₁ L₂ : ℝ) : ℝ :=
  Δ * L₁ ^ (1 / 2 : ℝ) * L₂ ^ (1 / 4 : ℝ) * ε ^ (-(7 / 4 : ℝ))

/-- Formal target, proved by `main_lower_bound`: the dimension is chosen
before the algorithm. The matching upper bound and full minimax result
are proved separately in `MainUpperBound` and `OracleComplexity`. -/
def MainLowerBound : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ ε Δ L₁ L₂ : ℝ, 0 < ε → 0 < Δ → 0 < L₁ → 0 < L₂ →
      ε ≤ c * L₁ ^ 2 / L₂ →
      C ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)) →
      ∀ T : ℕ, (T : ℝ) < c * rate ε Δ L₁ L₂ →
        ∃ d : ℕ, ∀ (Seed : Type) [MeasurableSpace Seed]
          (ν : Measure Seed) [IsProbabilityMeasure ν] (A : Algorithm d Seed),
          ∃ f : Space d → ℝ,
            InFunctionClass f Δ L₁ L₂ ∧ ν (Success A f ε T) < (2 / 3 : ℝ≥0∞)

end RandomizedFO2003.Model
