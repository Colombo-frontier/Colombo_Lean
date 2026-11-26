import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact target model for the supplied manuscript, lines 240–289.
The definitions `MainLowerBound`, `MainUpperBound`, and `MainTheorem` are
unproved targets, NOT theorem declarations. They are intentionally not
replaced by interfaces assuming the desired hard distribution exists.

The pointwise gap condition is equivalent to `f 0 - inf f ≤ 1` with a finite
infimum. All derivative budgets use the manuscript's directional convention.
An algorithm makes exactly T calls; early stopping is represented by padding
and ignoring answers. Queries and final outputs have no norm/span restriction.
-/

namespace MatchingBounds1005.Model

open MeasureTheory
open scoped ENNReal ContDiff

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Response (d : ℕ) := ℝ × Space d

def InFunctionClass {d : ℕ} (p : ℕ) (f : Space d → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x, f 0 - f x ≤ 1) ∧
    ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ x v : Space d, ‖v‖ = 1 → ∀ s t : ℝ,
      |iteratedDeriv q (fun u : ℝ => f (x + u • v)) t -
        iteratedDeriv q (fun u : ℝ => f (x + u • v)) s| ≤ |t - s|

noncomputable def oracle {d : ℕ} (f : Space d → ℝ) (x : Space d) : Response d :=
  (f x, gradient f x)

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

noncomputable def rate (ε : ℝ) : ℝ := ε ^ (-(5 / 3 : ℝ))
noncomputable def dimensionRate (ε : ℝ) : ℝ := ε ^ (-(47 / 3 : ℝ))

/-- One sampled instance law, chosen before every algorithm and private seed.
Pointwise class membership can be obtained by restricting to the norm event.
Measurability of success is required explicitly, not silently assumed. -/
def HardDistribution (p d T : ℕ) (ε : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
    (μ : Measure Ω) (_ : IsProbabilityMeasure μ) (F : Ω → Space d → ℝ),
      Measurable (fun z : Ω × Space d => oracle (F z.1) z.2) ∧
      (∀ sample, InFunctionClass p (F sample)) ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] [StandardBorelSpace Seed]
        (ν : Measure Seed) [IsProbabilityMeasure ν] (A : Algorithm d Seed),
        MeasurableSet {z : Ω × Seed | z.2 ∈ Success A (F z.1) ε T} ∧
        (μ.prod ν) {z : Ω × Seed | z.2 ∈ Success A (F z.1) ε T} ≤ (1 / 3 : ℝ≥0∞)

def MainLowerBound : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ d : ℕ,
      1 ≤ d ∧ (d : ℝ) ≤ C * dimensionRate ε ∧
      HardDistribution p d ⌊c * rate ε⌋₊ ε

def MainUpperBound : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ d : ℕ, 1 ≤ d →
      ∃ T : ℕ, ∃ A : Algorithm d Unit,
        (T : ℝ) ≤ C * rate ε * Real.log (2 / ε) ∧
        ∀ f : Space d → ℝ, InFunctionClass p f → () ∈ Success A f ε T

def RandomizedCap (p d : ℕ) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ (Seed : Type) (_ : MeasurableSpace Seed) (_ : StandardBorelSpace Seed)
    (ν : Measure Seed) (_ : IsProbabilityMeasure ν) (A : Algorithm d Seed),
      ∀ f : Space d → ℝ, InFunctionClass p f →
        (2 / 3 : ℝ≥0∞) ≤ ν (Success A f ε T)

def DeterministicCap (p d : ℕ) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ A : Algorithm d Unit, ∀ f : Space d → ℝ,
    InFunctionClass p f → () ∈ Success A f ε T

/-- The least successful integer cap, viewed in extended nonnegative reals.
The infimum of an empty set is infinity. -/
noncomputable def randomizedQueries (p d : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  sInf {x | ∃ T : ℕ, x = (T : ℝ≥0∞) ∧ RandomizedCap p d ε T}

noncomputable def deterministicQueries (p d : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  sInf {x | ∃ T : ℕ, x = (T : ℝ≥0∞) ∧ DeterministicCap p d ε T}

noncomputable def randomizedQueriesUniform (p : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ d : ℕ, randomizedQueries p (d + 1) ε

noncomputable def deterministicQueriesUniform (p : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ d : ℕ, deterministicQueries p (d + 1) ε

def MainMinimaxTheorem : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ENNReal.ofReal (c * rate ε) ≤ randomizedQueriesUniform p ε ∧
      randomizedQueriesUniform p ε ≤ deterministicQueriesUniform p ε ∧
      deterministicQueriesUniform p ε ≤ ENNReal.ofReal (C * rate ε * Real.log (2 / ε))

/-- The distributional strengthening and the complete numerical minimax
statement are both required for main-theorem acceptance. -/
def MainTheorem : Prop := MainLowerBound ∧ MainUpperBound ∧ MainMinimaxTheorem

theorem class_mono {d p q : ℕ} {f : Space d → ℝ}
    (hqp : q ≤ p) (hf : InFunctionClass p f) : InFunctionClass q f :=
  ⟨hf.1, hf.2.1, fun j hj hq => hf.2.2 j hj (hq.trans hqp)⟩

theorem bounded_below {d p : ℕ} {f : Space d → ℝ}
    (hf : InFunctionClass p f) : BddBelow (Set.range f) := by
  refine ⟨f 0 - 1, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := hf.2.1 x
  linarith

end MatchingBounds1005.Model
