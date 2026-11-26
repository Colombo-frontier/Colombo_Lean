import Mathlib

/-!
# Full mathematical objects for the task006 paper

This file defines the actual sample-function and finite adaptive value-oracle
objects. It does not postulate an upper bound, lower bound, posterior law,
concentration theorem, or optimization guarantee.
-/

open MeasureTheory
open scoped BigOperators

namespace Task006.Full

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Transcript (N : ℕ) := Fin N → ℝ
abbrev QueryAction (d : ℕ) := Option (ℕ × Space d)

def actionToSum (d : ℕ) : QueryAction d → Unit ⊕ (ℕ × Space d)
  | none => Sum.inl ()
  | some q => Sum.inr q

/-- The usual disjoint-union sigma-algebra for an optional paid query. -/
instance queryActionMeasurableSpace (d : ℕ) : MeasurableSpace (QueryAction d) :=
  MeasurableSpace.comap (actionToSum d) inferInstance

def queryDomain (d : ℕ) (R : ℝ) : Set (Space d) := Metric.closedBall 0 (2 * R)
def outputDomain (d : ℕ) (R : ℝ) : Set (Space d) := Metric.closedBall 0 R

/-- A stochastic sample family with exactly the finite 3/2-moment contract.
The explicit integrability field expresses the finite expectation in the paper;
merely comparing Lean's totalized real integral would not express that condition. -/
structure SampleInstance (d : ℕ) (L R : ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  sample : Space d → Ω → ℝ
  modulus : Ω → ℝ
  measurable_sample : ∀ x ∈ queryDomain d R, Measurable (sample x)
  measurable_modulus : Measurable modulus
  nonneg_modulus : ∀ᵐ ω ∂μ, 0 ≤ modulus ω
  convex_sample : ∀ᵐ ω ∂μ, ConvexOn ℝ (queryDomain d R) (fun x => sample x ω)
  lipschitz_sample : ∀ᵐ ω ∂μ, ∀ x ∈ queryDomain d R, ∀ y ∈ queryDomain d R,
    |sample x ω - sample y ω| ≤ modulus ω * ‖x - y‖
  integrable_origin : Integrable (sample 0) μ
  integrable_moment : Integrable (fun ω => modulus ω ^ (3 / 2 : ℝ)) μ
  moment_bound : (∫ ω, modulus ω ^ (3 / 2 : ℝ) ∂μ) ≤ L ^ (3 / 2 : ℝ)

namespace SampleInstance

noncomputable def objective {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (I : SampleInstance d L R Ω μ) (x : Space d) : ℝ :=
  ∫ ω, I.sample x ω ∂μ

end SampleInstance

/-- An arbitrary finite adaptive query policy. It has no span or computation
restriction. Future transcript entries are ignored by `past_only`.
Legality is a separate predicate on real executions, not a counterfactual
restriction on the action policy. -/
structure OracleAlgorithm (d N : ℕ) (S : Type*) [MeasurableSpace S] where
  action : Fin N → S → Transcript N → QueryAction d
  action_measurable : ∀ t, Measurable (fun sh : S × Transcript N => action t sh.1 sh.2)
  past_only : ∀ t s h h', (∀ i, i.val < t.val → h i = h' i) → action t s h = action t s h'
  output : S → Transcript N → Space d
  output_measurable : Measurable (fun sh : S × Transcript N => output sh.1 sh.2)

namespace OracleAlgorithm

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

/-- Exact scalar reply from a fixed independent-sample tape. The status of an
unqueried handle is never returned by this oracle. -/
def scalarReply (F : Space d → Ω → ℝ) (tape : ℕ → Ω) : QueryAction d → ℝ
  | none => 0
  | some (handle, point) => F point (tape handle)

/-- Executing t paid slots, with `none` slots costing no scalar reply. -/
def runPrefix (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) : ℕ → Transcript N
  | 0 => fun _ => 0
  | t + 1 =>
    let h := A.runPrefix F tape seed t
    if ht : t < N then
      Function.update h ⟨t, ht⟩ (scalarReply F tape (A.action ⟨t, ht⟩ seed h))
    else h

def finalTranscript (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) : Transcript N := A.runPrefix F tape seed N

def executedAction (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : Fin N) : QueryAction d :=
  A.action t seed (A.runPrefix F tape seed t.val)

noncomputable def paidSlots (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) : Finset (Fin N) :=
  Finset.univ.filter (fun t => (A.executedAction F tape seed t).isSome)

noncomputable def handleSlots (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (handle : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun t => ∃ x, A.executedAction F tape seed t = some (handle, x))

def executionLegal (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (R : ℝ) : Prop :=
  (∀ t handle x, A.executedAction F tape seed t = some (handle, x) → x ∈ queryDomain d R) ∧
  (∀ handle, (A.handleSlots F tape seed handle).card ≤ 2) ∧
  A.output seed (A.finalTranscript F tape seed) ∈ outputDomain d R

/-- The same worst-case reply cap holds on every path, even under adaptive
stopping, because each slot contains at most one paid value. -/
theorem paid_reply_cap (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) : (A.paidSlots F tape seed).card ≤ N := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin N)

end OracleAlgorithm

end Task006.Full
