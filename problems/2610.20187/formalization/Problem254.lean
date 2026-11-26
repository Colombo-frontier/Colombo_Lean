import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
The actual OCO problem and statistical theorem targets of manuscript 254.
Definitions ending in `Statement` are propositions, NOT proofs of those
propositions. No regret guarantee is a field of the problem or learner.
Rounds use zero-based indexing. Losses are ambient functions, with derivatives
required only within the decision set, allowing lower-dimensional domains.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Paper254

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Loss (d : ℕ) := Space d → ℝ

instance spaceMeasurable (d : ℕ) : MeasurableSpace (Space d) := borel (Space d)
instance spaceBorel (d : ℕ) : BorelSpace (Space d) := ⟨rfl⟩

structure Domain (d : ℕ) (D : ℝ) where
  carrier : Set (Space d)
  nonempty : carrier.Nonempty
  compact : IsCompact carrier
  convex : Convex ℝ carrier
  diameter : ∀ x ∈ carrier, ∀ y ∈ carrier, ‖x - y‖ ≤ D

def ExpConcaveOn {d : ℕ} (η : ℝ) (W : Set (Space d)) (f : Loss d) : Prop :=
  ConcaveOn ℝ W (fun w => Real.exp (-η * f w))

structure AdmissibleLoss {d : ℕ} {D : ℝ} (W : Domain d D)
    (G η : ℝ) (f : Loss d) : Prop where
  expConcave : ExpConcaveOn η W.carrier f
  gradient : ∀ w ∈ W.carrier, ∃ g : Space d,
    HasGradientWithinAt f g W.carrier w ∧ ‖g‖ ≤ G

/-- A learner receives exactly the previous t loss functions; the return type
enforces properness. Neither comparator nor path budget is an input. -/
abbrev OnlineLearner {d : ℕ} {D : ℝ} (W : Domain d D) (T : ℕ) :=
  (t : Fin T) → (Fin t.val → Loss d) → W.carrier

def past {d T : ℕ} (f : Fin T → Loss d) (t : Fin T) : Fin t.val → Loss d :=
  fun j => f ⟨j.val, Nat.lt_trans j.isLt t.isLt⟩

def predictions {d T : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W T) (f : Fin T → Loss d) : Fin T → W.carrier :=
  fun t => A t (past f t)

def regret {d T : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W T) (f : Fin T → Loss d) (u : Fin T → W.carrier) : ℝ :=
  ∑ t, (f t (predictions A f t).val - f t (u t).val)

/-- Exactly T-1 Euclidean jumps; zero when T is zero or one. -/
def pathLength {d T : ℕ} {D : ℝ} {W : Domain d D} (u : Fin T → W.carrier) : ℝ :=
  ∑ t : Fin T, if h : 0 < t.val then
    ‖(u t).val - (u ⟨t.val - 1, by omega⟩).val‖ else 0

def logFactor (T : ℕ) : ℝ := 1 + Real.log (2 * (T : ℝ))
def curvature (D G η : ℝ) : ℝ := min (η / 2) (1 / (4 * G * D))

def curvedRate (d T : ℕ) (P : ℝ) : ℝ :=
  (d : ℝ) ^ (1 / 3 : ℝ) * logFactor T ^ (4 / 3 : ℝ) *
    (T : ℝ) ^ (1 / 3 : ℝ) * P ^ (2 / 3 : ℝ)

def upperFrontier (d T : ℕ) (P : ℝ) : ℝ :=
  d * logFactor T ^ 2 +
    min (curvedRate d T P) (min (Real.sqrt (T * (1 + P))) T)

def normalizedFrontier (d T : ℕ) (P : ℝ) : ℝ :=
  d + min ((d : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (1 / 3 : ℝ) * P ^ (2 / 3 : ℝ))
    (min (Real.sqrt (T * P)) T)

/-- Statistical assertion of Theorem 4.1, with the constants outside d,T,W.
The proof must construct a learner before seeing losses or a comparator. -/
def MainCurvedStatement : Prop :=
  ∀ D G η : ℝ, 0 < D → 0 < G → 0 < η →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ d T : ℕ, 0 < d → 0 < T → ∀ W : Domain d D,
  ∃ A : OnlineLearner W T,
  ∀ f : Fin T → Loss d, (∀ t, AdmissibleLoss W G η (f t)) →
  ∀ u : Fin T → W.carrier,
  pathLength u ≤ c * T / (Real.sqrt d * logFactor T ^ 2) →
  regret A f u ≤ C * (d * logFactor T ^ 2 + curvedRate d T (pathLength u))

/-- Statistical assertion of Corollary 4.2, without asymptotic notation. -/
def MainUpperStatement : Prop :=
  ∀ D G η : ℝ, 0 < D → 0 < G → 0 < η →
  ∃ C : ℝ, 0 < C ∧
  ∀ d T : ℕ, 0 < d → 0 < T → ∀ W : Domain d D,
  ∃ A : OnlineLearner W T,
  ∀ f : Fin T → Loss d, (∀ t, AdmissibleLoss W G η (f t)) →
  ∀ u : Fin T → W.carrier, regret A f u ≤ C * upperFrontier d T (pathLength u)

/-- Parameter-explicit clipped statistical bound. Requiring every feasible
scale is equivalent to bounding by the minimum, since this continuous scale
objective attains its minimum on the nonempty compact interval [D/T,D].
This file does not claim to have proved that analytic equivalence. -/
def ClippedUpperStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∀ D G η : ℝ, 0 < D → 0 < G → 0 < η →
  ∀ d T : ℕ, 0 < d → 0 < T → ∀ W : Domain d D,
  ∃ A : OnlineLearner W T,
  ∀ f : Fin T → Loss d, (∀ t, AdmissibleLoss W G η (f t)) →
  ∀ u : Fin T → W.carrier,
    regret A f u ≤ G * D * T ∧
    ∀ τ : ℝ, D / T ≤ τ → τ ≤ D →
      regret A f u ≤ C * (((d : ℝ) + 1) * logFactor T ^ 2 / curvature D G η +
        Real.sqrt ((d : ℝ) + 1) * logFactor T ^ 2 / (curvature D G η * τ) *
          pathLength u + curvature D G η * G ^ 2 * T * τ ^ 2)

def ballDomain (d : ℕ) : Domain d 1 where
  carrier := Metric.closedBall 0 (1/2)
  nonempty := ⟨0, by simp⟩
  compact := isCompact_closedBall _ _
  convex := convex_closedBall _ _
  diameter := by
    intro x hx y hy
    have hx' : ‖x‖ ≤ (1/2 : ℝ) := by simpa [Metric.mem_closedBall] using hx
    have hy' : ‖y‖ ≤ (1/2 : ℝ) := by simpa [Metric.mem_closedBall] using hy
    have ht := norm_sub_le x y
    linarith

def coordinateSquare {d : ℕ} (j : Fin d) (y : Bool) : Loss d :=
  fun w => (w j - (if y then 1 else -1)) ^ 2 / 2

def hardSequence {d T : ℕ} (s : Fin T → Fin d × Bool) : Fin T → Loss d :=
  fun t => coordinateSquare (s t).1 (s t).2

/-- A single random seed represents all internal random bits. Each action is
measurable in that seed, for every fixed past. The adversary cannot see it. -/
def SeedMeasurable {d T : ℕ} {D : ℝ} {W : Domain d D}
    {Ω : Type*} [MeasurableSpace Ω] (A : Ω → OnlineLearner W T) : Prop :=
  ∀ t history, Measurable (fun ω => (A ω t history).val)

/-- Statistical assertion of Theorem 5.1, written in its pointwise
for-every-learner form rather than using infimum/supremum. Constants are
uniform in d,T,P and in the randomized learner. Hard instances are chosen
outside the expectation, so the loss sequence and comparator are oblivious.
The universe parameter allows arbitrary measurable random seed spaces. -/
def MainLowerStatement.{u} : Prop :=
  ∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧
  ∀ d T : ℕ, 0 < d → 0 < T → c₀ * (d : ℝ)^2 ≤ T →
  ∀ P : ℝ, 0 ≤ P →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ A : Ω → OnlineLearner (ballDomain d) T, SeedMeasurable A →
  ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
    pathLength v ≤ P ∧
    c * normalizedFrontier d T P ≤ ∫ ω, regret (A ω) (hardSequence s) v ∂μ

theorem predictions_proper {d T : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W T) (f : Fin T → Loss d) (t : Fin T) :
    (predictions A f t).val ∈ W.carrier := (predictions A f t).property

theorem predictions_nonanticipating {d T : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W T) (f g : Fin T → Loss d) (t : Fin T)
    (h : ∀ s : Fin T, s.val < t.val → f s = g s) :
    predictions A f t = predictions A g t := by
  unfold predictions
  congr 1
  funext j
  exact h _ j.isLt

theorem pathLength_nonneg {d T : ℕ} {D : ℝ} {W : Domain d D}
    (u : Fin T → W.carrier) : 0 ≤ pathLength u := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs <;> positivity

theorem pathLength_constant {d T : ℕ} {D : ℝ} {W : Domain d D}
    (u : W.carrier) : pathLength (fun _ : Fin T => u) = 0 := by
  unfold pathLength
  apply Finset.sum_eq_zero
  intro t _
  split_ifs <;> simp

theorem regret_of_own_predictions {d T : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W T) (f : Fin T → Loss d) :
    regret A f (predictions A f) = 0 := by simp [regret]

end Paper254

#print axioms Paper254.predictions_nonanticipating
#print axioms Paper254.pathLength_nonneg
#print axioms Paper254.pathLength_constant
#print axioms Paper254.regret_of_own_predictions
