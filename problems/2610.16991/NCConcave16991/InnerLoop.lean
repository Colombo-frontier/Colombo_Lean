import NCConcave16991.InnerAlgorithm
import NCConcave16991.UpperRecurrence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite independent seeds and the actual inner trajectory

A seed of length `k+1` is a seed of length `k` followed by a fresh uniform
index. Thus the law is a genuine finite product law. The trajectory is
recursively the projected stochastic step, and its expectation recursion is
derived by Fubini and the proved one-step descent.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.InnerAlgorithm

/-- A finite tuple of exactly `k` component identities, in chronological order. -/
@[reducible] def Seed (n : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Seed n k × Fin n

@[reducible] instance seedFintype (n : ℕ) : (k : ℕ) → Fintype (Seed n k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => by
    letI := seedFintype n k
    exact inferInstanceAs (Fintype (Seed n k × Fin n))

@[reducible] instance seedMeasurableSpace (n : ℕ) [MeasurableSpace (Fin n)] :
    (k : ℕ) → MeasurableSpace (Seed n k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k + 1 => by
    letI := seedMeasurableSpace n k
    exact inferInstanceAs (MeasurableSpace (Seed n k × Fin n))

instance seedMeasurableSingleton (n : ℕ) [MeasurableSpace (Fin n)]
    [MeasurableSingletonClass (Fin n)] : (k : ℕ) → MeasurableSingletonClass (Seed n k)
  | 0 => inferInstanceAs (MeasurableSingletonClass Unit)
  | k + 1 => by
    letI := seedMeasurableSingleton n k
    exact inferInstanceAs (MeasurableSingletonClass (Seed n k × Fin n))

variable {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]

/-- The actual product law of fresh independent uniform component identities. -/
def seedLaw : (k : ℕ) → Measure (Seed n k)
  | 0 => Measure.dirac ()
  | k + 1 => (seedLaw k).prod (uniformIndexLaw n)

instance seedLaw_probability : (k : ℕ) → IsProbabilityMeasure (seedLaw (n := n) k)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac (() : Unit)))
  | k + 1 => by
    letI := seedLaw_probability k
    exact inferInstanceAs (IsProbabilityMeasure ((seedLaw k).prod (uniformIndexLaw n)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- The actual finite-seed iteration, initialized at the anchor. -/
def trajectory (G : Fin n → E → E) (regularizer : E → E) (anchor : S) (bias : E)
    (η : ℝ) : (k : ℕ) → Seed n k → S
  | 0, _ => anchor
  | k + 1, ω => step S hne hclosed hconvex G regularizer anchor bias η
      (trajectory G regularizer anchor bias η k ω.1) ω.2

/-- Exact finite-law mean squared error of this actual trajectory. -/
def meanSquare (G : Fin n → E → E) (regularizer : E → E) (anchor : S) (bias : E)
    (η : ℝ) (star : E) (k : ℕ) : ℝ :=
  ∫ ω, ‖(trajectory S hne hclosed hconvex G regularizer anchor bias η k ω : E) - star‖ ^ 2
    ∂seedLaw k

/-- Exact finite-law mean of an energy along the actual trajectory. -/
def meanCost (G : Fin n → E → E) (regularizer : E → E) (anchor : S) (bias : E)
    (η : ℝ) (W : E → ℝ) (k : ℕ) : ℝ :=
  ∫ ω, W (trajectory S hne hclosed hconvex G regularizer anchor bias η k ω) ∂seedLaw k

 theorem meanSquare_initial (G : Fin n → E → E) (regularizer : E → E)
    (anchor : S) (bias : E) (η : ℝ) (star : E) :
    meanSquare S hne hclosed hconvex G regularizer anchor bias η star 0 = ‖(anchor : E) - star‖ ^ 2 := by
  simp [meanSquare, seedLaw, trajectory]

 theorem meanSquare_nonneg (G : Fin n → E → E) (regularizer : E → E)
    (anchor : S) (bias : E) (η : ℝ) (star : E) (k : ℕ) :
    0 ≤ meanSquare S hne hclosed hconvex G regularizer anchor bias η star k :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-- The exact finite-law recursion is derived from fresh independent samples and the actual step. -/
theorem meanSquare_recursion {G : Fin n → E → E} (regularizer : E → E)
    {L μ : ℝ} (hL : 0 ≤ L) (hAS : AveragedSmooth G S L)
    (anchor : S) (bias : E) {η : ℝ} (hη : 0 < η) (hsmall : 11 * η * L ^ 2 ≤ μ)
    (star : S)
    (hstar : VariationalInequality.IsSolution S (fun w ↦ operator G regularizer w + bias) star)
    (W : E → ℝ) (Vstar : ℝ)
    (hLip : ∀ z ∈ S, ‖operator G regularizer z - operator G regularizer star‖ ≤ 3 * L * ‖z - star‖)
    (hMono : ∀ z ∈ S, W z ≤ ⟪operator G regularizer z - operator G regularizer star, z - star⟫_ℝ)
    (hcoercive : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ W z)
    (hanchor : ‖(star : E) - anchor‖ ^ 2 ≤ Vstar) (k : ℕ) :
    meanSquare S hne hclosed hconvex G regularizer anchor bias η star (k + 1) ≤
      meanSquare S hne hclosed hconvex G regularizer anchor bias η star k -
        η * meanCost S hne hclosed hconvex G regularizer anchor bias η W k +
          2 * η ^ 2 * L ^ 2 * Vstar := by
  let z := trajectory S hne hclosed hconvex G regularizer anchor bias η k
  have hp (ω : Seed n k) := step_descent S hne hclosed hconvex regularizer hL hAS
    (anchor : E) bias anchor.property hη hsmall (z ω) star hstar (W (z ω)) Vstar
    (hLip (z ω) (z ω).property) (hMono (z ω) (z ω).property)
    (hcoercive (z ω) (z ω).property) hanchor
  have hi := integral_mono (μ := seedLaw k) Integrable.of_finite Integrable.of_finite hp
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  rw [meanSquare, seedLaw, integral_prod _ Integrable.of_finite]
  exact hi

/-- The actual trajectory's expected coercive energy telescopes over the finite inner loop. -/
theorem meanCost_sum_bound {G : Fin n → E → E} (regularizer : E → E)
    {L μ : ℝ} (hL : 0 ≤ L) (hAS : AveragedSmooth G S L)
    (anchor : S) (bias : E) {η : ℝ} (hη : 0 < η) (hsmall : 11 * η * L ^ 2 ≤ μ)
    (star : S)
    (hstar : VariationalInequality.IsSolution S (fun w ↦ operator G regularizer w + bias) star)
    (W : E → ℝ) (Vstar : ℝ)
    (hLip : ∀ z ∈ S, ‖operator G regularizer z - operator G regularizer star‖ ≤ 3 * L * ‖z - star‖)
    (hMono : ∀ z ∈ S, W z ≤ ⟪operator G regularizer z - operator G regularizer star, z - star⟫_ℝ)
    (hcoercive : ∀ z ∈ S, μ * ‖z - star‖ ^ 2 ≤ W z)
    (hanchor : ‖(star : E) - anchor‖ ^ 2 ≤ Vstar) (K : ℕ) :
    η * ∑ k ∈ Finset.range K, meanCost S hne hclosed hconvex G regularizer anchor bias η W k ≤
      ‖(anchor : E) - star‖ ^ 2 + (K : ℝ) * (2 * η ^ 2 * L ^ 2 * Vstar) := by
  let energy := meanSquare S hne hclosed hconvex G regularizer anchor bias η (star : E)
  let cost := meanCost S hne hclosed hconvex G regularizer anchor bias η W
  have hrec (k : ℕ) : energy (k + 1) ≤ energy k - η * cost k + η * (2 * η * L ^ 2 * Vstar) := by
    have h := meanSquare_recursion S hne hclosed hconvex regularizer hL hAS anchor bias hη hsmall
      star hstar W Vstar hLip hMono hcoercive hanchor k
    dsimp [energy, cost]
    nlinarith
  have ht := descent_telescopes energy cost (fun _ ↦ 2 * η * L ^ 2 * Vstar) η hrec K
  have hn := meanSquare_nonneg S hne hclosed hconvex G regularizer anchor bias η (star : E) K
  have h0 := meanSquare_initial S hne hclosed hconvex G regularizer anchor bias η (star : E)
  dsimp [energy] at ht
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
  dsimp [cost] at ht
  nlinarith

end NCConcave16991.InnerAlgorithm


