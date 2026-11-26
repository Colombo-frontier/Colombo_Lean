import NoisyZO.AssouadReduction
import NoisyZO.HardHypercube
import NoisyZO.Model
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Concrete decision errors for the Assouad reduction

This module turns a family of output laws into the coordinate-error and
edge-distance quantities used by the finite Assouad argument.  The testing
edge inequality and the strong-convexity output-to-loss comparison are proved
here, rather than retained as free scalar premises.
-/

open MeasureTheory Set
open scoped BigOperators

namespace NoisyZO

noncomputable section

/-- Outputs whose decoded `i`-th sign disagrees with vertex `s`. -/
def assouadErrorSet {d : ℕ} (s : Hypercube d) (i : Fin d) : Set (Point d) :=
  {x | decode x i ≠ s i}

theorem measurable_decode {d : ℕ} (i : Fin d) :
    Measurable (fun x : Point d ↦ decode x i) := by
  unfold decode
  apply Measurable.ite
  · exact measurableSet_Ici.preimage
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  · exact measurable_const
  · exact measurable_const

theorem assouadErrorSet_measurable {d : ℕ} (s : Hypercube d) (i : Fin d) :
    MeasurableSet (assouadErrorSet s i) := by
  change MeasurableSet ((fun x : Point d ↦ decode x i) ⁻¹' ({s i}ᶜ))
  exact (measurableSet_singleton _).compl.preimage (measurable_decode i)

/-- Probability of a decoded coordinate error under each output law. -/
def assouadErrorProbability {d : ℕ}
    (law : Hypercube d → Measure (Point d))
    (s : Hypercube d) (i : Fin d) : ℝ :=
  (law s).real (assouadErrorSet s i)

/-- Difference on the particular decision event used by an Assouad edge. -/
def assouadEdgeEventDistance {d : ℕ}
    (law : Hypercube d → Measure (Point d))
    (s : Hypercube d) (i : Fin d) : ℝ :=
  |(law s).real (assouadErrorSet s i) -
    (law (flipHypercube s i)).real (assouadErrorSet s i)|

/-- Flipping coordinate `i` exchanges its error event with its complement. -/
theorem assouadErrorSet_flip {d : ℕ} (s : Hypercube d) (i : Fin d) :
    assouadErrorSet (flipHypercube s i) i = (assouadErrorSet s i)ᶜ := by
  ext x
  cases hs : s i <;>
    simp [assouadErrorSet, flipHypercube, hs]

/-- The concrete decision error and event distance automatically satisfy the
two-point testing inequality used by Assouad's lemma. -/
theorem assouadErrorProbability_edge
    {d : ℕ} (law : Hypercube d → Measure (Point d))
    [∀ s, IsProbabilityMeasure (law s)]
    (s : Hypercube d) (i : Fin d) :
    1 - assouadEdgeEventDistance law s i ≤
      assouadErrorProbability law s i +
        assouadErrorProbability law (flipHypercube s i) i := by
  let E : Set (Point d) := assouadErrorSet s i
  have hE : MeasurableSet E := assouadErrorSet_measurable s i
  have hcomp := probReal_add_probReal_compl
    (μ := law (flipHypercube s i)) hE
  have habs :
      (law (flipHypercube s i)).real E - (law s).real E ≤
        |(law s).real E - (law (flipHypercube s i)).real E| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  rw [assouadErrorProbability, assouadErrorProbability,
    assouadEdgeEventDistance, assouadErrorSet_flip]
  change 1 - |(law s).real E - (law (flipHypercube s i)).real E| ≤
    (law s).real E + (law (flipHypercube s i)).real Eᶜ
  nlinarith

private theorem coordinateError_eq_indicator {d : ℕ}
    (s : Hypercube d) (i : Fin d) :
    (fun x : Point d ↦ if decode x i = s i then (0 : ℝ) else 1) =
      (assouadErrorSet s i).indicator (fun _ ↦ (1 : ℝ)) := by
  funext x
  by_cases h : decode x i = s i <;>
    simp [assouadErrorSet, Set.indicator, h]

/-- Integrating one coordinate-error indicator gives its concrete error
probability. -/
theorem integral_coordinateError_eq_probability
    {d : ℕ} (law : Hypercube d → Measure (Point d))
    (s : Hypercube d) (i : Fin d) :
    (∫ x, (if decode x i = s i then (0 : ℝ) else 1) ∂law s) =
      assouadErrorProbability law s i := by
  rw [coordinateError_eq_indicator, integral_indicator_const 1
    (assouadErrorSet_measurable s i)]
  simp [assouadErrorProbability]

/-- Expected Hamming loss is the sum of the concrete coordinate-error
probabilities. -/
theorem integral_hammingLoss_eq_sum_errorProbability
    {d : ℕ} (law : Hypercube d → Measure (Point d))
    [∀ s, IsProbabilityMeasure (law s)] (s : Hypercube d) :
    (∫ x, hammingLoss s x ∂law s) =
      ∑ i : Fin d, assouadErrorProbability law s i := by
  have hint : ∀ i : Fin d,
      Integrable (fun x : Point d ↦
        if decode x i = s i then (0 : ℝ) else 1) (law s) := by
    intro i
    rw [coordinateError_eq_indicator]
    exact (integrable_const (1 : ℝ)).indicator
      (assouadErrorSet_measurable s i)
  unfold hammingLoss
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hint i)]
  exact Finset.sum_congr rfl fun i _ ↦
    integral_coordinateError_eq_probability law s i

/-- A normalized objective's strong-convexity field bounds its gap below by
half the squared distance to its stationary minimizer. -/
theorem NormalizedObjective.half_distance_sq_le_gap
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) :
    (1 / 2 : ℝ) * ‖x - F.minimizer‖ ^ 2 ≤
      F.f x - F.f F.minimizer := by
  have h := F.strong F.minimizer x
  rw [F.minimizer_stationary, inner_zero_left, add_zero] at h
  linarith

/-- The center of the Boolean hard family is exactly the signed center used by
the deterministic Hamming decoder. -/
theorem hardCenter_hypercubeSign_eq_signCenter {d : ℕ}
    (c : ℝ) (s : Hypercube d) :
    hardCenter (c / Real.sqrt d) (hypercubeSign s) =
      signCenter (c / (2 * Real.sqrt d)) s := by
  ext i
  simp only [hardCenter_apply, hypercubeSign, signCenter_apply]
  ring

/-- Once the exact minimizer is a signed center, expected Hamming error is
automatically bounded by expected optimization loss. -/
theorem NormalizedObjective.expected_hamming_to_gap
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (law : Hypercube d → Measure (Point d))
    [∀ s, IsProbabilityMeasure (law s)]
    (c : ℝ) (hc : 0 ≤ c) (s : Hypercube d)
    (hmin : F.minimizer = signCenter c s)
    (hgap : Integrable (fun x ↦ F.f x - F.f F.minimizer) (law s)) :
    (c ^ 2 / 2) * (∑ i : Fin d, assouadErrorProbability law s i) ≤
      ∫ x, F.f x - F.f F.minimizer ∂law s := by
  have hham : Integrable (fun x ↦ hammingLoss s x) (law s) := by
    unfold hammingLoss
    apply integrable_finsetSum Finset.univ
    intro i _hi
    rw [coordinateError_eq_indicator]
    exact (integrable_const (1 : ℝ)).indicator
      (assouadErrorSet_measurable s i)
  have hscaled : Integrable (fun x ↦ (c ^ 2 / 2) * hammingLoss s x) (law s) :=
    hham.const_mul _
  calc
    (c ^ 2 / 2) * (∑ i : Fin d, assouadErrorProbability law s i) =
        (c ^ 2 / 2) * (∫ x, hammingLoss s x ∂law s) := by
      rw [integral_hammingLoss_eq_sum_errorProbability law s]
    _ = ∫ x, (c ^ 2 / 2) * hammingLoss s x ∂law s := by
      rw [integral_const_mul]
    _ ≤ ∫ x, F.f x - F.f F.minimizer ∂law s := by
      apply integral_mono hscaled hgap
      intro x
      apply hamming_to_stronglyConvex_loss hc s x
      rw [← hmin]
      exact F.half_distance_sq_le_gap x

end

end NoisyZO
