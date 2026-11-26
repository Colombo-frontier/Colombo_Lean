import NCConcave16991.EpochVariance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Finite independent histories and actual stochastic trajectories

The history at time t consists of exactly t independent draws. Future samples
do not occur in the state at time t. All moment recurrences below are derived
by integrating the actual next-state map under the product law.
-/

open MeasureTheory
open scoped BigOperators

namespace NCConcave16991.FiniteProcess

universe u

@[reducible] def History (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | t + 1 => History I t × I

instance historyFinite (I : Type u) [Finite I] : ∀ t, Finite (History I t)
  | 0 => inferInstanceAs (Finite PUnit)
  | t + 1 => by
    have := historyFinite I t
    exact inferInstanceAs (Finite (History I t × I))

@[reducible] instance historyMeasurable (I : Type u) [MeasurableSpace I] :
    ∀ t, MeasurableSpace (History I t)
  | 0 => PUnit.instMeasurableSpace
  | t + 1 => @Prod.instMeasurableSpace _ _ (historyMeasurable I t) inferInstance

instance historySingleton (I : Type u) [MeasurableSpace I]
    [MeasurableSingletonClass I] : ∀ t, MeasurableSingletonClass (History I t)
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit)
  | t + 1 => @Prod.instMeasurableSingletonClass _ _ _ _ (historySingleton I t) inferInstance

variable {I : Type u} [MeasurableSpace I]

noncomputable def law (ν : Measure I) : (t : ℕ) → Measure (History I t)
  | 0 => Measure.dirac PUnit.unit
  | t + 1 => (law ν t).prod ν

instance law_probability (ν : Measure I) [IsProbabilityMeasure ν] :
    ∀ t, IsProbabilityMeasure (law ν t)
  | 0 => by
    change IsProbabilityMeasure (@Measure.dirac PUnit PUnit.instMeasurableSpace PUnit.unit)
    infer_instance
  | t + 1 => by
    have := law_probability ν t
    change IsProbabilityMeasure ((law ν t).prod ν)
    infer_instance

def trajectory {E : Type*} (step : ℕ → E → I → E) (initial : E) :
    (t : ℕ) → History I t → E
  | 0, _ => initial
  | t + 1, h => step t (trajectory step initial t h.1) h.2

variable [Finite I] [MeasurableSingletonClass I]
  (ν : Measure I) [IsProbabilityMeasure ν]

theorem integral_succ {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] (t : ℕ) (f : History I (t + 1) → H) :
    (∫ h, f h ∂law ν (t + 1)) = ∫ h, ∫ i, f (h, i) ∂ν ∂law ν t := by
  exact integral_prod _ Integrable.of_finite

theorem integral_previous (t : ℕ) (f : History I t → ℝ) :
    (∫ h : History I (t + 1), f h.1 ∂law ν (t + 1)) = ∫ h, f h ∂law ν t := by
  rw [integral_succ]
  simp

theorem trajectory_integral_succ {E H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (step : ℕ → E → I → E) (initial : E) (f : E → H) (t : ℕ) :
    (∫ h, f (trajectory step initial (t + 1) h) ∂law ν (t + 1)) =
      ∫ h, ∫ i, f (step t (trajectory step initial t h) i) ∂ν ∂law ν t := by
  exact integral_succ ν t _

/-- A local moment estimate is integrated over the genuine preceding history. -/
theorem integral_step_le (t : ℕ) (f : History I (t + 1) → ℝ)
    (bound : History I t → ℝ)
    (hstep : ∀ h, (∫ i, f (h, i) ∂ν) ≤ bound h) :
    (∫ h, f h ∂law ν (t + 1)) ≤ ∫ h, bound h ∂law ν t := by
  rw [integral_succ]
  exact integral_mono Integrable.of_finite Integrable.of_finite hstep

/-- Exact-refresh variance accumulation for actual finite independent histories.
The one-step bound is conditioned only on the preceding history. -/
theorem epoch_variance {q : ℕ} (hq : 0 < q) {α : ℝ} (hα : 0 ≤ α)
    (error : (t : ℕ) → History I t → ℝ)
    (movement : (t : ℕ) → History I t → ℝ)
    (he : ∀ t h, 0 ≤ error t h) (hm : ∀ t h, 0 ≤ movement t h)
    (hreset : ∀ t, t % q = 0 → ∀ h, error t h = 0)
    (hstep : ∀ t, (t + 1) % q ≠ 0 → ∀ h,
      (∫ i, error (t + 1) (h, i) ∂ν) ≤ error t h + α * movement t h)
    (S : ℕ) :
    (∑ t ∈ Finset.range S, ∫ h, error t h ∂law ν t) ≤
      (q : ℝ) * α * ∑ t ∈ Finset.range S, ∫ h, movement t h ∂law ν t := by
  apply epoch_variance_sum hq _ _ hα
  · intro t
    exact integral_nonneg (he t)
  · intro t
    exact integral_nonneg (hm t)
  · intro t ht
    simp_rw [hreset t ht]
    simp
  · intro t ht
    have hh := integral_step_le ν t (error (t + 1)) _ (hstep t ht)
    simpa only [integral_add Integrable.of_finite Integrable.of_finite,
      integral_const_mul] using hh

/-- Version where the movement is also produced by the new samples. This
includes an inner solve followed by a fresh anchor-difference batch. -/
theorem epoch_variance_next {q : ℕ} (hq : 0 < q) {α : ℝ} (hα : 0 ≤ α)
    (error : (t : ℕ) → History I t → ℝ)
    (movement : (t : ℕ) → History I (t + 1) → ℝ)
    (he : ∀ t h, 0 ≤ error t h) (hm : ∀ t h, 0 ≤ movement t h)
    (hreset : ∀ t, t % q = 0 → ∀ h, error t h = 0)
    (hstep : ∀ t, (t + 1) % q ≠ 0 → ∀ h,
      (∫ i, error (t + 1) (h, i) ∂ν) ≤
        error t h + α * ∫ i, movement t (h, i) ∂ν)
    (S : ℕ) :
    (∑ t ∈ Finset.range S, ∫ h, error t h ∂law ν t) ≤
      (q : ℝ) * α * ∑ t ∈ Finset.range S, ∫ h, movement t h ∂law ν (t + 1) := by
  have hh := epoch_variance ν hq hα error
    (fun t h ↦ ∫ i, movement t (h, i) ∂ν) he
    (fun t h ↦ integral_nonneg (fun i ↦ hm t (h, i))) hreset hstep S
  simpa only [← integral_succ] using hh

end NCConcave16991.FiniteProcess
