import MatchingBounds1005.ScheduledGaussianPrefix

/-! Scheduled Haar prefix control in an arbitrary sufficiently large ambient
dimension, so the concrete copied-chain dimension can be used directly. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianMatrix
open MatchingBounds1005.GaussianBlockGeometry MatchingBounds1005.ScheduledPrefix

namespace MatchingBounds1005.ScheduledHaar
universe u

theorem RoundPolicy.haar_prefix_failure_of_dimension {dim : ℕ} (n : ℕ)
    (hdim : 0 < dim) (hroom : actionCount n ≤ dim) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (Q : Vec dim →L[ℝ] Vec dim) (plan : RoundPolicy (Vec dim) n H)
    (I : ℕ → Submodule ℝ (Vec dim)) (A : Submodule ℝ (Vec dim))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q n I)
    (hIA : ∀ t, I t ≤ A) {η ζ : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hangle : (gaussianMatrixLaw dim (actionCount n + actionCount n)).real
      {g | ¬ CyclicAngleGood A Q g η} ≤ ζ) :
    (μ.prod (haarLaw (Vec dim))).real
      {p | roundQueryTrace (Vec dim) n (plan.run n Q (p.2 : Vec dim →L[ℝ] Vec dim) p.1)
          ∉ prefixEvent I A η} ≤ ζ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hroom
  exact plan.haar_prefix_failure d n hdim μ Q I A hmono hschedule hIA hη hηhalf hangle

theorem SourcePolicy.haar_prefix_failure_of_dimension {dim : ℕ} (w : List SourceKind)
    (hdim : 0 < dim) (hroom : actionCount w.length ≤ dim) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (Q : Vec dim →L[ℝ] Vec dim) (plan : SourcePolicy (E := Vec dim) w H)
    (I : ℕ → Submodule ℝ (Vec dim)) (A : Submodule ℝ (Vec dim))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q w I)
    (hIA : ∀ t, I t ≤ A) {η ζ : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hangle : (gaussianMatrixLaw dim (actionCount w.length + actionCount w.length)).real
      {g | ¬ CyclicAngleGood A Q g η} ≤ ζ) :
    (μ.prod (haarLaw (Vec dim))).real
      {p | roundQueryTrace (Vec dim) w.length
        ((plan.compile w).run w.length Q (p.2 : Vec dim →L[ℝ] Vec dim) p.1)
          ∉ prefixEvent I A η} ≤ ζ :=
  (plan.compile w).haar_prefix_failure_of_dimension w.length hdim hroom μ Q I A hmono
    (plan.compile_scheduled w Q I hschedule) hIA hη hηhalf hangle

theorem RoundPolicy.haar_prefix_measurable {dim : ℕ} (n : ℕ)
    (hroom : actionCount n ≤ dim) {H : Type u} [MeasurableSpace H]
    (Q : Vec dim →L[ℝ] Vec dim) (plan : RoundPolicy (Vec dim) n H)
    (I : ℕ → Submodule ℝ (Vec dim)) (A : Submodule ℝ (Vec dim)) (η : ℝ) :
    MeasurableSet {p : H × Rotation (Vec dim) |
      roundQueryTrace (Vec dim) n (plan.run n Q (p.2 : Vec dim →L[ℝ] Vec dim) p.1)
        ∈ prefixEvent I A η} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hroom
  exact ((roundQueryTrace_measurable n).comp (plan.run_measurable d n Q))
    (measurableSet_prefixEvent I A η)

end MatchingBounds1005.ScheduledHaar
