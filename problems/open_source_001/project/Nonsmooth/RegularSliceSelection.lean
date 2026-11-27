import Nonsmooth.DominatedSliceNoSpike
import Nonsmooth.RankControlledSelection

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def regularSliceEnergy (V : ℝ → ℝ → ℝ) (y : ℝ) : ℝ :=
  (y - ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) ^ 2 +
    (potentialExpectation V (fun _ x => x) y - ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) ^ 2

theorem realDensityLaw_atomless (w : ℝ → ℝ) (x : ℝ) : (realDensityLaw w) {x} = 0 := by
  have hac : realDensityLaw w ≪ (volume : Measure ℝ) :=
    cond_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  exact hac (measure_singleton x)

theorem regularSliceEnergy_nonneg (V : ℝ → ℝ → ℝ) (y : ℝ) : 0 ≤ regularSliceEnergy V y :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem regularSliceEnergy_measurable {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) :
    Measurable (regularSliceEnergy V) := by
  have hm : Measurable (potentialExpectation V (fun _ x => x)) :=
    (continuous_iff_continuousAt.mpr (fun t => (regularFamily_regression_hasDerivAt H t).continuousAt)).measurable
  unfold regularSliceEnergy
  fun_prop

/-- Logarithmic control of any selected regular slice energy. Candidate rows may
have different potential densities; their scalar marginals are the actual laws. -/
theorem regular_slice_selected_energy {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ} [Nonempty (Fin k)]
    (V : Fin k → ℝ → ℝ → ℝ)
    (H : ∀ i, RegularStrongSliceFamily (V i))
    (G : ∀ i, RegularStrongSliceFamily (fun t x => V i x t))
    (C : ∀ i, RegularSliceMomentContinuity (V i) (H i))
    (X : Fin k → α → ℝ) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = realDensityLaw (potentialPartition (V i)))
    (Z : α → ℝ) (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (hsel : ∀ x, ∃ i, Z x ≤ regularSliceEnergy (V i) (X i x)) :
    Integrable Z μ ∧ (∫ x, Z x ∂μ) ≤ 72 * (1 + 2 * Real.log (4 * (k : ℝ))) := by
  apply selected_rank_controlled_energy μ X hX
    (fun i y => by rw [hlaw i]; exact realDensityLaw_atomless _ y)
    (fun i => regularSliceEnergy (V i)) (fun i => regularSliceEnergy_measurable (H i))
    (by norm_num : (0 : ℝ) < 72) _ Z hZ hZ0 hsel
  intro i y
  rw [hlaw i]
  exact dominated_slice_no_spike (H i) (G i) (C i) y

theorem regular_slice_selected_log_energy {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ} [Nonempty (Fin k)]
    (V : Fin k → ℝ → ℝ → ℝ)
    (H : ∀ i, RegularStrongSliceFamily (V i))
    (G : ∀ i, RegularStrongSliceFamily (fun t x => V i x t))
    (C : ∀ i, RegularSliceMomentContinuity (V i) (H i))
    (X : Fin k → α → ℝ) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = realDensityLaw (potentialPartition (V i)))
    (Z : α → ℝ) (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (hsel : ∀ x, ∃ i, Z x ≤ regularSliceEnergy (V i) (X i x)) :
    Integrable Z μ ∧ (∫ x, Z x ∂μ) ≤ 504 * Real.log (Real.exp 1 * (k : ℝ)) := by
  have hs := regular_slice_selected_energy μ V H G C X hX hlaw Z hZ hZ0 hsel
  have hk : (1 : ℝ) ≤ k := by
    exact_mod_cast (show 1 ≤ k from Nat.succ_le_of_lt (by simpa only [Fintype.card_fin] using
      (Fintype.card_pos : 0 < Fintype.card (Fin k))))
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk
  refine ⟨hs.1, hs.2.trans ?_⟩
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hk0.ne',
    Real.log_mul (Real.exp_ne_zero _) hk0.ne', Real.log_exp]
  nlinarith

end
end Nonsmooth
