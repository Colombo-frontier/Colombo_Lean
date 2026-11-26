import HeavyTail.MaskedCoordinateOracle
import HeavyTail.GaussianAdaptiveLower

/-! Actual adaptive masked-coordinate testing and objective-event lower bound.
The oracle's unobserved-coordinate event forces transcript agreement through
the generic sampler execution induction; no testing premise is assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace HeavyTail.MaskedLower
open GaussianLower
noncomputable section

variable {Seed : Type} [MeasurableSpace Seed] {k T : ℕ}

theorem masked_hypercube_pair_testing
    (A : AdaptiveKernel.Policy Seed (HardSpace k) (HardSpace k) (HardSpace k) T)
    (P : Measure Seed) [IsProbabilityMeasure P] (a ρ : ℝ) {π : ℝ}
    (hπ : 0 ≤ π) (hπ1 : π ≤ 1) (hkπ : (k : ℝ) * π ≤ 1)
    (hbudget : (T : ℝ) * π ≤ 1 / 8) (v : Fin k → Bool) (j : Fin k) :
    (7 / 8 : ℝ) ≤
      hypercubeBitError (fun v => A.historyLaw P (maskedKernel a ρ π hπ hkπ v) T)
        (fun h => hardDecode (A.output h)) v j +
      hypercubeBitError (fun v => A.historyLaw P (maskedKernel a ρ π hπ hkπ v) T)
        (fun h => hardDecode (A.output h)) (gaussianFlip v j) j := by
  have hd : Measurable (fun h => hardDecode (A.output h) j) :=
    (hardDecode_measurable j).comp A.output_measurable
  have ht := AdaptiveKernel.sampler_pair_testing_lower A P
    (coordinateCoin π hπ hkπ).toMeasure (maskedSampler_measurable a ρ π v)
    (maskedSampler_measurable a ρ π (gaussianFlip v j)) {b | b ≠ some j}
    (maskedSampler_neighbor_agreement a ρ π v j) (fun h => hardDecode (A.output h) j) hd (v j)
  rw [coordinate_no_reveal_probability hπ hkπ j] at ht
  have hleft := (no_reveal_all_calls_lower hπ1 hbudget).trans ht
  simpa only [hypercubeBitError, maskedKernel, gaussianFlip, Function.update_same] using hleft

theorem masked_objective_probability_lower (hk : 0 < k)
    (A : AdaptiveKernel.Policy Seed (HardSpace k) (HardSpace k) (HardSpace k) T)
    (P : Measure Seed) [IsProbabilityMeasure P] {μ D a π : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hπ : 0 ≤ π) (hπ1 : π ≤ 1) (hkπ : (k : ℝ) * π ≤ 1)
    (hbudget : (T : ℝ) * π ≤ 1 / 8) :
    ∃ v : Fin k → Bool, (1 / 4 : ℝ) ≤
      (A.historyLaw P (maskedKernel a (envelopeRadius μ D a / Real.sqrt k) π hπ hkπ v) T).real
        {h | envelope μ D a / 4 ≤ traceLoss μ D a v (A.output h)} := by
  let Q := fun v : Fin k → Bool => A.historyLaw P
    (maskedKernel a (envelopeRadius μ D a / Real.sqrt k) π hπ hkπ v) T
  let decode := fun h => hardDecode (A.output h)
  have hd (i : Fin k) : Measurable (fun h => decode h i) :=
    (hardDecode_measurable i).comp A.output_measurable
  obtain ⟨v, hv⟩ := exists_hypercube_hamming_probability hk Q hd
    (masked_hypercube_pair_testing A P a (envelopeRadius μ D a / Real.sqrt k)
      hπ hπ1 hkπ hbudget)
  refine ⟨v, hv.trans (measureReal_mono ?_)⟩
  intro h hh
  have hgap := hardComposite_loss_hamming hk hμ hD ha (gaussianSigns v) (gaussianSigns_mem v)
    (A.output h)
  have hJ : (k : ℝ) / 4 ≤ (signHamming (gaussianSigns v) (fun j => A.output h j) : ℝ) := by
    change (k : ℝ) / 4 ≤ decodedHamming (fun x : HardSpace k => hardDecode x) v (A.output h) at hh
    simpa only [decodedHamming_eq_signHamming] using hh
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hmul := mul_le_mul_of_nonneg_left hJ
    (div_nonneg (envelope_nonneg hμ hD ha) hkR.le)
  have he : envelope μ D a / (k : ℝ) * ((k : ℝ) / 4) = envelope μ D a / 4 := by field_simp
  rw [he] at hmul
  exact hmul.trans hgap

end
end HeavyTail.MaskedLower
