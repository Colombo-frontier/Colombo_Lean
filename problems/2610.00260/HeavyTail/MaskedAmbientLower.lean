import HeavyTail.ActiveSpaceEmbedding
import HeavyTail.MaskedOracleModel
import HeavyTail.AdaptiveKernelModel

/-! Adaptive masked-coordinate lower bound in an arbitrary larger Euclidean
ambient space. The actual embedded private oracle is identified with its fresh
finite sampler; the hidden-coordinate transcript agreement is then derived. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail.MaskedLower
open GaussianLower
noncomputable section

def ambientMaskedSampler {k d : ℕ} (θ : OracleParameters) (e : HardSpace k →ₗᵢ[ℝ] HardSpace d)
    (a ρ π : ℝ) (v : Fin k → Bool)
    (z : (quadraticPublicProblem (HardSpace d) θ).X × CoordinateMask k) : HardSpace d :=
  e (maskedSampler a ρ π v (activeProjection e z.1, z.2))

theorem ambientMaskedSampler_measurable {k d : ℕ} (θ : OracleParameters)
    (e : HardSpace k →ₗᵢ[ℝ] HardSpace d) (a ρ π : ℝ) (v : Fin k → Bool) :
    Measurable (ambientMaskedSampler θ e a ρ π v) :=
  e.continuous.measurable.comp ((maskedSampler_measurable a ρ π v).comp
    (((activeProjection e).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd))

theorem embeddedMasked_oracle_sampler {k d : ℕ} (θ : OracleParameters)
    (e : HardSpace k →ₗᵢ[ℝ] HardSpace d) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (π : ℝ) (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool) :
    (embeddedPrivateInstance e (maskedPrivateInstance θ hk hdim π hπ hkπ v)).oracle =
      kernelOfSampler (coordinateCoin π hπ.le hkπ).toMeasure
        (ambientMaskedSampler θ e (maskedAmplitude θ.G θ.L θ.p k π)
          (envelopeRadius θ.μ θ.D (maskedAmplitude θ.G θ.L θ.p k π) / Real.sqrt k) π v)
        (ambientMaskedSampler_measurable θ e _ _ π v) :=
  embeddedOracle_sampler e (maskedPrivateInstance θ hk hdim π hπ hkπ v)
    (coordinateCoin π hπ.le hkπ).toMeasure
    (maskedSampler _ _ π v) (maskedSampler_measurable _ _ π v) rfl

theorem ambientMasked_pair_testing {k d : ℕ} (θ : OracleParameters)
    (e : HardSpace k →ₗᵢ[ℝ] HardSpace d) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1) (hkπ : (k : ℝ) * π ≤ 1) (hbudget : (θ.T : ℝ) * π ≤ 1 / 8)
    (A : PublicPolicy (quadraticPublicProblem (HardSpace d) θ)) (v : Fin k → Bool) (j : Fin k) :
    (7 / 8 : ℝ) ≤
      hypercubeBitError (fun v => A.strategy.historyLaw A.seedLaw
        (embeddedPrivateInstance e (maskedPrivateInstance θ hk hdim π hπ hkπ v)).oracle θ.T)
        (fun h => hardDecode (activeProjection e (A.strategy.output h))) v j +
      hypercubeBitError (fun v => A.strategy.historyLaw A.seedLaw
        (embeddedPrivateInstance e (maskedPrivateInstance θ hk hdim π hπ hkπ v)).oracle θ.T)
        (fun h => hardDecode (activeProjection e (A.strategy.output h))) (gaussianFlip v j) j := by
  let a := maskedAmplitude θ.G θ.L θ.p k π
  let ρ := envelopeRadius θ.μ θ.D a / Real.sqrt k
  have hd : Measurable (fun h => hardDecode (activeProjection e (A.strategy.output h)) j) :=
    (hardDecode_measurable j).comp ((activeProjection e).continuous.measurable.comp
      (measurable_subtype_coe.comp A.strategy.output_measurable))
  have hagree : ∀ x b, b ∈ {b : CoordinateMask k | b ≠ some j} →
      ambientMaskedSampler θ e a ρ π v (x, b) =
        ambientMaskedSampler θ e a ρ π (gaussianFlip v j) (x, b) := by
    intro x b hb
    exact congrArg e (maskedSampler_neighbor_agreement a ρ π v j (activeProjection e x) b hb)
  have ht := AdaptiveKernel.sampler_pair_testing_lower A.strategy A.seedLaw
    (coordinateCoin π hπ.le hkπ).toMeasure (ambientMaskedSampler_measurable θ e a ρ π v)
    (ambientMaskedSampler_measurable θ e a ρ π (gaussianFlip v j)) {b | b ≠ some j} hagree
    (fun h => hardDecode (activeProjection e (A.strategy.output h)) j) hd (v j)
  rw [coordinate_no_reveal_probability hπ.le hkπ j] at ht
  have hleft := (no_reveal_all_calls_lower hπ1 hbudget).trans ht
  simp only [hypercubeBitError, embeddedMasked_oracle_sampler, gaussianFlip, Function.update_self]
  exact hleft

theorem ambientMasked_objective_probability_lower {k d : ℕ} (θ : OracleParameters)
    (e : HardSpace k →ₗᵢ[ℝ] HardSpace d) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1) (hkπ : (k : ℝ) * π ≤ 1) (hbudget : (θ.T : ℝ) * π ≤ 1 / 8)
    (A : PublicPolicy (quadraticPublicProblem (HardSpace d) θ)) :
    ∃ v : Fin k → Bool, (1 / 4 : ℝ) ≤
      (PublicPolicy.outputLaw A (embeddedPrivateInstance e
        (maskedPrivateInstance θ hk hdim π hπ hkπ v))).real
        {x | ENNReal.ofReal (envelope θ.μ θ.D (maskedAmplitude θ.G θ.L θ.p k π) / 4) ≤
          (embeddedPrivateInstance e (maskedPrivateInstance θ hk hdim π hπ hkπ v)).loss x} := by
  let a := maskedAmplitude θ.G θ.L θ.p k π
  let I := fun v => maskedPrivateInstance θ hk hdim π hπ hkπ v
  let J := fun v => embeddedPrivateInstance e (I v)
  let Q := fun v => A.strategy.historyLaw A.seedLaw (J v).oracle θ.T
  let decode := fun h => hardDecode (activeProjection e (A.strategy.output h))
  have hd (i : Fin k) : Measurable (fun h => decode h i) :=
    (hardDecode_measurable i).comp ((activeProjection e).continuous.measurable.comp
      (measurable_subtype_coe.comp A.strategy.output_measurable))
  obtain ⟨v, hv⟩ := exists_hypercube_hamming_probability hk Q hd
    (ambientMasked_pair_testing θ e hk hdim π hπ hπ1 hkπ hbudget A)
  refine ⟨v, ?_⟩
  change (1 / 4 : ℝ) ≤ (PublicPolicy.outputLaw A (J v)).real
    {x | ENNReal.ofReal (envelope θ.μ θ.D a / 4) ≤ (J v).loss x}
  have hEvent : MeasurableSet {x | ENNReal.ofReal (envelope θ.μ θ.D a / 4) ≤ (J v).loss x} :=
    measurableSet_le measurable_const (J v).loss_measurable
  unfold PublicPolicy.outputLaw AdaptiveKernel.Policy.outputLaw
  rw [map_measureReal_apply A.strategy.output_measurable hEvent]
  apply hv.trans
  apply measureReal_mono (μ := Q v) _ (measure_ne_top _ _)
  intro h hh
  have ha : 0 ≤ a := maskedAmplitude_nonneg θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L) hπ.le k
  let x := activeProjection e (A.strategy.output h)
  have hgap := hardComposite_loss_hamming hk θ.μ_nonneg θ.D_pos.le ha
    (gaussianSigns v) (gaussianSigns_mem v) x
  have hJ : (k : ℝ) / 4 ≤ (signHamming (gaussianSigns v) (fun j => x j) : ℝ) := by
    change (k : ℝ) / 4 ≤ decodedHamming (fun x : HardSpace k => hardDecode x) v x at hh
    simpa only [decodedHamming_eq_signHamming] using hh
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hmul := mul_le_mul_of_nonneg_left hJ
    (div_nonneg (envelope_nonneg θ.μ_nonneg θ.D_pos.le ha) hkR.le)
  have heq : envelope θ.μ θ.D a / (k : ℝ) * ((k : ℝ) / 4) = envelope θ.μ θ.D a / 4 := by field_simp
  rw [heq] at hmul
  have hactive : ENNReal.ofReal (envelope θ.μ θ.D a / 4) ≤
      (I v).loss (activeQuery e (A.strategy.output h)) := by
    rw [maskedPrivateInstance_loss]
    exact ENNReal.ofReal_le_ofReal (hmul.trans hgap)
  exact hactive.trans (embeddedPrivateInstance_loss_domination e (I v) (A.strategy.output h))

end
end HeavyTail.MaskedLower
