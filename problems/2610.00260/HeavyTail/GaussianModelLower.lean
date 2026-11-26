import HeavyTail.GaussianOracleModel
import HeavyTail.GaussianMinimax
import HeavyTail.AdaptiveKernelTransport
import HeavyTail.ModelQuantile

/-! Gaussian trace lower bound in the full public/private fresh-oracle model.
Every public-data-only randomized policy is tested against one fixed member
of the admissible Gaussian family on the same public quadratic problem. -/

open MeasureTheory
open scoped ENNReal
namespace HeavyTail.GaussianLower
noncomputable section

theorem gaussian_publicPolicy_probability_lower {k : ℕ} (θ : OracleParameters)
    (hk : 0 < k) (hT : 0 < θ.T) (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2)
    (A : PublicPolicy (quadraticPublicProblem (HardSpace k) θ)) :
    ∃ v : Fin k → Bool,
      θ.δ < (PublicPolicy.outputLaw A (gaussianPrivateInstance θ hk hdim
        (traceAmplitude θ.G θ.L θ.T)
        (traceAmplitude_nonneg θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L) θ.T)
        (traceAmplitude_le_G θ.G θ.L θ.T) v)).real
        {x | ENNReal.ofReal (traceRate θ.μ θ.D θ.G θ.L θ.T) ≤
          (gaussianPrivateInstance θ hk hdim (traceAmplitude θ.G θ.L θ.T)
            (traceAmplitude_nonneg θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L) θ.T)
            (traceAmplitude_le_G θ.G θ.L θ.T) v).loss x} := by
  let a := traceAmplitude θ.G θ.L θ.T
  have ha : 0 ≤ a := traceAmplitude_nonneg θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L) θ.T
  have haG : a ≤ θ.G := traceAmplitude_le_G θ.G θ.L θ.T
  let A' := A.mapQueryOutput Subtype.val measurable_subtype_coe
    Subtype.val measurable_subtype_coe
  have hδ : θ.δ < 1 / 4 := θ.δ_lt_tenth.trans (by norm_num)
  obtain ⟨v, hv⟩ := gaussian_trace_rate_probability_lower hk hT θ.μ_nonneg θ.D_pos.le
    θ.G_pos.le (θ.s_pos.trans_le θ.s_le_L) hδ A'
  let I := gaussianPrivateInstance θ hk hdim a ha haG v
  refine ⟨v, ?_⟩
  change θ.δ < (PublicPolicy.outputLaw A I).real {x | ENNReal.ofReal
    (traceRate θ.μ θ.D θ.G θ.L θ.T) ≤ I.loss x}
  have hEvent : MeasurableSet {x | ENNReal.ofReal (traceRate θ.μ θ.D θ.G θ.L θ.T) ≤ I.loss x} :=
    measurableSet_le measurable_const I.loss_measurable
  unfold PublicPolicy.outputLaw AdaptiveKernel.Policy.outputLaw
  rw [map_measureReal_apply A.strategy.output_measurable hEvent]
  apply hv.trans_le
  unfold traceExperimentLaw at hv ⊢
  change (A'.strategy.historyLaw A.seedLaw (traceKernel a
    (envelopeRadius θ.μ θ.D a / Real.sqrt k) (θ.L / Real.sqrt k) v) θ.T).real _ ≤ _
  dsimp only [A', AdaptiveKernel.RandomizedPolicy.mapQueryOutput]
  rw [AdaptiveKernel.Policy.historyLaw_mapQueryOutput]
  apply measureReal_mono (μ := A.strategy.historyLaw A.seedLaw I.oracle θ.T) _ (measure_ne_top _ _)
  intro h hh
  change traceRate θ.μ θ.D θ.G θ.L θ.T ≤ traceLoss θ.μ θ.D a v (A.strategy.output h) at hh
  change ENNReal.ofReal (traceRate θ.μ θ.D θ.G θ.L θ.T) ≤ I.loss (A.strategy.output h)
  rw [gaussianPrivateInstance_loss]
  exact ENNReal.ofReal_le_ofReal hh

/-- `eq:lb-trace` for the full class, with the explicit universal constant 1/16384. -/
theorem gaussian_fixedCallMinimax_lower {k : ℕ} (θ : OracleParameters)
    (hk : 0 < k) (hT : 0 < θ.T) (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) :
    ENNReal.ofReal (traceRate θ.μ θ.D θ.G θ.L θ.T) ≤ fixedCallMinimax (HardSpace k) θ := by
  apply fixedCallMinimax_lower
  intro A
  obtain ⟨v, hv⟩ := gaussian_publicPolicy_probability_lower θ hk hT hdim
    (A (quadraticPublicProblem (HardSpace k) θ))
  exact ⟨quadraticPublicProblem (HardSpace k) θ,
    gaussianPrivateInstance θ hk hdim (traceAmplitude θ.G θ.L θ.T)
      (traceAmplitude_nonneg θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L) θ.T)
      (traceAmplitude_le_G θ.G θ.L θ.T) v, hv⟩

theorem gaussian_fixedCallMinimax_lower_of_dimension {d : ℕ} (θ : OracleParameters)
    (hT : 0 < θ.T) (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal (traceRate θ.μ θ.D θ.G θ.L θ.T) ≤ fixedCallMinimax (HardSpace d) θ := by
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hs2 : 0 < θ.s ^ 2 := sq_pos_of_pos θ.s_pos
  have hd : θ.L ^ 2 / θ.s ^ 2 ≤ (d : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hdim)
  have hdpos : (0 : ℝ) < d := (div_pos (sq_pos_of_pos hL) hs2).trans_le hd
  exact gaussian_fixedCallMinimax_lower θ (Nat.cast_pos.mp hdpos) hT
    ((div_le_iff₀ hs2).mp hd)

end
end HeavyTail.GaussianLower
