import SampleReuse.MarginalDirectionalInformation
import SampleReuse.MarginalStoppingRate
import SampleReuse.MarginalStoppingCost

open SecondOrder MeasureTheory
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section

theorem marginal_positive_actual_gradient_lower {Ξ S H : Type} {d : ℕ} {R : ℝ}
    [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Fintype H]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalActualLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalTableObservation P ε v N w).2‖ ≤ ε}) :
    marginalDirectionalConstant*R^2 ≤
      ∫ w, ((marginalTableObservation P ε v N w).1 : ℝ) ∂marginalActualLaw μ hR true := by
  have hs : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε} := by
    intro θ
    rw [marginal_actual_success_probability]
    exact hsuccess θ
  have hh := marginal_positive_gradient_information_lower μ P hP hε hv hR N hs
  rwa [marginal_actual_expected_gradients] at hh

theorem marginal_positive_stopping_gradient_lower {Ξ H S : Type} {d : ℕ} {R : ℝ}
    [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace (List H)]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (idle : H)
    (hN : ∀ N, MeasurableOracleAlgorithmFamily
      (fun ξ => normalizeMarginalOracle N (marginalFreeze (P ξ) (stop ξ) idle)))
    {ε : ℝ} (hε : 0 < ε) {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R)
    (hsolve : ∀ θ, (2/3:ℝ) ≤ (marginalLazyLaw μ hR θ).real
      (marginalLazyStoppedSuccess P stop ε v θ)) :
    ENNReal.ofReal (marginalDirectionalConstant*R^2) ≤
      ∫⁻ w, marginalLazyExtendedGradientCount P stop idle ε v w ∂marginalLazyLaw μ hR true := by
  let frozen := fun ξ => marginalFreeze (P ξ) (stop ξ) idle
  obtain ⟨N,hcap⟩ := binary_success_finite_horizon (fun θ => marginalLazyLaw μ hR θ)
    (marginalLazyStoppedSuccessBy P stop ε v) (marginalLazyStoppedSuccessBy_mono P stop ε v) hsolve
  have hgood (θ : Bool) : (3/5:ℝ) ≤ (marginalLazyLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalLazyObservation frozen ε v N w).2‖ ≤ ε} := by
    apply (hcap θ).trans
    apply measureReal_mono
    · intro w hw
      obtain ⟨k,hk,hstop,hgrad⟩ := hw
      change ‖gradient _ ((frozen w.1).output N (lazyPersistentRun
        (marginalAsPersistent (frozen w.1)).toQueryPolicy (marginalLazyReply ε v) w.2 N).1)‖ ≤ ε
      rw [marginalFreeze_lazy_first_stop (P w.1) (stop w.1) idle ε v w.2 hstop hk]
      exact hgrad
    · finiteness
  have htable (θ : Bool) : (3/5:ℝ) ≤ (marginalActualLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ))
        (marginalTableObservation (fun ξ => normalizeMarginalOracle N (frozen ξ)) ε v N w).2‖ ≤ ε} := by
    rw [← marginal_lazy_success_probability μ frozen N (hN N) ε v hR θ]
    exact hgood θ
  have hθ := marginal_positive_actual_gradient_lower μ
    (fun ξ => normalizeMarginalOracle N (frozen ξ)) (hN N) hε hv hR N htable
  rw [← marginal_lazy_expected_gradients μ frozen N (hN N) ε v hR true] at hθ
  have hm : Measurable (fun w : Ξ × (ℕ → SignedCoefficient R) =>
      ((marginalLazyObservation frozen ε v N w).1 : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (marginalLazyObservation_measurable frozen N (hN N) ε v).fst
  have hb (w : Ξ × (ℕ → SignedCoefficient R)) :
      ‖((marginalLazyObservation frozen ε v N w).1 : ℝ)‖ ≤ (N:ℝ) := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hh : (marginalLazyObservation frozen ε v N w).1 ≤ N := by
      dsimp only [marginalLazyObservation]
      calc
        _ ≤ ∑ _k ∈ Finset.range N, 1 := Finset.sum_le_sum (fun k _ => by split_ifs <;> omega)
        _ = N := by simp
    exact_mod_cast hh
  have hi : Integrable (fun w : Ξ × (ℕ → SignedCoefficient R) =>
      ((marginalLazyObservation frozen ε v N w).1 : ℝ)) (marginalLazyLaw μ hR true) :=
    (integrable_const (N:ℝ)).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hh := ENNReal.ofReal_le_ofReal hθ
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))] at hh
  apply hh.trans
  apply lintegral_mono
  intro w
  dsimp only
  rw [ENNReal.ofReal_natCast]
  exact le_iSup (fun N : ℕ => ((marginalLazyObservation frozen ε v N w).1 : ℝ≥0∞)) N

def marginalPositiveStoppingConstant (M : Parameters) : ℝ := marginalDirectionalConstant*M.gradientNoise^2/16

theorem marginalPositiveStoppingConstant_pos (M : Parameters) : 0 < marginalPositiveStoppingConstant M :=
  div_pos (mul_pos marginalDirectionalConstant_pos (sq_pos_of_pos M.gradientNoise_pos)) (by norm_num)

theorem marginal_positive_radius_rate (M : Parameters) {ε : ℝ} (hε : 0 < ε) :
    marginalDirectionalConstant*(marginalRadius M ε)^2 = marginalPositiveStoppingConstant M/ε^2 := by
  unfold marginalRadius marginalPositiveStoppingConstant
  field_simp [hε.ne']
  ring_nf
  simp

variable {Ξ H S : Type} {d : ℕ} [MeasurableSpace Ξ] [MeasurableSpace H] [MeasurableSpace S]
  [MeasurableSingletonClass H] [Countable H]
local instance marginalPositiveListMeasurable : MeasurableSpace (List H) := ⊤
local instance marginalPositiveListSingleton : MeasurableSingletonClass (List H) := ⟨fun _ => trivial⟩

/-- Literal positive-hypothesis appendix bound, for every ordinary measurable
stopping algorithm over an unlimited countable handle supply. -/
theorem marginal_positive_stopping_rate (M : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      ∃ hR : 2 ≤ marginalRadius M ε,
      ∀ v : Point d, ‖v‖=1 →
      ∀ (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
        (_hP : MeasurableOracleAlgorithmFamily P) (stop : Ξ → ℕ → S → Bool)
        (_hs : ∀ n, Measurable (fun w : Ξ × S => stop w.1 n w.2)) (idle : H),
      (∀ θ, (2/3:ℝ) ≤ (marginalLazyLaw μ hR θ).real
        (marginalLazyStoppedSuccess P stop ε v θ)) →
      (∀ θ, Admissible
        (coefficientPMF (marginalRadius M ε) (signValue θ) hR (signValue_sq θ)).toMeasure M
        (marginalLoss ε v (2*ε*signValue θ))
        (fun z : SignedCoefficient (marginalRadius M ε) => marginalLoss ε v (2*ε*z.1)) 0) ∧
        ENNReal.ofReal (marginalPositiveStoppingConstant M/ε^2) ≤
          ∫⁻ w, marginalLazyExtendedGradientCount P stop idle ε v w ∂marginalLazyLaw μ hR true := by
  obtain ⟨η,hη,hcal⟩ := marginal_calibration M
  refine ⟨η,hη,?_⟩
  intro ε hε he
  obtain ⟨hR,hgap,hL1,hL2,hnoise,hG⟩ := hcal ε hε he
  refine ⟨hR,?_⟩
  intro v hv μ _ P hP stop hs idle hsolve
  have hnorm (N : ℕ) : MeasurableOracleAlgorithmFamily
      (fun ξ => normalizeMarginalOracle N (marginalFreeze (P ξ) (stop ξ) idle)) :=
    normalizeMarginalOracle_measurable _ (freezeOracle_measurable P hP stop hs (false,idle,0)) N
  have hh := marginal_positive_stopping_gradient_lower μ P stop idle hnorm hε hv hR hsolve
  rw [marginal_positive_radius_rate M hε] at hh
  exact ⟨fun θ => marginal_sample_admissible M hε hR hv θ hgap hL1 hL2 hnoise hG,hh⟩

end
end SampleReuse
