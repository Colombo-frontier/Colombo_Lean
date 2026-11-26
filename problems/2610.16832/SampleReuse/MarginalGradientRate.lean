import SampleReuse.MarginalGradientInformation

open SecondOrder MeasureTheory

namespace SampleReuse
noncomputable section

def marginalRateConstant (M : Parameters) : ℝ := binaryTestingConstant*M.gradientNoise^2/16

theorem marginalRateConstant_pos (M : Parameters) : 0 < marginalRateConstant M := by
  unfold marginalRateConstant
  exact div_pos (mul_pos binaryTestingConstant_pos (sq_pos_of_pos M.gradientNoise_pos)) (by norm_num)

theorem marginal_radius_rate (M : Parameters) {ε : ℝ} (hε : 0 < ε) :
    binaryTestingConstant*(marginalRadius M ε)^2 = marginalRateConstant M/ε^2 := by
  unfold marginalRadius marginalRateConstant
  field_simp [ne_of_gt hε]
  ring_nf
  simp

/-- The calibrated marginal-gradient lower bound. Both hypotheses are actual
admissible common-loss models. Any measurable adaptive policy succeeding for
both has a hypothesis requiring Omega(epsilon^-2) expected gradient calls,
with any finite number of uncharged Hessian queries and persistent reuse. -/
theorem marginal_gradient_rate (M : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      ∃ hR : 2 ≤ marginalRadius M ε,
      ∀ (d : ℕ) (v : Point d), ‖v‖=1 →
        (∀ θ : Bool, Admissible
          (coefficientPMF (marginalRadius M ε) (signValue θ) hR (signValue_sq θ)).toMeasure M
          (marginalLoss ε v (2*ε*signValue θ))
          (fun a : SignedCoefficient (marginalRadius M ε) => marginalLoss ε v (2*ε*a.1)) 0) ∧
        ∀ (Ξ S Handle : Type) [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle]
          [MeasurableSingletonClass Handle] [Countable Handle]
          (μ : Measure Ξ) [IsProbabilityMeasure μ]
          (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
          (hP : MeasurableOracleAlgorithmFamily P) (N : ℕ),
          (∀ θ : Bool, (2/3:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
            {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) →
          ∃ θ : Bool, marginalRateConstant M/ε^2 ≤ ∫ h,
            (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N h : ℝ)
            ∂marginalOracleLaw μ P hP ε v hR θ N := by
  obtain ⟨η,hη,hcal⟩ := marginal_calibration M
  refine ⟨η,hη,fun ε hε he => ?_⟩
  obtain ⟨hR,hgap,hL1,hL2,hnoise,hG⟩ := hcal ε hε he
  refine ⟨hR,fun d v hv => ⟨?_,?_⟩⟩
  · intro θ
    exact marginal_sample_admissible M hε hR hv θ hgap hL1 hL2 hnoise hG
  · intro Ξ S Handle _ _ _ _ _ μ _ P hP N hsuccess
    obtain ⟨θ,hθ⟩ := marginal_gradient_instance_lower μ P hP hε hv hR N hsuccess
    exact ⟨θ,by simpa only [marginal_radius_rate M hε] using hθ⟩

end
end SampleReuse
