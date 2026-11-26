import SampleReuse.MarginalLazyStopping
import SampleReuse.PersistentNormalizationMeasurable
import SampleReuse.MarginalGradientCurvature

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

theorem marginalAsPersistent_measurable {Ξ H S : Type} {d : ℕ}
    [MeasurableSpace Ξ] [MeasurableSpace H] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) :
    MeasurableOracleAlgorithmFamily (fun ξ => marginalAsPersistent (P ξ)) := by
  refine ⟨⟨hP.initial,?_,hP.update⟩,hP.output⟩
  intro n
  exact ((hP.query n).fst.prodMk (hP.query n).snd.snd).prodMk (hP.query n).snd.fst

theorem marginalFromPersistent_measurable {Ξ H S : Type} {d : ℕ}
    [MeasurableSpace Ξ] [MeasurableSpace H] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm ((Bool × Point d) × H) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) :
    MeasurableOracleAlgorithmFamily (fun ξ => marginalFromPersistent (P ξ)) := by
  refine ⟨⟨hP.initial,?_,hP.update⟩,hP.output⟩
  intro n
  exact (hP.query n).fst.fst.prodMk ((hP.query n).snd.prodMk (hP.query n).fst.snd)

theorem normalizeMarginalOracle_measurable {Ξ H S : Type} {d : ℕ}
    [MeasurableSpace Ξ] [MeasurableSpace H] [MeasurableSpace S]
    [MeasurableSingletonClass H] [Countable H]
    [MeasurableSpace (List H)] [MeasurableSingletonClass (List H)]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (N : ℕ) :
    MeasurableOracleAlgorithmFamily (fun ξ => normalizeMarginalOracle N (P ξ)) :=
  marginalFromPersistent_measurable _
    (normalizePersistentAlgorithm_measurable _ (marginalAsPersistent_measurable P hP) N)

def marginalStoppingConstant (M : Parameters) : ℝ := truncatedTestingConstant*M.gradientNoise^2/16

theorem marginalStoppingConstant_pos (M : Parameters) : 0 < marginalStoppingConstant M :=
  div_pos (mul_pos truncatedTestingConstant_pos (sq_pos_of_pos M.gradientNoise_pos)) (by norm_num)

theorem marginal_stopping_radius_rate (M : Parameters) {ε : ℝ} (hε : 0 < ε) :
    truncatedTestingConstant*(marginalRadius M ε)^2 = marginalStoppingConstant M/ε^2 := by
  unfold marginalRadius marginalStoppingConstant
  field_simp [hε.ne']
  ring_nf
  simp

variable {Ξ H S : Type} {d : ℕ} [MeasurableSpace Ξ] [MeasurableSpace H] [MeasurableSpace S]
  [MeasurableSingletonClass H] [Countable H]

local instance marginalStoppingListMeasurable : MeasurableSpace (List H) := ⊤
local instance marginalStoppingListSingleton : MeasurableSingletonClass (List H) := ⟨fun _ => trivial⟩

/-- Standard measurable policies with an unlimited countable supply of opaque
handles satisfy the operational regularity automatically. -/
theorem marginal_stopping_measurable_gradient_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (stop : Ξ → ℕ → S → Bool)
    (hs : ∀ n, Measurable (fun w : Ξ × S => stop w.1 n w.2)) (idle : H)
    {ε R : ℝ} (hε : 0 < ε) {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R)
    (hsolve : ∀ θ, (2/3:ℝ) ≤ (marginalLazyLaw μ hR θ).real
      (marginalLazyStoppedSuccess P stop ε v θ)) :
    ∃ θ, ENNReal.ofReal (truncatedTestingConstant*R^2) ≤
      ∫⁻ w, marginalLazyExtendedGradientCount P stop idle ε v w ∂marginalLazyLaw μ hR θ := by
  apply marginal_stopping_gradient_lower μ P stop idle _ hε hv hR hsolve
  intro N
  exact normalizeMarginalOracle_measurable _
    (freezeOracle_measurable P hP stop hs (false,idle,0)) N

/-- A parameter-only small-epsilon threshold gives the actual admissible
appendix family and an expected gradient-call lower bound for unrestricted
stopping. Hessian calls have no cost in this conclusion. -/
theorem marginal_stopping_rate (M : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      ∃ hR : 2 ≤ marginalRadius M ε,
      ∀ v : Point d, ‖v‖=1 →
      ∀ (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
        (_hP : MeasurableOracleAlgorithmFamily P) (stop : Ξ → ℕ → S → Bool)
        (_hs : ∀ n, Measurable (fun w : Ξ × S => stop w.1 n w.2)) (idle : H),
      (∀ θ, (2/3:ℝ) ≤ (marginalLazyLaw μ hR θ).real
        (marginalLazyStoppedSuccess P stop ε v θ)) →
      ∃ θ, Admissible
        (coefficientPMF (marginalRadius M ε) (signValue θ) hR (signValue_sq θ)).toMeasure M
        (marginalLoss ε v (2*ε*signValue θ))
        (fun z : SignedCoefficient (marginalRadius M ε) => marginalLoss ε v (2*ε*z.1)) 0 ∧
        ENNReal.ofReal (marginalStoppingConstant M/ε^2) ≤
          ∫⁻ w, marginalLazyExtendedGradientCount P stop idle ε v w ∂marginalLazyLaw μ hR θ := by
  obtain ⟨η,hη,hcal⟩ := marginal_calibration M
  refine ⟨η,hη,?_⟩
  intro ε hε he
  obtain ⟨hR,hgap,hL1,hL2,hnoise,hG⟩ := hcal ε hε he
  refine ⟨hR,?_⟩
  intro v hv μ _ P hP stop hs idle hsolve
  obtain ⟨θ,hθ⟩ := marginal_stopping_measurable_gradient_lower μ P hP stop hs idle hε hv hR hsolve
  rw [marginal_stopping_radius_rate M hε] at hθ
  exact ⟨θ,marginal_sample_admissible M hε hR hv θ hgap hL1 hL2 hnoise hG,hθ⟩

end
end SampleReuse
