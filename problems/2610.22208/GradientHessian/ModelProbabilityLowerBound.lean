import GradientHessian.MachineJointSuccess
import GradientHessian.Model

/-! A finite-cutoff hard-law probability bound excludes an unrestricted
model guarantee. The input-dependent unbounded stopping time is handled by
the exact increasing success union and the product-measure identity. -/

noncomputable section
namespace GradientHessian.Model
open Classical MeasureTheory Machine
open scoped ENNReal

theorem not_guarantees_of_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d G H : ℕ} {T : ℝ}
    (f : Ω → Point d → ℝ) (A : Algorithm d) :
    letI := A.seedSpace
    letI := A.stateSpace
    letI := A.probability
    Measurable (fun q : Ω × Point d => ordinaryOracle (f q.1) q.2) →
    Measurable (fun q : Ω × Point d => richOracle (f q.1) q.2) →
    (∀ᵐ w ∂μ,Admissible T (f w)) →
    ((∀ᵐ w ∂μ,A.policy.HasCaps (ordinaryOracle (f w)) (richOracle (f w)) G H) →
      ∀ N : ℕ,(μ.prod A.seedLaw).real {q | A.policy.output
        (A.policy.run (ordinaryOracle (f q.1)) (richOracle (f q.1)) N q.2)∈stationary (f q.1)}≤1/32) →
    ¬A.Guarantees T G H := by
  letI := A.seedSpace
  letI := A.stateSpace
  letI := A.probability
  intro ho hr hadmissible hcut hA
  let good : Set (Ω × Point d) := {q | q.2∈stationary (f q.1)}
  have hg : MeasurableSet good := by
    change MeasurableSet {q : Ω × Point d | ‖fderiv ℝ (f q.1) q.2‖≤1}
    exact measurableSet_le ho.snd.norm measurable_const
  have hcaps : ∀ᵐ w ∂μ,A.policy.HasCaps (ordinaryOracle (f w)) (richOracle (f w)) G H := by
    filter_upwards [hadmissible] with w hw
    exact (hA (f w) hw).2.1
  have hlo : (2/3 : ℝ≥0∞)≤(μ.prod A.seedLaw)
      (A.policy.jointSuccess (fun w => ordinaryOracle (f w)) (fun w => richOracle (f w)) good) := by
    apply A.policy.joint_success_lower _ _ good ho hr hg μ A.seedLaw (2/3)
    filter_upwards [hadmissible] with w hw
    exact (hA (f w) hw).2.2
  have hup : (μ.prod A.seedLaw)
      (A.policy.jointSuccess (fun w => ordinaryOracle (f w)) (fun w => richOracle (f w)) good)≤(1/32 : ℝ≥0∞) := by
    apply A.policy.joint_success_le_of_cutoffs _ _ good (μ.prod A.seedLaw) (1/32)
    intro N
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num : (1/32 : ℝ≥0∞)≠⊤)).mp
    simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hcut hcaps N
  have hb := ENNReal.toReal_mono (by norm_num : (1/32 : ℝ≥0∞)≠⊤) (hlo.trans hup)
  norm_num [ENNReal.toReal_div] at hb

end GradientHessian.Model
