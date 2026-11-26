import SampleReuse.MarginalGradientTableLower
import SampleReuse.BinaryTestingTruncation

open SecondOrder MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

variable {Ξ S Handle : Type} {d : ℕ} {R : ℝ}
  [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle]
  [MeasurableSingletonClass Handle] [Countable Handle]

local instance marginalTruncation_option_measurable : MeasurableSpace (Option Handle) := ⊤
local instance marginalTruncation_option_singleton : MeasurableSingletonClass (Option Handle) := ⟨fun _ => trivial⟩

theorem truncated_marginal_classifier_success (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) :
    (3/5:ℝ) ≤ (marginalHiddenOracleLaw μ P hP ε v hR N).real
      {h | marginalClassify v (marginalHistoryOutput P ε v N (finiteHistoryMapInitial Prod.snd N h)) =
        (finiteHistoryInitial N h).1} := by
  have hc := (marginalClassify_measurable v).comp (marginalHistoryOutput_measurable P hP ε v N (R := R))
  have hE : MeasurableSet {z : Bool × FiniteHistory Ξ (SignedCoefficient R) N |
      marginalClassify v (marginalHistoryOutput P ε v N z.2) = z.1} :=
    measurableSet_eq_fun_of_countable (hc.comp measurable_snd) measurable_fst
  have he := hiddenDisclosure_event (PMF.uniformOfFintype Bool).toMeasure μ
    (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
    (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v)
    (marginalCoefficientLaw hR) N
    (fun θ h => marginalClassify v (marginalHistoryOutput P ε v N h) = θ) hE
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  change ENNReal.ofReal (3/5:ℝ) ≤ (marginalHiddenOracleLaw μ P hP ε v hR N) _
  change ENNReal.ofReal (3/5:ℝ) ≤ adaptiveKernelLaw _ _ _ _
  rw [he]
  calc
    _ = ∫⁻ _ : Bool, ENNReal.ofReal (3/5:ℝ) ∂(PMF.uniformOfFintype Bool).toMeasure := by
      simp only [lintegral_const,measure_univ,mul_one]
    _ ≤ _ := by
      apply lintegral_mono
      intro θ
      have hh := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hsuccess θ)
      exact hh.trans (measure_mono (fun h hs => marginal_stationary_classifies hε hv θ hs))

/-- Actual expected gradient-call lower bound for the adaptive persistent
derivative experiment. The number and locations of Hessian calls are arbitrary. -/
theorem truncated_marginal_gradient_information_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) :
    truncatedTestingConstant*R^2 ≤ ∫ h,
      (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N
        (finiteHistoryMapInitial Prod.snd N h) : ℝ)
      ∂marginalHiddenOracleLaw μ P hP ε v hR N := by
  have hc := (marginalClassify_measurable v).comp (marginalHistoryOutput_measurable P hP ε v N (R := R))
  have hh := truncated_hidden_binary_testing_calls μ
    (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
    (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v)
    (marginalCoefficientLaw hR) (fun _ => fairCoefficientPMF R hR) (fun key => key.isSome)
    (fun θ key hn => by cases key <;> simp_all [marginalCoefficientLaw])
    (κ := 1/R^2) (by positivity) (marginalCoefficientLaw_kl hR) N
    (fun h => marginalClassify v (marginalHistoryOutput P ε v N h)) hc
    (truncated_marginal_classifier_success μ P hP hε hv hR N hsuccess)
  simp_rw [marginalHistoryGradientCount_hidden] at hh
  rw [one_div_mul_eq_div] at hh
  exact (le_div_iff₀ (sq_pos_of_pos (by linarith : 0<R))).mp hh

/-- Some actual hypothesis has the gradient-call lower bound; this removes
the hidden-prior averaging from the final conclusion. -/
theorem truncated_marginal_gradient_instance_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) :
    ∃ θ : Bool, truncatedTestingConstant*R^2 ≤ ∫ h,
      (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N h : ℝ)
      ∂marginalOracleLaw μ P hP ε v hR θ N := by
  classical
  let cost : FiniteHistory Ξ (SignedCoefficient R) N → ℝ := fun h =>
    marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N h
  have hm : Measurable cost := (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
    (marginalHistoryGradientCount_measurable _ hP.toMeasurableQueryPolicyFamily ε v N)
  have hb (h : FiniteHistory Ξ (SignedCoefficient R) N) : ‖cost h‖ ≤ (N:ℝ) := by
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ cost h)]
    dsimp [cost]
    exact_mod_cast marginalHistoryGradientCount_le (fun ξ => (P ξ).toQueryPolicy) ε v N h
  have he := hiddenDisclosure_integral (PMF.uniformOfFintype Bool).toMeasure μ
    (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
    (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v)
    (marginalCoefficientLaw hR) N (fun z => cost z.2) (hm.comp measurable_snd) N (fun z => hb z.2)
  have hlo := truncated_marginal_gradient_information_lower μ P hP hε hv hR N hsuccess
  change truncatedTestingConstant*R^2 ≤ ∫ h, cost (finiteHistoryMapInitial Prod.snd N h)
    ∂adaptiveKernelLaw _ _ _ at hlo
  rw [he] at hlo
  let I : Bool → ℝ := fun θ => ∫ h, cost h ∂marginalOracleLaw μ P hP ε v hR θ N
  change truncatedTestingConstant*R^2 ≤ ∫ θ, I θ ∂(PMF.uniformOfFintype Bool).toMeasure at hlo
  have hmean : (∫ θ, I θ ∂(PMF.uniformOfFintype Bool).toMeasure) = (I false+I true)/2 := by
    rw [PMF.integral_eq_sum]
    norm_num [Fintype.sum_bool,PMF.uniformOfFintype_apply]
    ring
  rw [hmean] at hlo
  by_contra! hn
  have hf := hn false
  have ht := hn true
  change I false < truncatedTestingConstant*R^2 at hf
  change I true < truncatedTestingConstant*R^2 at ht
  linarith

theorem truncated_marginal_actual_gradient_lower [Fintype Handle]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalActualLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalTableObservation P ε v N w).2‖ ≤ ε}) :
    ∃ θ : Bool, truncatedTestingConstant*R^2 ≤
      ∫ w, ((marginalTableObservation P ε v N w).1 : ℝ) ∂marginalActualLaw μ hR θ := by
  have hs : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε} := by
    intro θ
    rw [marginal_actual_success_probability]
    exact hsuccess θ
  obtain ⟨θ,hθ⟩ := truncated_marginal_gradient_instance_lower μ P hP hε hv hR N hs
  exact ⟨θ,by rwa [marginal_actual_expected_gradients] at hθ⟩

end
end SampleReuse
