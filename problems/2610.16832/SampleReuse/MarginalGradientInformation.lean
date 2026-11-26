import SampleReuse.MarginalGradientHistory
import SampleReuse.HiddenDisclosureLaw

open SecondOrder MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

variable {Ξ S Handle : Type} {d : ℕ} {R : ℝ}
  [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle]
  [MeasurableSingletonClass Handle] [Countable Handle]

local instance marginalInformation_option_measurable : MeasurableSpace (Option Handle) := ⊤
local instance marginalInformation_option_singleton : MeasurableSingletonClass (Option Handle) := ⟨fun _ => trivial⟩

def marginalCoefficientLaw (hR : 2 ≤ R) (θ : Bool) : Option Handle → PMF (SignedCoefficient R)
  | none => fairCoefficientPMF R hR
  | some _ => coefficientPMF R (signValue θ) hR (signValue_sq θ)

omit [MeasurableSpace Handle] [MeasurableSingletonClass Handle] [Countable Handle] in
theorem marginalCoefficientLaw_kl (hR : 2 ≤ R) (θ : Bool) (key : Option Handle) :
    klDiv (marginalCoefficientLaw hR θ key).toMeasure (fairCoefficientPMF R hR).toMeasure ≤
      ENNReal.ofReal (1/R^2) := by
  cases key with
  | none => simp only [marginalCoefficientLaw,klDiv_self]; exact zero_le _
  | some r => exact klDiv_coefficient R (signValue θ) hR (signValue_sq θ)

def marginalOracleLaw (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R)
    (θ : Bool) (N : ℕ) : Measure (FiniteHistory Ξ (SignedCoefficient R) N) :=
  adaptiveKernelLaw μ
    (measurableDisclosureKernel (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
      (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v)
      (marginalCoefficientLaw hR θ)) N

instance marginalOracleLaw_probability (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R)
    (θ : Bool) (N : ℕ) : IsProbabilityMeasure (marginalOracleLaw μ P hP ε v hR θ N) := by
  unfold marginalOracleLaw
  infer_instance

def marginalHiddenOracleLaw (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R)
    (N : ℕ) : Measure (FiniteHistory (Bool × Ξ) (SignedCoefficient R) N) :=
  adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
    (hiddenDisclosureKernel (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
      (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v)
      (marginalCoefficientLaw hR)) N

instance marginalHiddenOracleLaw_probability (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R)
    (N : ℕ) : IsProbabilityMeasure (marginalHiddenOracleLaw μ P hP ε v hR N) := by
  unfold marginalHiddenOracleLaw
  infer_instance

theorem marginal_classifier_success (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (2/3:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) :
    (2/3:ℝ) ≤ (marginalHiddenOracleLaw μ P hP ε v hR N).real
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
  change ENNReal.ofReal (2/3:ℝ) ≤ (marginalHiddenOracleLaw μ P hP ε v hR N) _
  change ENNReal.ofReal (2/3:ℝ) ≤ adaptiveKernelLaw _ _ _ _
  rw [he]
  calc
    _ = ∫⁻ _ : Bool, ENNReal.ofReal (2/3:ℝ) ∂(PMF.uniformOfFintype Bool).toMeasure := by
      simp only [lintegral_const,measure_univ,mul_one]
    _ ≤ _ := by
      apply lintegral_mono
      intro θ
      have hh := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hsuccess θ)
      exact hh.trans (measure_mono (fun h hs => marginal_stationary_classifies hε hv θ hs))

/-- Actual expected gradient-call lower bound for the adaptive persistent
derivative experiment. The number and locations of Hessian calls are arbitrary. -/
theorem marginal_gradient_information_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (2/3:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) :
    binaryTestingConstant*R^2 ≤ ∫ h,
      (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N
        (finiteHistoryMapInitial Prod.snd N h) : ℝ)
      ∂marginalHiddenOracleLaw μ P hP ε v hR N := by
  have hc := (marginalClassify_measurable v).comp (marginalHistoryOutput_measurable P hP ε v N (R := R))
  have hh := hidden_binary_testing_calls μ
    (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
    (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v)
    (marginalCoefficientLaw hR) (fun _ => fairCoefficientPMF R hR) (fun key => key.isSome)
    (fun θ key hn => by cases key <;> simp_all [marginalCoefficientLaw])
    (κ := 1/R^2) (by positivity) (marginalCoefficientLaw_kl hR) N
    (fun h => marginalClassify v (marginalHistoryOutput P ε v N h)) hc
    (marginal_classifier_success μ P hP hε hv hR N hsuccess)
  simp_rw [marginalHistoryGradientCount_hidden] at hh
  rw [one_div_mul_eq_div] at hh
  exact (le_div_iff₀ (sq_pos_of_pos (by linarith : 0<R))).mp hh

/-- Some actual hypothesis has the gradient-call lower bound; this removes
the hidden-prior averaging from the final conclusion. -/
theorem marginal_gradient_instance_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (2/3:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) :
    ∃ θ : Bool, binaryTestingConstant*R^2 ≤ ∫ h,
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
  have hlo := marginal_gradient_information_lower μ P hP hε hv hR N hsuccess
  change binaryTestingConstant*R^2 ≤ ∫ h, cost (finiteHistoryMapInitial Prod.snd N h)
    ∂adaptiveKernelLaw _ _ _ at hlo
  rw [he] at hlo
  let I : Bool → ℝ := fun θ => ∫ h, cost h ∂marginalOracleLaw μ P hP ε v hR θ N
  change binaryTestingConstant*R^2 ≤ ∫ θ, I θ ∂(PMF.uniformOfFintype Bool).toMeasure at hlo
  have hmean : (∫ θ, I θ ∂(PMF.uniformOfFintype Bool).toMeasure) = (I false+I true)/2 := by
    rw [PMF.integral_eq_sum]
    norm_num [Fintype.sum_bool,PMF.uniformOfFintype_apply]
    ring
  rw [hmean] at hlo
  by_contra! hn
  have hf := hn false
  have ht := hn true
  change I false < binaryTestingConstant*R^2 at hf
  change I true < binaryTestingConstant*R^2 at ht
  linarith

end
end SampleReuse
