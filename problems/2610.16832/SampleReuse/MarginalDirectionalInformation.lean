import SampleReuse.MarginalDirectionalKL
import SampleReuse.BinaryTestingTruncation

open SecondOrder InformationTheory MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section
variable {Ξ S H : Type} {d : ℕ} {R : ℝ}
  [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace H]
  [MeasurableSingletonClass H] [Countable H]

local instance marginalDirectionalOptionMeasurable : MeasurableSpace (Option H) := ⊤
local instance marginalDirectionalOptionSingleton : MeasurableSingletonClass (Option H) := ⟨fun _ => trivial⟩

def marginalDirectionalCharge
    (P : Ξ → QueryPolicy (MarginalQuery H d) (PersistentReply d) S) (ε : ℝ) (v : Point d)
    (κ : ℝ) (n : ℕ) (h : FiniteHistory Ξ (SignedCoefficient R) n) : ℝ :=
  if (marginalHistoryQuery P ε v n h).1 then κ else 0

omit [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] in
theorem marginalDirectionalCharge_total
    (P : Ξ → QueryPolicy (MarginalQuery H d) (PersistentReply d) S) (ε : ℝ) (v : Point d)
    (κ : ℝ) : ∀ n (h : FiniteHistory Ξ (SignedCoefficient R) n),
    finiteHistoryCost (marginalDirectionalCharge P ε v κ) n h =
      κ*(marginalHistoryGradientCount P ε v n h : ℝ) := by
  intro n
  induction n with
  | zero => intro h; simp only [finiteHistoryCost,marginalHistoryGradientCount,Nat.cast_zero,mul_zero]
  | succ n ih =>
    intro h
    simp only [finiteHistoryCost,marginalDirectionalCharge,marginalHistoryGradientCount,ih,Nat.cast_add]
    split_ifs <;> simp
    ring

theorem marginal_positive_negative_information (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R) (N : ℕ) :
    klDiv (marginalOracleLaw μ P hP ε v hR true N) (marginalOracleLaw μ P hP ε v hR false N) ≤
      ENNReal.ofReal ((8/R^2)*∫ h,
        (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N h : ℝ)
        ∂marginalOracleLaw μ P hP ε v hR true N) := by
  let pol := fun ξ => (P ξ).toQueryPolicy
  let query := marginalHistoryKey pol ε v (R := R)
  let hq := marginalHistoryKey_measurable pol hP.toMeasurableQueryPolicyFamily ε v (R := R)
  let c := marginalDirectionalCharge pol ε v (8/R^2) (R := R)
  have hc : ∀ n, Measurable (c n) := fun n => Measurable.ite
    (((marginalHistoryQuery_measurable pol hP.toMeasurableQueryPolicyFamily ε v n).fst)
      (measurableSet_singleton true)) measurable_const measurable_const
  have hb : ∀ n h, 0 ≤ c n h ∧ c n h ≤ 8/R^2 := by
    intro n h
    dsimp [c,marginalDirectionalCharge]
    split_ifs <;> exact ⟨by positivity,by first | exact le_rfl | positivity⟩
  have hk : ∀ n h, klDiv
      (measurableDisclosureKernel query hq (marginalCoefficientLaw hR true) n h)
      (measurableDisclosureKernel query hq (marginalCoefficientLaw hR false) n h) ≤ ENNReal.ofReal (c n h) := by
    intro n h
    change klDiv (disclosurePMF (disclosureCache query n h (query n h))
      (marginalCoefficientLaw hR true (query n h))).toMeasure
      (disclosurePMF (disclosureCache query n h (query n h))
        (marginalCoefficientLaw hR false (query n h))).toMeasure ≤ _
    by_cases hg : (marginalHistoryQuery pol ε v n h).1 = true
    · have hqv : query n h = some (marginalHistoryQuery pol ε v n h).2.1 := by
        simp only [query,marginalHistoryKey,hg,if_true]
      have hcoef : klDiv (marginalCoefficientLaw hR true (query n h)).toMeasure
          (marginalCoefficientLaw hR false (query n h)).toMeasure ≤ ENNReal.ofReal (8/R^2) := by
        simpa only [hqv,marginalCoefficientLaw,signValue] using coefficient_positive_negative_kl hR
      have hh := disclosurePMF_kl (disclosureCache query n h (query n h)) _ _ hcoef
      apply hh.trans
      dsimp only [c,marginalDirectionalCharge]
      rw [if_pos hg]
      apply ENNReal.ofReal_le_ofReal
      split_ifs <;> first | exact le_rfl | positivity
    · have hqv : query n h = none := by simp only [query,marginalHistoryKey,if_neg hg]
      rw [hqv]
      simp only [marginalCoefficientLaw,klDiv_self]
      exact zero_le _
  have hi := adaptiveKernelLaw_kl_le μ
    (measurableDisclosureKernel query hq (marginalCoefficientLaw hR true))
    (measurableDisclosureKernel query hq (marginalCoefficientLaw hR false))
    c hc (by positivity : 0 ≤ 8/R^2) hb hk N
  simpa only [c,marginalDirectionalCharge_total,integral_const_mul] using hi

def marginalDirectionalConstant : ℝ := truncatedTestingConstant/8

theorem marginalDirectionalConstant_pos : 0 < marginalDirectionalConstant :=
  div_pos truncatedTestingConstant_pos (by norm_num)

/-- The positive hypothesis itself pays the gradient cost. This is the
literal directional assertion in the manuscript's appendix. -/
theorem marginal_positive_gradient_information_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε}) :
    marginalDirectionalConstant*R^2 ≤ ∫ h,
      (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N h : ℝ)
      ∂marginalOracleLaw μ P hP ε v hR true N := by
  let E : Set (FiniteHistory Ξ (SignedCoefficient R) N) :=
    {h | marginalClassify v (marginalHistoryOutput P ε v N h) = true}
  have hE : MeasurableSet E :=
    ((marginalClassify_measurable v).comp (marginalHistoryOutput_measurable P hP ε v N))
      (measurableSet_singleton true)
  have hp : (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR true N).real E := by
    apply (hsuccess true).trans
    exact measureReal_mono (fun h hh => marginal_stationary_classifies hε hv true hh)
  have hneg : (3/5:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR false N).real Eᶜ := by
    apply (hsuccess false).trans
    apply measureReal_mono
    · intro h hh ht
      have hc := marginal_stationary_classifies hε hv false hh
      change marginalClassify v (marginalHistoryOutput P ε v N h) = true at ht
      rw [hc] at ht
      contradiction
    · finiteness
  have hq : (marginalOracleLaw μ P hP ε v hR false N).real E ≤ (1/2:ℝ) := by
    rw [measureReal_compl hE,measureReal_univ_eq_one] at hneg
    linarith
  have hlo := truncated_testing_information_ennreal hE hp hq
  have hup := marginal_positive_negative_information μ P hP ε v hR N
  have hh := (ENNReal.ofReal_le_ofReal_iff'.mp (hlo.trans hup)).resolve_right
    (not_le_of_gt truncatedTestingConstant_pos)
  have hr : 0 < R^2 := sq_pos_of_pos (by linarith)
  have hm := mul_le_mul_of_nonneg_right hh hr.le
  unfold marginalDirectionalConstant
  field_simp at hm ⊢
  nlinarith only [hm]

end
end SampleReuse
