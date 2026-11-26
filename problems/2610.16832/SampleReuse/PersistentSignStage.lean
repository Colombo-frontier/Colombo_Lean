import SampleReuse.PersistentHiddenStage
import SecondOrder.FirstOrderProgress
import SecondOrder.FirstOrderAdaptiveInformation

/-! The actual conservative sign-array law in a persistent capped stage.
Both its D/R² information bound and its 2 exp(-D/128) activation tail are
proved from the concrete coefficient distribution and smooth gate. -/

open MeasureTheory ProbabilityTheory InformationTheory SecondOrder
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section
variable {d : ℕ} {S Key : Type} [MeasurableSpace S]
  [MeasurableSpace Key] [MeasurableSingletonClass Key] [Countable Key]

def signStageTrueArray (R : ℝ) (hR : 2 ≤ R) (target : Key → Prop)
    (common : Key → PMF (Fin d → SignedCoefficient R))
    (θ : Fin d → Bool) (key : Key) : PMF (Fin d → SignedCoefficient R) :=
  if target key then firstOrderCoefficientLaw θ R hR else common key

def signStageReferenceArray (R : ℝ) (hR : 2 ≤ R) (target : Key → Prop)
    (common : Key → PMF (Fin d → SignedCoefficient R))
    (key : Key) : PMF (Fin d → SignedCoefficient R) :=
  if target key then finitePiPMF (fun _ : Fin d => fairCoefficientPMF R hR) else common key

omit [MeasurableSpace Key] [MeasurableSingletonClass Key] [Countable Key] in
theorem signStageArray_same (R : ℝ) (hR : 2 ≤ R) (target : Key → Prop)
    (common : Key → PMF (Fin d → SignedCoefficient R)) (θ : Fin d → Bool)
    (key : Key) (hn : ¬target key) :
    signStageTrueArray R hR target common θ key = signStageReferenceArray R hR target common key := by
  simp only [signStageTrueArray, signStageReferenceArray, if_neg hn]

omit [MeasurableSpace Key] [MeasurableSingletonClass Key] [Countable Key] in
theorem signStageArray_kl (R : ℝ) (hR : 2 ≤ R) (target : Key → Prop)
    (common : Key → PMF (Fin d → SignedCoefficient R)) (θ : Fin d → Bool) (key : Key) :
    klDiv (signStageTrueArray R hR target common θ key).toMeasure
      (signStageReferenceArray R hR target common key).toMeasure ≤ ENNReal.ofReal ((d : ℝ) / R ^ 2) := by
  by_cases hk : target key
  · simpa only [signStageTrueArray, signStageReferenceArray, if_pos hk,
      firstOrderCoefficientLaw, Fintype.card_fin] using
      klDiv_coefficientProduct R (fun i => signValue (θ i)) hR (fun i => signValue_sq (θ i))
  · rw [signStageArray_same R hR target common θ key hk, klDiv_self]
    exact zero_le _

def signStageActivation {R : ℝ}
    (points : ∀ n, FiniteHistory S (Fin d → SignedCoefficient R) n → Point d)
    (n : ℕ) (θ : Fin d → Bool) (h : FiniteHistory S (Fin d → SignedCoefficient R) n) : Prop :=
  0 < firstOrderBlockCompletion θ (points n h)

theorem signStageActivation_measurable {R : ℝ}
    (points : ∀ n, FiniteHistory S (Fin d → SignedCoefficient R) n → Point d)
    (hp : ∀ n, Measurable (points n)) (n : ℕ) :
    MeasurableSet {z : (Fin d → Bool) × FiniteHistory S (Fin d → SignedCoefficient R) n |
      signStageActivation points n z.1 z.2} := by
  have hy : Measurable (fun h => fun j : Fin d => points n h j) :=
    measurable_pi_iff.mpr (fun j => (EuclideanSpace.proj j).continuous.measurable.comp (hp n))
  have hm := (firstOrderEncoding_joint_measurable hy).comp measurable_swap
  have he : {z : (Fin d → Bool) × FiniteHistory S (Fin d → SignedCoefficient R) n |
      signStageActivation points n z.1 z.2} =
      {z | (1 : ℝ) / 4 < firstOrderEncoding (fun j => points n z.2 j) z.1} := by
    ext z
    simpa only [Set.mem_setOf_eq, signStageActivation, firstOrderBlockEncoding_eq] using
      firstOrderBlockCompletion_pos_iff z.1 (points n z.2)
  rw [he]
  exact measurableSet_lt measurable_const hm

omit [MeasurableSpace S] in
theorem signStageActivation_tail {R : ℝ}
    (points : ∀ n, FiniteHistory S (Fin d → SignedCoefficient R) n → Point d)
    (n : ℕ) (h : FiniteHistory S (Fin d → SignedCoefficient R) n) :
    (signLaw d).real {θ | signStageActivation points n θ h} ≤ 2 * Real.exp (-(d : ℝ) / 128) := by
  have hh := ENNReal.toReal_mono (by finiteness) (firstOrderBlockCompletion_activation_tail (points n h))
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

/-- A target-stage continuation using persistent biased sign arrays has
activation probability at most 1/32 under explicit entropy/horizon scalars.
The query and terminal-output points can be arbitrary measurable functions
of the entire cached transcript and private seed. -/
theorem persistent_sign_stage_one_thirty_second
    (μ : Measure S) [IsProbabilityMeasure μ] (R : ℝ) (hR : 2 ≤ R)
    (query : ∀ n, FiniteHistory S (Fin d → SignedCoefficient R) n → Key)
    (hq : ∀ n, Measurable (query n)) (target : Key → Prop)
    (common : Key → PMF (Fin d → SignedCoefficient R))
    (cap : ℕ) (dummy : ∀ n, Kernel (FiniteHistory S (Fin d → SignedCoefficient R) n)
      (Fin d → SignedCoefficient R)) [∀ n, IsMarkovKernel (dummy n)]
    (points : ∀ n, FiniteHistory S (Fin d → SignedCoefficient R) n → Point d)
    (hp : ∀ n, Measurable (points n)) (N : ℕ)
    {L : ℝ} (hL : 0 < L)
    (hlog : L ≤ Real.log (1 / ((N + 1 : ℕ) * (2 * Real.exp (-(d : ℝ) / 128)))))
    (hbudget : 32 * ((cap : ℝ) * ((d : ℝ) / R ^ 2) + Real.log 2) ≤ L) :
    (kernelStageTrueLaw (signLaw d) μ (targetDisclosure query target)
      (targetDisclosure_measurable query hq target) cap
      (hiddenDisclosureKernel query hq (signStageTrueArray R hR target common)) dummy N).real
      (kernelSurvivalSet (fun n => (kernelHiddenEvent (signStageActivation points) n)ᶜ) N)ᶜ ≤ 1 / 32 := by
  apply (persistent_stage_firstActivation_bound (signLaw d) μ query hq
    (signStageTrueArray R hR target common) (signStageReferenceArray R hR target common) target
    (signStageArray_same R hR target common) cap dummy (by positivity)
    (signStageArray_kl R hR target common) (signStageActivation points)
    (signStageActivation_measurable points hp) (by positivity)
    (signStageActivation_tail points) N hL hlog).trans
  apply (div_le_iff₀ hL).mpr
  linarith only [hbudget]

end
end SampleReuse
