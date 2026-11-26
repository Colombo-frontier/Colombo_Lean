import HeavyTail.GaussianAdaptiveLikelihood
import HeavyTail.GaussianTestingHypercube
import HeavyTail.GaussianCalibration

/-! Actual objective-error probability lower bound for the adaptive Gaussian
hypercube family. Pairwise testing and the Hamming event are derived from the
constructed Gaussian history laws, for arbitrary measurable seed laws. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal
namespace HeavyTail.GaussianLower
noncomputable section

def hardDecode {k : ℕ} (x : HardSpace k) (j : Fin k) : Bool :=
  if x j ≤ 0 then false else true

lemma hardDecode_measurable {k : ℕ} (j : Fin k) :
    Measurable (fun x : HardSpace k ↦ hardDecode x j) := by
  unfold hardDecode
  exact Measurable.ite ((EuclideanSpace.proj j).continuous.measurable measurableSet_Iic)
    measurable_const measurable_const

lemma hardDecode_wrong_iff {k : ℕ} (x : HardSpace k) (v : Fin k → Bool) (j : Fin k) :
    hardDecode x j ≠ v j ↔ decodeSign (x j) ≠ gaussianSigns v j := by
  cases hv : v j <;> by_cases hx : x j ≤ 0 <;> norm_num [hardDecode, decodeSign, gaussianSigns, hv, hx]

theorem decodedHamming_eq_signHamming {k : ℕ} (x : HardSpace k) (v : Fin k → Bool) :
    decodedHamming (fun x : HardSpace k ↦ hardDecode x) v x =
      (signHamming (gaussianSigns v) (fun j ↦ x j) : ℝ) := by
  classical
  simp only [decodedHamming, signHamming, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, hardDecode_wrong_iff]

def traceKernel {k : ℕ} (a ρ σ : ℝ) (v : Fin k → Bool) : Kernel (HardSpace k) (HardSpace k) :=
  gaussianResponseKernel (hardGradient a ρ (gaussianSigns v))
    (hardGradient_measurable a ρ (gaussianSigns v)) σ

instance traceKernel_markov {k : ℕ} (a ρ σ : ℝ) (v : Fin k → Bool) :
    IsMarkovKernel (traceKernel a ρ σ v) := by unfold traceKernel; infer_instance

lemma normalized_gap_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : ℝ) (x : E) : ‖σ⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / σ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  ring

variable {Seed : Type} [MeasurableSpace Seed] {k T : ℕ}

theorem gaussian_hypercube_pair_testing (hk : 0 < k)
    (A : AdaptiveKernel.Policy Seed (HardSpace k) (HardSpace k) (HardSpace k) T)
    (P : Measure Seed) [IsProbabilityMeasure P] (a ρ : ℝ) {L : ℝ} (hL : 0 < L)
    (hsmall : Real.exp ((T : ℝ) * (4 * a ^ 2 / L ^ 2)) ≤ (65 / 64 : ℝ))
    (v : Fin k → Bool) (j : Fin k) :
    (7 / 8 : ℝ) ≤
      hypercubeBitError (fun v ↦ A.historyLaw P (traceKernel a ρ (L / Real.sqrt k) v) T)
        (fun h ↦ hardDecode (A.output h)) v j +
      hypercubeBitError (fun v ↦ A.historyLaw P (traceKernel a ρ (L / Real.sqrt k) v) T)
        (fun h ↦ hardDecode (A.output h)) (gaussianFlip v j) j := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hσ : L / Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hd (i : Fin k) : Measurable (fun h ↦ hardDecode (A.output h) i) :=
    (hardDecode_measurable i).comp A.output_measurable
  have hbound (x : HardSpace k) :
      ‖(L / Real.sqrt (k : ℝ))⁻¹ • (hardGradient a ρ (gaussianSigns (gaussianFlip v j)) x -
        hardGradient a ρ (gaussianSigns v) x)‖ ^ 2 ≤ 4 * a ^ 2 / L ^ 2 := by
    rw [normalized_gap_square, norm_sub_rev]
    exact gaussian_neighbor_normalized_signal hk hL a ρ v j x
  have ht := adaptive_gaussian_testing_lower A P
    (hardGradient_measurable a ρ (gaussianSigns v))
    (hardGradient_measurable a ρ (gaussianSigns (gaussianFlip v j))) hσ hbound hsmall
    (bitErrorSet_measurable hd v j)
  rw [← flipped_errorSet_compl (fun h ↦ hardDecode (A.output h)) v j] at ht
  exact ht

def traceObjective {k : ℕ} (μ D a : ℝ) (v : Fin k → Bool) (x : HardSpace k) : ℝ :=
  hardLoss a (envelopeRadius μ D a / Real.sqrt k) (gaussianSigns v) x + hardRegularizer μ x

def traceLoss {k : ℕ} (μ D a : ℝ) (v : Fin k → Bool) (x : HardSpace k) : ℝ :=
  traceObjective μ D a v x - traceObjective μ D a v (hardCenter μ D a (gaussianSigns v))

theorem gaussian_objective_probability_lower (hk : 0 < k)
    (A : AdaptiveKernel.Policy Seed (HardSpace k) (HardSpace k) (HardSpace k) T)
    (P : Measure Seed) [IsProbabilityMeasure P] {μ D a L : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a) (hL : 0 < L)
    (hsmall : Real.exp ((T : ℝ) * (4 * a ^ 2 / L ^ 2)) ≤ (65 / 64 : ℝ)) :
    ∃ v : Fin k → Bool,
      (1 / 4 : ℝ) ≤
        (A.historyLaw P (traceKernel a (envelopeRadius μ D a / Real.sqrt k)
          (L / Real.sqrt k) v) T).real
          {h | envelope μ D a / 4 ≤ traceLoss μ D a v (A.output h)} := by
  let Q := fun v : Fin k → Bool ↦ A.historyLaw P
    (traceKernel a (envelopeRadius μ D a / Real.sqrt k) (L / Real.sqrt k) v) T
  let decode := fun h ↦ hardDecode (A.output h)
  have hd (i : Fin k) : Measurable (fun h ↦ decode h i) :=
    (hardDecode_measurable i).comp A.output_measurable
  obtain ⟨v, hv⟩ := exists_hypercube_hamming_probability hk Q hd
    (gaussian_hypercube_pair_testing hk A P a (envelopeRadius μ D a / Real.sqrt k) hL hsmall)
  refine ⟨v, hv.trans (measureReal_mono ?_)⟩
  intro h hh
  have hgap := hardComposite_loss_hamming hk hμ hD ha (gaussianSigns v) (gaussianSigns_mem v)
    (A.output h)
  have hJ : (k : ℝ) / 4 ≤ (signHamming (gaussianSigns v) (fun j ↦ A.output h j) : ℝ) := by
    change (k : ℝ) / 4 ≤ decodedHamming (fun x : HardSpace k ↦ hardDecode x) v (A.output h) at hh
    simpa only [decodedHamming_eq_signHamming] using hh
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hmul := mul_le_mul_of_nonneg_left hJ
    (div_nonneg (envelope_nonneg hμ hD ha) hkR.le)
  have he : envelope μ D a / (k : ℝ) * ((k : ℝ) / 4) = envelope μ D a / 4 := by
    field_simp
  rw [he] at hmul
  exact hmul.trans hgap

end
end HeavyTail.GaussianLower

