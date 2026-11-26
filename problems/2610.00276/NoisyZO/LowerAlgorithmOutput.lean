import NoisyZO.LowerDecisionCore
import NoisyZO.HardAdmissibility
import NoisyZO.HardQuantitativeCertificate
import NoisyZO.EventPinsker

/-!
# Returned-point laws for adaptive Gaussian algorithms

An algorithm's final measurable output is pushed forward from its adaptive
Gaussian state law.  This removes the abstract family of output measures from
the lower-rate theorem.  If the algorithm returns a point in the unit ball,
the required objective-gap integrability is automatic.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NoisyZO

noncomputable section

/-- Distribution of the point returned from the final adaptive Gaussian
state under hard-family vertex `s`. -/
def hardAdaptiveOutputLaw
    {α : Type*} [MeasurableSpace α] {d : ℕ}
    (μ₀ : Measure α) (c h : ℝ) (hh : 0 < h)
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (T : ℕ) (output : α → Point d) (s : Hypercube d) :
    Measure (Point d) :=
  Measure.map output
    (adaptiveGaussianLaw μ₀
      (hardGaussianMean c h hh query s)
      (hardGaussianMean_measurable c h hh query hquery s)
      update hupdate T)

/-- A measurable returned point pushes the final transcript probability law
to a probability law. -/
theorem hardAdaptiveOutputLaw_isProbability
    {α : Type*} [MeasurableSpace α] {d : ℕ}
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (c h : ℝ) (hh : 0 < h)
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (T : ℕ) (output : α → Point d) (s : Hypercube d) :
    IsProbabilityMeasure
      (hardAdaptiveOutputLaw μ₀ c h hh query hquery update hupdate T output s) := by
  let _ : IsProbabilityMeasure
      (adaptiveGaussianLaw μ₀
        (hardGaussianMean c h hh query s)
        (hardGaussianMean_measurable c h hh query hquery s)
        update hupdate T) :=
    adaptiveGaussianLaw_isProbability μ₀
      (hardGaussianMean c h hh query s)
      (hardGaussianMean_measurable c h hh query hquery s)
      update hupdate T
  unfold hardAdaptiveOutputLaw
  infer_instance

/-- The event distance between neighboring returned-point laws satisfies Pinsker automatically.
Finiteness of KL follows from the bounded hard-family signal and the finite Gaussian transcript. -/
theorem hardAdaptiveOutputLaw_event_pinsker
    {α : Type*} [MeasurableSpace α] {d T : ℕ} (hd : 0 < d)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (c h : ℝ) (hh : 0 < h)
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (output : α → Point d) (houtput : Measurable output)
    (s : Hypercube d) (i : Fin d) :
    assouadEdgeEventDistance
        (hardAdaptiveOutputLaw μ₀ c h hh query hquery update hupdate T output) s i ≤
      Real.sqrt
        ((InformationTheory.klDiv
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean c h hh query s)
            (hardGaussianMean_measurable c h hh query hquery s)
            update hupdate T)
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean c h hh query (flipHypercube s i))
            (hardGaussianMean_measurable c h hh query hquery (flipHypercube s i))
            update hupdate T)).toReal / 2) := by
  let P : Measure α :=
    adaptiveGaussianLaw μ₀
      (hardGaussianMean c h hh query s)
      (hardGaussianMean_measurable c h hh query hquery s)
      update hupdate T
  let Q : Measure α :=
    adaptiveGaussianLaw μ₀
      (hardGaussianMean c h hh query (flipHypercube s i))
      (hardGaussianMean_measurable c h hh query hquery (flipHypercube s i))
      update hupdate T
  let _ : IsProbabilityMeasure P :=
    adaptiveGaussianLaw_isProbability μ₀
      (hardGaussianMean c h hh query s)
      (hardGaussianMean_measurable c h hh query hquery s)
      update hupdate T
  let _ : IsProbabilityMeasure Q :=
    adaptiveGaussianLaw_isProbability μ₀
      (hardGaussianMean c h hh query (flipHypercube s i))
      (hardGaussianMean_measurable c h hh query hquery (flipHypercube s i))
      update hupdate T
  let E : Set (Point d) := assouadErrorSet s i
  have hE : MeasurableSet E := assouadErrorSet_measurable s i
  have hfinite : InformationTheory.klDiv P Q ≠ ∞ := by
    exact hardAdaptiveGaussianLaw_edge_kl_ne_top hd μ₀ c h hh
      query hquery update hupdate s i
  have hpinsker := abs_probReal_sub_probReal_le_sqrt_klDiv
    P Q (hE.preimage houtput) hfinite
  change |(Measure.map output P).real E - (Measure.map output Q).real E| ≤
    Real.sqrt ((InformationTheory.klDiv P Q).toReal / 2)
  rw [map_measureReal_apply houtput hE, map_measureReal_apply houtput hE]
  exact hpinsker

/-- Unit-ball-valued returned points have integrable objective gap under the
concrete pushforward output law. -/
theorem NormalizedObjective.hardAdaptiveOutputLaw_gap_integrable
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d : ℕ}
    (F : NormalizedObjective o d)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (c h : ℝ) (hh : 0 < h)
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (T : ℕ) (output : α → Point d) (houtput : Measurable output)
    (houtput_mem : ∀ a, ‖output a‖ ≤ 1) (s : Hypercube d) :
    Integrable (fun x ↦ F.f x - F.f F.minimizer)
      (hardAdaptiveOutputLaw μ₀ c h hh query hquery update hupdate T output s) := by
  let μ : Measure α :=
    adaptiveGaussianLaw μ₀
      (hardGaussianMean c h hh query s)
      (hardGaussianMean_measurable c h hh query hquery s)
      update hupdate T
  let _ : IsProbabilityMeasure μ :=
    adaptiveGaussianLaw_isProbability μ₀
      (hardGaussianMean c h hh query s)
      (hardGaussianMean_measurable c h hh query hquery s)
      update hupdate T
  have hgapMeas : AEStronglyMeasurable
      (fun x ↦ F.f x - F.f F.minimizer) (Measure.map output μ) :=
    (F.smooth.continuous.sub continuous_const).aestronglyMeasurable
  apply (integrable_map_measure hgapMeas houtput.aemeasurable).2
  have hcompMeas : AEStronglyMeasurable
      ((fun x ↦ F.f x - F.f F.minimizer) ∘ output) μ :=
    ((F.smooth.continuous.sub continuous_const).measurable.comp houtput).aestronglyMeasurable
  apply (integrable_const (18 : ℝ)).mono' hcompMeas
  filter_upwards with a
  change |F.f (output a) - F.f F.minimizer| ≤ 18
  rw [abs_of_nonneg (F.gap_nonneg (output a))]
  exact F.gap_le_eighteen_of_norm_le (houtput_mem a)

/-- The normalized radial hard family assembled from its remaining analytic
certificate. -/
def radialHardObjectiveFamily
    {o : SmoothnessOrder} {d : ℕ} (c h : ℝ) (hh : 0 < h)
    (cert : ∀ s : Hypercube d,
      HardAnalyticCertificate o d
        (radialCutoff d h hh) (c / Real.sqrt d) (hypercubeSign s))
    (s : Hypercube d) : NormalizedObjective o d :=
  hardNormalizedObjective
    (radialCutoff d h hh) (c / Real.sqrt d) (hypercubeSign s) (cert s)

/-- The radial hard objective has exactly the signed center required by the
decision reduction. -/
theorem radialHardObjectiveFamily_minimizer
    {o : SmoothnessOrder} {d : ℕ} (c h : ℝ) (hh : 0 < h)
    (cert : ∀ s : Hypercube d,
      HardAnalyticCertificate o d
        (radialCutoff d h hh) (c / Real.sqrt d) (hypercubeSign s))
    (s : Hypercube d) :
    (radialHardObjectiveFamily c h hh cert s).minimizer =
      signCenter (c / (2 * Real.sqrt d)) s := by
  change hardCenter (c / Real.sqrt d) (hypercubeSign s) = _
  exact hardCenter_hypercubeSign_eq_signCenter c s

/-- Full adaptive lower rate for the measurable point returned by an algorithm.  The abstract
output-law, finite-risk, and event-level Pinsker premises are all discharged. -/
theorem hard_family_adaptive_gaussian_lower_rate_of_algorithm_output
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (output : α → Point d) (houtput : Measurable output)
    (houtput_mem : ∀ z, ‖output z‖ ≤ 1)
    (F : Hypercube d → NormalizedObjective o d)
    (hmin : ∀ s,
      (F s).minimizer =
        signCenter
          ((a * lowerBandwidth a d T β ^ (β - 1)) /
            (2 * Real.sqrt d)) s) :
    (3 * a ^ 2 / 64) *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β) ≤
      (∑ s : Hypercube d,
        (∫ x, (F s).f x - (F s).f (F s).minimizer
          ∂hardAdaptiveOutputLaw μ₀
            (a * lowerBandwidth a d T β ^ (β - 1))
            (lowerBandwidth a d T β)
            (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
              (lt_trans (by norm_num) hβ))
            query hquery update hupdate T output s)) /
          (2 : ℝ) ^ d := by
  let hh : 0 < lowerBandwidth a d T β :=
    lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
      (lt_trans (by norm_num) hβ)
  let law : Hypercube d → Measure (Point d) :=
    hardAdaptiveOutputLaw μ₀
      (a * lowerBandwidth a d T β ^ (β - 1))
      (lowerBandwidth a d T β) hh
      query hquery update hupdate T output
  let _ : ∀ s, IsProbabilityMeasure (law s) := fun s ↦
    hardAdaptiveOutputLaw_isProbability μ₀
      (a * lowerBandwidth a d T β ^ (β - 1))
      (lowerBandwidth a d T β) hh
      query hquery update hupdate T output s
  apply hard_family_adaptive_gaussian_lower_rate_of_output_laws
    hd hT β a hβ ha ha4 μ₀ query hquery update hupdate law F hmin
  · intro s
    exact (F s).hardAdaptiveOutputLaw_gap_integrable μ₀
      (a * lowerBandwidth a d T β ^ (β - 1))
      (lowerBandwidth a d T β) hh query hquery update hupdate T
      output houtput houtput_mem s
  · intro s i
    simpa only [law, hh] using
      hardAdaptiveOutputLaw_event_pinsker hd μ₀
        (a * lowerBandwidth a d T β ^ (β - 1))
        (lowerBandwidth a d T β) hh query hquery update hupdate
        output houtput s i

/-- The preceding algorithm-output rate specialized to the explicit radial hard family.  Only its
quantitative analytic certificate remains as an interface. -/
theorem hard_family_adaptive_gaussian_lower_rate_of_radial_certificate
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (output : α → Point d) (houtput : Measurable output)
    (houtput_mem : ∀ z, ‖output z‖ ≤ 1)
    (c h : ℝ) (hh : 0 < h)
    (hc : c = a * lowerBandwidth a d T β ^ (β - 1))
    (hband : h = lowerBandwidth a d T β)
    (cert : ∀ s : Hypercube d,
      HardAnalyticCertificate o d
        (radialCutoff d h hh) (c / Real.sqrt d) (hypercubeSign s)) :
    (3 * a ^ 2 / 64) *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β) ≤
      (∑ s : Hypercube d,
        (∫ x,
          (radialHardObjectiveFamily c h hh cert s).f x -
            (radialHardObjectiveFamily c h hh cert s).f
              (radialHardObjectiveFamily c h hh cert s).minimizer
          ∂hardAdaptiveOutputLaw μ₀ c h hh
            query hquery update hupdate T output s)) /
          (2 : ℝ) ^ d := by
  subst c
  subst h
  apply hard_family_adaptive_gaussian_lower_rate_of_algorithm_output
    hd hT β a hβ ha ha4 μ₀ query hquery update hupdate
    output houtput houtput_mem
    (radialHardObjectiveFamily
      (a * lowerBandwidth a d T β ^ (β - 1))
      (lowerBandwidth a d T β) hh cert)
  · intro s
    exact radialHardObjectiveFamily_minimizer
      (a * lowerBandwidth a d T β ^ (β - 1))
      (lowerBandwidth a d T β) hh cert s

/-- Canonical rate-scaled radial objective built from only the two remaining
perturbation derivative estimates. -/
def lowerRateHardObjective
    {o : SmoothnessOrder} {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (cert : ∀ s : Hypercube d,
      RadialHardQuantitativeCertificate o d
        (a * lowerBandwidth a d T β ^ (β - 1))
        (lowerBandwidth a d T β)
        (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
          (lt_trans (by norm_num) hβ)) s)
    (s : Hypercube d) : NormalizedObjective o d :=
  rateRadialHardObjective hd β a (lowerBandwidth a d T β)
    hβ ha ha4
    (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
      (lt_trans (by norm_num) hβ))
    (lowerBandwidth_le_one a d T β) s (cert s)

/-- Exact minimizer of the canonical rate-scaled hard objective. -/
theorem lowerRateHardObjective_minimizer
    {o : SmoothnessOrder} {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (cert : ∀ s : Hypercube d,
      RadialHardQuantitativeCertificate o d
        (a * lowerBandwidth a d T β ^ (β - 1))
        (lowerBandwidth a d T β)
        (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
          (lt_trans (by norm_num) hβ)) s)
    (s : Hypercube d) :
    (lowerRateHardObjective hd hT β a hβ ha ha4 cert s).minimizer =
      signCenter
        ((a * lowerBandwidth a d T β ^ (β - 1)) /
          (2 * Real.sqrt d)) s := by
  exact rateRadialHardObjective_minimizer hd β a
    (lowerBandwidth a d T β) hβ ha ha4
    (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
      (lt_trans (by norm_num) hβ))
    (lowerBandwidth_le_one a d T β) s (cert s)

/-- Lower rate for an actual algorithm output and the canonical hard family,
with the analytic interface reduced to its two perturbation derivative
bounds. -/
theorem hard_family_adaptive_gaussian_lower_rate_of_quantitative_certificate
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (output : α → Point d) (houtput : Measurable output)
    (houtput_mem : ∀ z, ‖output z‖ ≤ 1)
    (cert : ∀ s : Hypercube d,
      RadialHardQuantitativeCertificate o d
        (a * lowerBandwidth a d T β ^ (β - 1))
        (lowerBandwidth a d T β)
        (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
          (lt_trans (by norm_num) hβ)) s) :
    (3 * a ^ 2 / 64) *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β) ≤
      (∑ s : Hypercube d,
        (∫ x,
          (lowerRateHardObjective hd hT β a hβ ha ha4 cert s).f x -
            (lowerRateHardObjective hd hT β a hβ ha ha4 cert s).f
              (lowerRateHardObjective hd hT β a hβ ha ha4 cert s).minimizer
          ∂hardAdaptiveOutputLaw μ₀
            (a * lowerBandwidth a d T β ^ (β - 1))
            (lowerBandwidth a d T β)
            (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
              (lt_trans (by norm_num) hβ))
            query hquery update hupdate T output s)) /
          (2 : ℝ) ^ d := by
  apply hard_family_adaptive_gaussian_lower_rate_of_algorithm_output
    hd hT β a hβ ha ha4 μ₀ query hquery update hupdate
    output houtput houtput_mem
    (lowerRateHardObjective hd hT β a hβ ha ha4 cert)
  · exact lowerRateHardObjective_minimizer hd hT β a hβ ha ha4 cert

end

end NoisyZO
