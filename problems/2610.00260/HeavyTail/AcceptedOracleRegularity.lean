import HeavyTail.AcceptedOracleModel

/-! Measurability and integrability of the actual accepted means/noise. These
properties are derived from the raw kernel and the bounded acceptance event. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace Classical
namespace HeavyTail.PrivateInstance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

theorem acceptedMean_formula (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (z : E) :
    I.acceptedMean hR hn τ z =
      ((I.stageRawKernel hR hn z) (Prod.mk z ⁻¹' B.stageAcceptance hR hn τ)).toReal⁻¹ •
        (∫ g, (B.stageAcceptance hR hn τ).indicator
          (fun zg => B.correctedReply hR hn zg.1 zg.2) (z, g) ∂I.stageRawKernel hR hn z) := by
  unfold acceptedMean acceptedRawLaw ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv]
  congr 1
  rw [← integral_indicator ((B.stageAcceptance_measurable hR hn τ).preimage measurable_prodMk_left)]
  rfl

theorem acceptedMean_measurable (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) : Measurable (I.acceptedMean hR hn τ) := by
  have hm := (Kernel.measurable_kernel_prodMk_left (κ := I.stageRawKernel hR hn)
    (B.stageAcceptance_measurable hR hn τ)).ennreal_toReal.inv
  have hi := ((B.correctedReply_measurable hR hn).stronglyMeasurable.indicator
    (B.stageAcceptance_measurable hR hn τ)).integral_kernel_prod_right' (κ := I.stageRawKernel hR hn)
  have he := hm.smul hi.measurable
  change Measurable (fun z => I.acceptedMean hR hn τ z)
  simp_rw [I.acceptedMean_formula]
  exact he

theorem acceptedRawLaw_probability (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    IsProbabilityMeasure (I.acceptedRawLaw hR hn τ z) :=
  ProbabilityTheory.cond_isProbabilityMeasure (I.stageAcceptance_pos hR hn hτ z hz)

theorem acceptedReply_norm_bound (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (z : E) :
    ∀ᵐ g ∂I.acceptedRawLaw hR hn τ z, ‖B.correctedReply hR hn z g‖ ≤ τ :=
  ProbabilityTheory.ae_cond_mem ((B.stageAcceptance_measurable hR hn τ).preimage measurable_prodMk_left)

theorem acceptedReply_memLp (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) (p : ℝ≥0∞) :
    MemLp (B.correctedReply hR hn z) p (I.acceptedRawLaw hR hn τ z) := by
  letI := I.acceptedRawLaw_probability hR hn hτ z hz
  exact MemLp.of_bound (B.correctedReply_measurable_right hR hn z).aestronglyMeasurable τ
    (I.acceptedReply_norm_bound hR hn τ z)

theorem acceptedReply_integrable (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    Integrable (B.correctedReply hR hn z) (I.acceptedRawLaw hR hn τ z) := by
  exact memLp_one_iff_integrable.mp (I.acceptedReply_memLp hR hn hτ z hz 1)

theorem acceptedNoise_memLp (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) (p : ℝ≥0∞) :
    MemLp (fun g => B.correctedReply hR hn z g - I.acceptedMean hR hn τ z) p
      (I.acceptedRawLaw hR hn τ z) := by
  letI := I.acceptedRawLaw_probability hR hn hτ z hz
  exact (I.acceptedReply_memLp hR hn hτ z hz p).sub (memLp_const _)

theorem acceptedNoise_centered (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    (∫ g, B.correctedReply hR hn z g - I.acceptedMean hR hn τ z
      ∂I.acceptedRawLaw hR hn τ z) = 0 := by
  letI := I.acceptedRawLaw_probability hR hn hτ z hz
  rw [integral_sub (I.acceptedReply_integrable hR hn hτ z hz) (integrable_const _), integral_const]
  simp [acceptedMean]

theorem acceptedNoise_square_integrable (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    Integrable (fun g => ‖B.correctedReply hR hn z g - I.acceptedMean hR hn τ z‖ ^ 2)
      (I.acceptedRawLaw hR hn τ z) := by
  letI := I.acceptedRawLaw_probability hR hn hτ z hz
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (I.acceptedNoise_memLp hR hn hτ z hz 2).integrable_norm_rpow'

end HeavyTail.PrivateInstance
