import UpperProgramBlocks
import UpperOptimizationMixture
import UpperSmoothingInstance
import HaarRebalancingSampleInstance

/-! The actual fresh coordinate laws, without any conditional-law premise. -/
set_option maxHeartbeats 1000000
open MeasureTheory Set
open Task006.HaarRebalancing
open scoped BigOperators NNReal
namespace Task006.Full
noncomputable section

abbrev UpperRoundNoise (d : ℕ) (Ω : Type*) := (Fin d → UnitBallPoint d) × (Fin d → Ω)
def upperRoundNoiseLaw {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω) :
    Measure (UpperRoundNoise d Ω) :=
  (Measure.pi (fun _ : Fin d => unitBallProbability d)).prod (Measure.pi (fun _ : Fin d => μ))
instance upperRoundNoiseLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (upperRoundNoiseLaw d μ) :=
  inferInstanceAs (IsProbabilityMeasure ((Measure.pi (fun _ : Fin d => unitBallProbability d)).prod
    (Measure.pi (fun _ : Fin d => μ))))

def upperCoordinateSample {d : ℕ} {Ω : Type*} (i : Fin d) (z : UpperRoundNoise d Ω) : Ω × Space d :=
  (z.2 i, (z.1 i).val)

theorem upperCoordinateSample_measurePreserving {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (i : Fin d) :
    MeasurePreserving (upperCoordinateSample i) (upperRoundNoiseLaw d μ) (μ.prod (unitBallLaw d)) := by
  have hval : MeasurePreserving (Subtype.val : UnitBallPoint d → Space d)
      (unitBallProbability d) (unitBallLaw d) := ⟨measurable_subtype_coe, unitBallProbability_map d⟩
  have hu := hval.comp (measurePreserving_eval (fun _ : Fin d => unitBallProbability d) i)
  have hz := measurePreserving_eval (fun _ : Fin d => μ) i
  exact (Measure.measurePreserving_swap (μ := unitBallLaw d) (ν := μ)).comp (hu.prod hz)

theorem integral_comp_measurePreserving {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : Measure A} {β : Measure B} {f : A → B}
    (hf : MeasurePreserving f α β) {g : B → E} (hg : AEStronglyMeasurable g β) :
    (∫ a, g (f a) ∂α) = ∫ b, g b ∂β := by
  have hg' : AEStronglyMeasurable g (α.map f) := hf.map_eq.symm ▸ hg
  exact (integral_map hf.measurable.aemeasurable hg').symm.trans (by rw [hf.map_eq])

namespace SampleInstance
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

/-- The actual globally measurable analysis sample, with input order of the
implemented block function. -/
def rebalancedSample (hR : 0 ≤ R) (x : Space d) (ω : Ω) : ℝ := I.jointLipschitzSample hR ω x

theorem rebalancedSample_measurable (hR : 0 ≤ R) :
    Measurable (Function.uncurry (I.rebalancedSample hR)) :=
  (I.jointLipschitzSample_spec hR).1.comp measurable_swap

/-- The exact unclipped scalar in one coordinate of the implemented block. -/
def upperCoordinateSecant (hR : 0 ≤ R) (ρ δ : ℝ) (x : Space d)
    (Q : OrthogonalGroup d) (i : Fin d) (z : UpperRoundNoise d Ω) : ℝ :=
  I.regularizedSecant hR ρ δ x (upperCoordinateSample i z) (column Q i)

theorem upperCoordinateSecant_measurable (hR : 0 ≤ R) (ρ δ : ℝ) (x : Space d)
    (Q : OrthogonalGroup d) (i : Fin d) : Measurable (I.upperCoordinateSecant hR ρ δ x Q i) :=
  ((I.regularizedSecant_measurable hR ρ δ x).comp
    (measurable_id.prodMk measurable_const)).comp (upperCoordinateSample_measurePreserving μ i).measurable

theorem regularizedSecant_integrable (hR : 0 ≤ R) {ρ δ : ℝ} (hδ : 0 < δ)
    (x q : Space d) (hq : ‖q‖ = 1) :
    Integrable (fun z => I.regularizedSecant hR ρ δ x z q) I.secantSampleLaw := by
  have heq : I.modulus =ᵐ[μ] fun ω => (Real.toNNReal (I.modulus ω) : ℝ) := by
    filter_upwards [I.nonneg_modulus] with ω hω
    rw [Real.coe_toNNReal _ hω]
  have hm := (I.integrable_modulus.congr heq).comp_fst (unitBallLaw d)
  apply hm.mono' (((I.regularizedSecant_measurable hR ρ δ x).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs, Function.comp_def, id_eq] using
      (I.regularizedSecant_pathwise hR (ρ := ρ) hδ x).2.2 z q hq)

theorem regularizedSecant_power_integrable (hR : 0 ≤ R) {ρ δ : ℝ} (hδ : 0 < δ)
    (x q : Space d) (hq : ‖q‖ = 1) :
    Integrable (fun z => |I.regularizedSecant hR ρ δ x z q| ^ (3 / 2 : ℝ)) I.secantSampleLaw := by
  have hm := I.nonnegativeModulus_moment
  have hD : Measurable (fun z : Ω × Space d => I.regularizedSecant hR ρ δ x z q) :=
    (I.regularizedSecant_measurable hR ρ δ x).comp (measurable_id.prodMk measurable_const)
  have hmeas : Measurable (fun z : Ω × Space d => |I.regularizedSecant hR ρ δ x z q| ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp hD.abs
  apply hm.1.mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _)
      ((I.regularizedSecant_pathwise hR (ρ := ρ) hδ x).2.2 z q hq) (by norm_num))

theorem upperCoordinateSecant_integrable (hR : 0 ≤ R) {ρ δ : ℝ} (hδ : 0 < δ)
    (x : Space d) (Q : OrthogonalGroup d) (i : Fin d) :
    Integrable (I.upperCoordinateSecant hR ρ δ x Q i) (upperRoundNoiseLaw d μ) ∧
      Integrable (fun z => |I.upperCoordinateSecant hR ρ δ x Q i z| ^ (3 / 2 : ℝ))
        (upperRoundNoiseLaw d μ) := by
  have hq := (orthonormal_column Q).norm_eq_one i
  have hmp := upperCoordinateSample_measurePreserving μ i
  exact ⟨hmp.integrable_comp_of_integrable (I.regularizedSecant_integrable hR hδ x _ hq),
    hmp.integrable_comp_of_integrable (I.regularizedSecant_power_integrable hR hδ x _ hq)⟩

theorem upperCoordinateSecant_moment_eq (hR : 0 ≤ R) {ρ δ : ℝ} (hδ : 0 < δ)
    (x : Space d) (Q : OrthogonalGroup d) (i : Fin d) :
    (∫ z, |I.upperCoordinateSecant hR ρ δ x Q i z| ^ (3 / 2 : ℝ) ∂upperRoundNoiseLaw d μ) =
      I.rebalancedDirectionalMoment hR ρ δ x (column Q i) :=
  integral_comp_measurePreserving (upperCoordinateSample_measurePreserving μ i)
    (I.regularizedSecant_power_integrable hR hδ x _ ((orthonormal_column Q).norm_eq_one i)).aestronglyMeasurable

/-- Exact fresh-coordinate mean: the original smoothed population secant. -/
theorem upperCoordinateSecant_mean_eq (hR : 0 ≤ R) {ρ δ : ℝ}
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ)
    {x : Space d} (hx : ‖x‖ + δ ≤ R) (Q : OrthogonalGroup d) (i : Fin d) :
    (∫ z, I.upperCoordinateSecant hR ρ δ x Q i z ∂upperRoundNoiseLaw d μ) =
      centralSecant (ballSmooth I.objective ρ) x (column Q i) δ := by
  have hq := (orthonormal_column Q).norm_eq_one i
  have heq := I.regularizedSecant_eq_raw_ae hR hρ hρR hδ hx
  have hreg := I.regularizedSecant_integrable hR (ρ := ρ) hδ x (column Q i) hq
  have hraw : Integrable (fun z : Ω × Space d => I.oracleSecant ρ δ x (column Q i) z.2 z.1)
      I.secantSampleLaw := hreg.congr (by
        filter_upwards [heq] with z hz
        exact hz _ hq)
  have hxp : ‖x + δ • column Q i‖ ≤ R := by
    have hh := norm_add_le x (δ • column Q i)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hq, mul_one] at hh
    exact hh.trans hx
  have hxm : ‖x - δ • column Q i‖ ≤ R := by
    have hh := norm_sub_le x (δ • column Q i)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hq, mul_one] at hh
    exact hh.trans hx
  calc
    _ = ∫ z, I.regularizedSecant hR ρ δ x z (column Q i) ∂I.secantSampleLaw :=
      integral_comp_measurePreserving (upperCoordinateSample_measurePreserving μ i) hreg.aestronglyMeasurable
    _ = ∫ z : Ω × Space d, I.oracleSecant ρ δ x (column Q i) z.2 z.1 ∂I.secantSampleLaw := by
      apply integral_congr_ae
      filter_upwards [heq] with z hz
      exact hz _ hq
    _ = ∫ u, (∫ ω, I.oracleSecant ρ δ x (column Q i) u ω ∂μ) ∂unitBallLaw d :=
      integral_prod_symm _ hraw
    _ = _ := I.oracleSecant_iterated_mean hL hρ hρR hxp hxm

/-- Exact scalar identity to the implemented block formula. -/
theorem upperCoordinateSecant_eq_formula (hR : 0 ≤ R) (ρ δ : ℝ) (x : Space d)
    (Q : OrthogonalGroup d) (i : Fin d) (z : UpperRoundNoise d Ω) :
    I.upperCoordinateSecant hR ρ δ x Q i z =
      (I.rebalancedSample hR (x + δ • column Q i + ρ • (z.1 i).val) (z.2 i) -
        I.rebalancedSample hR (x - δ • column Q i + ρ • (z.1 i).val) (z.2 i)) / (2 * δ) := by
  have hp : x + ρ • (z.1 i).val + δ • column Q i = x + δ • column Q i + ρ • (z.1 i).val := by abel
  have hm : x + ρ • (z.1 i).val - δ • column Q i = x - δ • column Q i + ρ • (z.1 i).val := by abel
  simp only [upperCoordinateSecant, upperCoordinateSample, regularizedSecant,
    Task006.SphereConcentration.sampledCentralSecant, Task006.SphereConcentration.centralSecant,
    rebalancedSample, hp, hm]

end SampleInstance
end
end Task006.Full
