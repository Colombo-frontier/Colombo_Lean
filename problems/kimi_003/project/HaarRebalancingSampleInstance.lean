import HaarRebalancingModel
import HaarRebalancingMeasurable

/-! Full U3 for the original sample instance, including joint good-basis
measurability, original raw oracle moment equality, and the Haar bad-basis
bound. The measurable representative changes only analysis on a null set. -/

set_option maxHeartbeats 1000000
open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.HaarRebalancing Task006.SphereConcentration
open scoped NNReal ENNReal
namespace Task006.Full.SampleInstance
noncomputable section
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

/-- Everywhere measurable analysis moment; it equals the raw directional
moment for every legal center and unit q, as proved below. -/
def rebalancedDirectionalMoment (hR : 0 ≤ R) (ρ δ : ℝ) (x q : Space d) : ℝ :=
  directionalMoment I.secantSampleLaw (I.regularizedSecant hR ρ δ x) q

theorem rebalancedDirectionalMoment_joint_measurable (hR : 0 ≤ R) (ρ δ : ℝ) :
    Measurable (fun p : Space d × Space d => I.rebalancedDirectionalMoment hR ρ δ p.1 p.2) := by
  have hm : Measurable (fun p : (Ω × Space d) × (Space d × Space d) =>
      I.regularizedSecant hR ρ δ p.2.1 p.1 p.2.2) :=
    (I.regularizedSecant_joint_measurable hR ρ δ).comp
      (((measurable_fst.comp measurable_snd).prodMk measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
  have hp := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp hm.abs
  exact hp.stronglyMeasurable.integral_prod_left'.measurable

/-- The manuscript's explicit U3 moment threshold. -/
def rebalancingThreshold (L : ℝ) (d : ℕ) (s : ℝ) : ℝ :=
  rebalancingC2 * L ^ (3 / 2 : ℝ) * (s / (d : ℝ)) ^ (3 / 4 : ℝ)

/-- One Haar basis is good when each actual directional moment is below M.
The everywhere definition uses the null-equivalent measurable representative. -/
def goodRebalancedBasis (hR : 0 ≤ R) (ρ δ s : ℝ) (x : Space d)
    (Q : OrthogonalGroup d) : Prop :=
  ∀ i : Fin d, I.rebalancedDirectionalMoment hR ρ δ x (column Q i) <
    rebalancingThreshold L d s

theorem measurableSet_goodRebalancedBasis (hR : 0 ≤ R) (ρ δ s : ℝ) :
    MeasurableSet {p : Space d × OrthogonalGroup d |
      I.goodRebalancedBasis hR ρ δ s p.1 p.2} := by
  exact measurableSet_all_column_moment_lt
    (I.rebalancedDirectionalMoment_joint_measurable hR ρ δ)
    (rebalancingThreshold L d s)

/-- The analysis moment is exactly the original oracle moment on every unit
q at every legal center x, with no extra sample regularity assumption. -/
theorem rebalancedDirectionalMoment_eq_oracle (hR : 0 ≤ R) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) {x q : Space d}
    (hx : ‖x‖ + δ ≤ R) (hq : ‖q‖ = 1) :
    I.rebalancedDirectionalMoment hR ρ δ x q = I.oracleDirectionalMoment ρ δ x q :=
  I.regularizedDirectionalMoment_eq_raw hR hρ hρR hδ hx hq

/-- A good basis has the manuscript's actual raw moment bound coordinatewise. -/
theorem goodRebalancedBasis_oracle_moment_le (hR : 0 ≤ R) {ρ δ s : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) {x : Space d}
    (hx : ‖x‖ + δ ≤ R) {Q : OrthogonalGroup d}
    (hQ : I.goodRebalancedBasis hR ρ δ s x Q) (i : Fin d) :
    I.oracleDirectionalMoment ρ δ x (column Q i) ≤ rebalancingThreshold L d s := by
  have hcol : ‖column Q i‖ = 1 := (orthonormal_column Q).norm_eq_one i
  rw [← I.rebalancedDirectionalMoment_eq_oracle hR hρ hρR hδ hx hcol]
  exact (hQ i).le

/-- Full U3: every legal original sample instance, at every center x, has a
bad-basis probability at most d*exp(-s). The estimate itself holds everywhere
for the analysis extension; legal centers identify all moments with the raw
oracle. No independence between Haar columns is assumed. -/
theorem badRebalancedBasis_probability_le (hR : 0 ≤ R) (hd : 0 < d) (hL : 0 < L)
    {ρ δ s : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s) (x : Space d) :
    (orthogonalHaarProbability d).real {Q | ¬I.goodRebalancedBasis hR ρ δ s x Q} ≤
      (d : ℝ) * Real.exp (-s) := by
  have hp := I.regularizedSecant_pathwise hR (ρ := ρ) hδ x
  have hm := I.nonnegativeModulus_moment
  have ht := haar_basis_rebalancing hd (I.regularizedSecant hR ρ δ x)
    (fun z : Ω × Space d => Real.toNNReal (I.modulus z.1))
    (I.regularizedSecant_measurable hR ρ δ x)
    (I.measurable_modulus.real_toNNReal.comp measurable_fst)
    hp.1 hp.2.1 hp.2.2 hm.1 hL hm.2 hs
  simpa only [goodRebalancedBasis, not_forall, not_lt, rebalancedDirectionalMoment,
    rebalancingThreshold] using ht

/-- The exact manuscript U3 statement for the original raw oracle moment and
any uniform-sphere draw, uniformly over every legal center and sample instance. -/
theorem oracleDirectionalMoment_rebalancing (hR : 0 ≤ R) (hd : 0 < d) (hL : 0 < L)
    {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ} [IsProbabilityMeasure ν]
    {v : Θ → Space d} (hv : UniformSphereLaw v ν) (hvmeas : Measurable v)
    {ρ δ s : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) (hs : 1 ≤ s)
    {x : Space d} (hx : ‖x‖ + δ ≤ R) :
    ν.real {ω | rebalancingThreshold L d s ≤ I.oracleDirectionalMoment ρ δ x (v ω)} ≤
      Real.exp (-s) := by
  have hp := I.regularizedSecant_pathwise hR (ρ := ρ) hδ x
  have hm := I.nonnegativeModulus_moment
  have ht := directionalMoment_rebalancing hv hvmeas hd
    (I.regularizedSecant hR ρ δ x)
    (fun z : Ω × Space d => Real.toNNReal (I.modulus z.1))
    (I.regularizedSecant_measurable hR ρ δ x)
    (I.measurable_modulus.real_toNNReal.comp measurable_fst)
    hp.1 hp.2.1 hp.2.2 hm.1 hL hm.2 hs
  have hevent : {ω | rebalancingThreshold L d s ≤ I.oracleDirectionalMoment ρ δ x (v ω)} =ᵐ[ν]
      {ω | rebalancingThreshold L d s ≤ I.rebalancedDirectionalMoment hR ρ δ x (v ω)} := by
    filter_upwards [hv.unit_ae] with ω hω
    change (rebalancingThreshold L d s ≤ I.oracleDirectionalMoment ρ δ x (v ω)) =
      (rebalancingThreshold L d s ≤ I.rebalancedDirectionalMoment hR ρ δ x (v ω))
    rw [I.rebalancedDirectionalMoment_eq_oracle hR hρ hρR hδ hx hω]
  rw [measureReal_congr hevent]
  exact ht

end
end Task006.Full.SampleInstance
