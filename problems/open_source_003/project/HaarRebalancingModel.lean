import HaarRebalancingThreshold
import SphereConcentrationSecants
import UpperProgramRegularization
import UpperSmoothingSecant

/-!
The actual sample-instance U3 interface. A jointly measurable globally Lipschitz
analysis representative is derived from the model's local a.e. assumptions and
agrees simultaneously at every legal query. The algorithm and its samples are
not altered. All moment formulas below are the original raw secants' moments.
-/
set_option maxHeartbeats 1000000

open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.HaarRebalancing Task006.SphereConcentration
open scoped NNReal ENNReal

namespace Task006.Full.SampleInstance
noncomputable section
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

/-- A global Lipschitz analysis extension, derived rather than added to the
model. The original local oracle is recovered simultaneously at all legal x. -/
theorem exists_joint_lipschitz_regularization (hR : 0 ≤ R) :
    ∃ F : Ω → Space d → ℝ,
      Measurable (fun p : Ω × Space d => F p.1 p.2) ∧
      (∀ ω, LipschitzWith (Real.toNNReal (I.modulus ω)) (F ω)) ∧
      ∀ᵐ ω ∂μ, ∀ x ∈ queryDomain d R, F ω x = I.sample x ω := by
  classical
  obtain ⟨F, hFm, hFae⟩ := I.exists_joint_regularization hR
  obtain ⟨A, hAae, hAm, hA⟩ :=
    (I.nonneg_modulus.and (I.lipschitz_sample.and hFae)).exists_measurable_mem
  have hr : 0 ≤ 2 * R := by positivity
  let projectQuery : Space d → Space d := ballProj (2 * R) hr
  have hprojectQuerym : Measurable projectQuery := (ballProj_lipschitz hr).continuous.measurable
  have hprojectQuerymem (x : Space d) : projectQuery x ∈ queryDomain d R := ballProj_mem _ hr x
  let H : Ω → Space d → ℝ := fun ω x => if ω ∈ A then F (projectQuery x) ω else 0
  refine ⟨H, ?_, ?_, ?_⟩
  · exact Measurable.ite (hAm.preimage measurable_fst)
      (hFm.comp ((hprojectQuerym.comp measurable_snd).prodMk measurable_fst)) measurable_const
  · intro ω
    apply LipschitzWith.of_dist_le_mul
    intro x y
    by_cases hω : ω ∈ A
    · have hh := hA ω hω
      have hlip := hh.2.1 (projectQuery x) (hprojectQuerymem x) (projectQuery y) (hprojectQuerymem y)
      have hp := (ballProj_lipschitz hr).norm_sub_le x y
      simp only [NNReal.coe_one, one_mul] at hp
      change ‖H ω x - H ω y‖ ≤ _ * ‖x - y‖
      simp only [H, if_pos hω, hh.2.2 _ (hprojectQuerymem x), hh.2.2 _ (hprojectQuerymem y),
        Real.norm_eq_abs, Real.coe_toNNReal _ hh.1]
      exact hlip.trans (mul_le_mul_of_nonneg_left hp hh.1)
    · simp only [H, if_neg hω, dist_self]
      positivity
  · filter_upwards [hAae] with ω hω
    intro x hx
    have hxn : ‖x‖ ≤ 2 * R := by simpa only [queryDomain, mem_closedBall, dist_zero_right] using hx
    have hp : projectQuery x = x := ballProj_eq_self hr hxn
    simpa only [H, if_pos hω, hp] using (hA ω hω).2.2 x hx

/-- A fixed canonical representative, used only in measurable analysis
formulas. Choice does not enter the algorithm. -/
@[irreducible] def jointLipschitzSample (hR : 0 ≤ R) : Ω → Space d → ℝ :=
  (I.exists_joint_lipschitz_regularization hR).choose

theorem jointLipschitzSample_spec (hR : 0 ≤ R) :
    Measurable (fun p : Ω × Space d => I.jointLipschitzSample hR p.1 p.2) ∧
      (∀ ω, LipschitzWith (Real.toNNReal (I.modulus ω)) (I.jointLipschitzSample hR ω)) ∧
      ∀ᵐ ω ∂μ, ∀ x ∈ queryDomain d R,
        I.jointLipschitzSample hR ω x = I.sample x ω :=
by
  unfold jointLipschitzSample
  exact (I.exists_joint_lipschitz_regularization hR).choose_spec

/-- Product law of one original hidden sample and one independent ball draw. -/
def secantSampleLaw (_I : SampleInstance d L R Ω μ) : Measure (Ω × Space d) := μ.prod (unitBallLaw d)
instance secantSampleLaw_probability : IsProbabilityMeasure I.secantSampleLaw :=
  inferInstanceAs (IsProbabilityMeasure (μ.prod (unitBallLaw d)))

/-- Jointly measurable analysis secant, with the same centered formula. -/
def regularizedSecant (hR : 0 ≤ R) (ρ δ : ℝ) (x : Space d)
    (z : Ω × Space d) (q : Space d) : ℝ :=
  sampledCentralSecant (fun z : Ω × Space d => I.jointLipschitzSample hR z.1)
    (fun z => x + ρ • z.2) δ z q

/-- The actual directional moment, retaining raw oracle values. -/
def oracleDirectionalMoment (ρ δ : ℝ) (x q : Space d) : ℝ :=
  ∫ z : Ω × Space d, |I.oracleSecant ρ δ x q z.2 z.1| ^ (3 / 2 : ℝ) ∂I.secantSampleLaw

/-- Joint measurability also in the algorithm's center x. -/
theorem regularizedSecant_joint_measurable (hR : 0 ≤ R) (ρ δ : ℝ) :
    Measurable (fun p : (Space d × (Ω × Space d)) × Space d =>
      I.regularizedSecant hR ρ δ p.1.1 p.1.2 p.2) := by
  let Z := (Space d × (Ω × Space d)) × Space d
  have hω : Measurable (fun p : Z => p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hx : Measurable (fun p : Z => p.1.1) := measurable_fst.comp measurable_fst
  have hu : Measurable (fun p : Z => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hq : Measurable (fun p : Z => p.2) := measurable_snd
  have hρu : Measurable (fun p : Z => ρ • p.1.2.2) :=
    (measurable_const : Measurable (fun _ : Z => ρ)).smul hu
  have hδq : Measurable (fun p : Z => δ • p.2) :=
    (measurable_const : Measurable (fun _ : Z => δ)).smul hq
  have hplus : Measurable (fun p : Z => p.1.1 + ρ • p.1.2.2 + δ • p.2) :=
    (hx.add hρu).add hδq
  have hminus : Measurable (fun p : Z => p.1.1 + ρ • p.1.2.2 - δ • p.2) :=
    (hx.add hρu).sub hδq
  have hp := (I.jointLipschitzSample_spec hR).1.comp (hω.prodMk hplus)
  have hm := (I.jointLipschitzSample_spec hR).1.comp (hω.prodMk hminus)
  exact (hp.sub hm).div_const (2 * δ)

theorem regularizedSecant_measurable (hR : 0 ≤ R) (ρ δ : ℝ) (x : Space d) :
    Measurable (fun p : (Ω × Space d) × Space d => I.regularizedSecant hR ρ δ x p.1 p.2) :=
  (I.regularizedSecant_joint_measurable hR ρ δ).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

/-- The regularized secants satisfy every pathwise U3 input, on every sample.
These facts are derived from the original a.e. local sample instance. -/
theorem regularizedSecant_pathwise (hR : 0 ≤ R) {ρ δ : ℝ} (hδ : 0 < δ) (x : Space d) :
    (∀ z : Ω × Space d, LipschitzOnWith (Real.toNNReal (I.modulus z.1))
      (I.regularizedSecant hR ρ δ x z) (sphere (0 : _) 1)) ∧
    (∀ z q, I.regularizedSecant hR ρ δ x z (-q) = -I.regularizedSecant hR ρ δ x z q) ∧
    (∀ z q, ‖q‖ = 1 → |I.regularizedSecant hR ρ δ x z q| ≤ Real.toNNReal (I.modulus z.1)) := by
  let F : (Ω × Space d) → Space d → ℝ := fun z => I.jointLipschitzSample hR z.1
  let c : (Ω × Space d) → Space d := fun z => x + ρ • z.2
  let G : (Ω × Space d) → ℝ≥0 := fun z => Real.toNNReal (I.modulus z.1)
  have hF : ∀ z, ∀ a ∈ (univ : Set (Space d)), ∀ b ∈ (univ : Set (Space d)),
      |F z a - F z b| ≤ (G z : ℝ) * ‖a - b‖ := by
    intro z a ha b hb
    simpa only [F, G, Real.norm_eq_abs] using
      ((I.jointLipschitzSample_spec hR).2.1 z.1).norm_sub_le a b
  have hlegal : ∀ z q, ‖q‖ = 1 → c z + δ • q ∈ (univ : Set (Space d)) ∧
      c z - δ • q ∈ (univ : Set (Space d)) := by simp
  exact ⟨sampledCentralSecant_lipschitz G hδ hF hlegal,
    sampledCentralSecant_odd F c δ,
    sampledCentralSecant_abs_le G hδ hF hlegal⟩

/-- The nonnegative modulus representative has exactly the model's moment. -/
theorem nonnegativeModulus_moment :
    Integrable (fun z : Ω × Space d =>
      ((Real.toNNReal (I.modulus z.1) : ℝ≥0) : ℝ) ^ (3 / 2 : ℝ)) I.secantSampleLaw ∧
    (∫ z : Ω × Space d, ((Real.toNNReal (I.modulus z.1) : ℝ≥0) : ℝ) ^ (3 / 2 : ℝ)
      ∂I.secantSampleLaw) ≤ L ^ (3 / 2 : ℝ) := by
  have heq : (fun ω => ((Real.toNNReal (I.modulus ω) : ℝ≥0) : ℝ) ^ (3 / 2 : ℝ)) =ᵐ[μ]
      (fun ω => I.modulus ω ^ (3 / 2 : ℝ)) := by
    filter_upwards [I.nonneg_modulus] with ω hω
    rw [Real.coe_toNNReal _ hω]
  have hm := I.integrable_moment.congr heq.symm
  have hp := hm.comp_fst (unitBallLaw d)
  refine ⟨hp, ?_⟩
  change (∫ z : Ω × Space d, ((Real.toNNReal (I.modulus z.1) : ℝ≥0) : ℝ) ^ (3 / 2 : ℝ)
    ∂μ.prod (unitBallLaw d)) ≤ _
  rw [integral_prod _ hp]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_congr_ae heq]
  exact I.moment_bound

/-- Agreement is simultaneous in the direction q for each good sample pair.
Only the original unit-ball draw is used; no projection changes that draw. -/
theorem regularizedSecant_eq_raw_ae (hR : 0 ≤ R) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) {x : Space d}
    (hx : ‖x‖ + δ ≤ R) :
    ∀ᵐ z : Ω × Space d ∂I.secantSampleLaw, ∀ q, ‖q‖ = 1 →
      I.regularizedSecant hR ρ δ x z q = I.oracleSecant ρ δ x q z.2 z.1 := by
  have hω := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := unitBallLaw d)).ae
    ((I.jointLipschitzSample_spec hR).2.2)
  have hu := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := unitBallLaw d)).ae
    (unitBallLaw_norm_le d)
  filter_upwards [hω, hu] with z hz hzu
  intro q hq
  have hxp : ‖x + δ • q‖ ≤ R := by
    calc
      ‖x + δ • q‖ ≤ ‖x‖ + ‖δ • q‖ := norm_add_le _ _
      _ ≤ R := by simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hq, mul_one] using hx
  have hxm : ‖x - δ • q‖ ≤ R := by
    calc
      ‖x - δ • q‖ ≤ ‖x‖ + ‖δ • q‖ := norm_sub_le _ _
      _ ≤ R := by simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hq, mul_one] using hx
  have hp := hz _ (ballTranslate_mem_queryDomain hρ hρR hxp hzu)
  have hm := hz _ (ballTranslate_mem_queryDomain hρ hρR hxm hzu)
  have hadd : x + ρ • z.2 + δ • q = x + δ • q + ρ • z.2 := by abel
  have hsub : x + ρ • z.2 - δ • q = x - δ • q + ρ • z.2 := by abel
  simp only [regularizedSecant, sampledCentralSecant, Task006.SphereConcentration.centralSecant,
    oracleSecant, hadd, hsub, hp, hm]

theorem regularizedDirectionalMoment_eq_raw (hR : 0 ≤ R) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) {x q : Space d}
    (hx : ‖x‖ + δ ≤ R) (hq : ‖q‖ = 1) :
    directionalMoment I.secantSampleLaw (I.regularizedSecant hR ρ δ x) q =
      I.oracleDirectionalMoment ρ δ x q := by
  apply integral_congr_ae
  filter_upwards [I.regularizedSecant_eq_raw_ae hR hρ hρR hδ hx] with z hz
  rw [hz q hq]

/-- The raw oracle's r-th power is genuinely integrable under the original
independent sample and smoothing law at every legal unit direction. -/
theorem oracleSecant_threeHalves_integrable_product (hR : 0 ≤ R) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) {x q : Space d}
    (hx : ‖x‖ + δ ≤ R) (hq : ‖q‖ = 1) :
    Integrable (fun z : Ω × Space d =>
      |I.oracleSecant ρ δ x q z.2 z.1| ^ (3 / 2 : ℝ)) I.secantSampleLaw := by
  have hD : Measurable (fun z : Ω × Space d => I.regularizedSecant hR ρ δ x z q) :=
    (I.regularizedSecant_measurable hR ρ δ x).comp (measurable_id.prodMk measurable_const)
  have hpow : Measurable (fun z : Ω × Space d =>
      |I.regularizedSecant hR ρ δ x z q| ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp hD.abs
  have hm := I.nonnegativeModulus_moment
  have hpath := (I.regularizedSecant_pathwise hR (ρ := ρ) hδ x).2.2
  have hint : Integrable (fun z : Ω × Space d =>
      |I.regularizedSecant hR ρ δ x z q| ^ (3 / 2 : ℝ)) I.secantSampleLaw :=
    hm.1.mono' hpow.aestronglyMeasurable (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hpath z q hq) (by norm_num)))
  apply hint.congr
  filter_upwards [I.regularizedSecant_eq_raw_ae hR hρ hρR hδ hx] with z hz
  rw [hz q hq]

/-- Fubini identifies Phi with exactly the iterated fresh-sample/ball-draw
expectation used in the manuscript and actual round analysis. -/
theorem oracleDirectionalMoment_eq_iterated (hR : 0 ≤ R) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) {x q : Space d}
    (hx : ‖x‖ + δ ≤ R) (hq : ‖q‖ = 1) :
    I.oracleDirectionalMoment ρ δ x q =
      ∫ u, (∫ ω, |I.oracleSecant ρ δ x q u ω| ^ (3 / 2 : ℝ) ∂μ) ∂unitBallLaw d := by
  exact integral_prod_symm _
    (I.oracleSecant_threeHalves_integrable_product hR hρ hρR hδ hx hq)

end
end Task006.Full.SampleInstance
