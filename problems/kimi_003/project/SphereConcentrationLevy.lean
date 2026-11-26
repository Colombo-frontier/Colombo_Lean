import SphereConcentrationGaussian
import SphereConcentrationRadial
import SphereConcentrationMedian
import GaussianRadius

/-!
Median concentration on the Euclidean unit sphere, derived from an actual
Gaussian annulus, real Lipschitz extension, the proved Gaussian concentration
theorem, and proved uniqueness of the invariant sphere law. Constants are
explicit universal values; no spherical concentration theorem is a premise.
-/

open Set MeasureTheory ProbabilityTheory GaussianMeasure Metric
open Task006.HaarRebalancing
open scoped ENNReal NNReal ProbabilityTheory

namespace Task006.SphereConcentration
noncomputable section
variable {d : ℕ}

/-- A distribution equality gives equality of all real probabilities of
measurable scalar events, allowing different underlying sample spaces. -/
theorem real_event_eq_of_map_eq {Ω Ω' B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure Ω'} {f : Ω → B} {g : Ω' → B}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν)
    (hlaw : Measure.map f μ = Measure.map g ν)
    {s : Set B} (hs : MeasurableSet s) :
    μ.real (f ⁻¹' s) = ν.real (g ⁻¹' s) := by
  have h := congrArg (fun ρ : Measure B => (ρ s).toReal) hlaw
  simpa only [Measure.map_apply_of_aemeasurable hf hs,
    Measure.map_apply_of_aemeasurable hg hs, Measure.real] using h

/-- Dimension-dependent spherical concentration, for a positive Lipschitz
constant. The exponent uses d and is slightly stronger than the source d-1 form. -/
theorem sphere_lipschitz_median_concentration_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ)
    (hd : 0 < d) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    {H : ℝ≥0} (hH : 0 < H) (hlip : LipschitzOnWith H a (sphere (0 : _) 1))
    (hlo : (1 / 2 : ℝ) ≤ μ.real {ω | a (v ω) ≤ 0})
    (hhi : (1 / 2 : ℝ) ≤ μ.real {ω | 0 ≤ a (v ω)})
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |a (v ω)|} ≤
      Real.exp 128 * Real.exp (-(d : ℝ) * t ^ 2 / (128 * (H : ℝ) ^ 2)) := by
  let r : ℝ := Real.sqrt (d : ℝ) / 2
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdreal
  have hr : 0 < r := by dsimp [r]; positivity
  let A := outerAnnulus d r
  have hA : MeasurableSet A := measurableSet_outerAnnulus d r
  have hmass : (1 / 16 : ℝ) ≤ (stdGaussianE d).real A := by
    have h := Task006.GaussianRadius.gaussian_annulus_probability d hd
    change (1 / 12 : ℝ) ≤ (stdGaussianE d).real A at h
    linarith
  have hmassne : stdGaussianE d A ≠ 0 := by
    intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hmass
    norm_num at hmass
  have hstdne : stdGaussian (EuclideanSpace ℝ (Fin d)) (outerAnnulus d r) ≠ 0 := by
    rwa [← sltGaussian_eq_stdGaussian d]
  let ρ := (stdGaussianE d)[|A]
  letI : IsProbabilityMeasure ρ := cond_isProbabilityMeasure hmassne
  have hrho : gaussianAnnulusLaw d r = ρ := by
    unfold gaussianAnnulusLaw
    rw [← sltGaussian_eq_stdGaussian d]
  have hdir : Measure.map NormedSpace.normalize ρ = Measure.map v μ := by
    rw [← hrho]
    exact gaussianAnnulusDirection_map_eq hv hr hstdne
  let K : ℝ≥0 := Real.toNNReal (2 / r) * H
  have hHreal : 0 < (H : ℝ) := hH
  have hK : 0 < K := mul_pos (Real.toNNReal_pos.mpr (by positivity)) hH
  obtain ⟨g, hg, heq⟩ := exists_radial_lipschitz_extension hr hlip
  change LipschitzWith K g at hg
  have heqae : g =ᵐ[ρ] a ∘ NormedSpace.normalize := by
    apply ae_cond_of_forall_mem hA
    intro x hx
    exact (heq hx).symm
  have hlaw : Measure.map g ρ = Measure.map (fun ω => a (v ω)) μ := by
    calc
      Measure.map g ρ = Measure.map (a ∘ NormedSpace.normalize) ρ := Measure.map_congr heqae
      _ = Measure.map a (Measure.map NormedSpace.normalize ρ) := by
        rw [Measure.map_map ha measurable_normalize]
      _ = Measure.map a (Measure.map v μ) := by rw [hdir]
      _ = Measure.map (fun ω => a (v ω)) μ :=
        AEMeasurable.map_map_of_aemeasurable ha.aemeasurable hv.measurable
  have hevents (P : ℝ → Prop) (hP : MeasurableSet {z | P z}) :
      ρ.real {x | P (g x)} = μ.real {ω | P (a (v ω))} :=
    real_event_eq_of_map_eq hg.continuous.aemeasurable
      (ha.aemeasurable.comp_aemeasurable hv.measurable) hlaw hP
  have hloG : (1 / 2 : ℝ) ≤ ρ.real {x | g x ≤ 0} := by
    rw [hevents (fun z => z ≤ 0) measurableSet_Iic]
    exact hlo
  have hhiG : (1 / 2 : ℝ) ≤ ρ.real {x | 0 ≤ g x} := by
    rw [hevents (fun z => 0 ≤ z) measurableSet_Ici]
    exact hhi
  have htail := gaussian_conditioned_median_concentration hd hK hg hA hmass hloG hhiG ht
  change ρ.real {x | t ≤ |g x|} ≤ _ at htail
  rw [hevents (fun z => t ≤ |z|) (measurableSet_le measurable_const measurable_id.abs)] at htail
  have hKreal : (K : ℝ) = 4 * (H : ℝ) / Real.sqrt (d : ℝ) := by
    change (Real.toNNReal (2 / r) : ℝ) * (H : ℝ) = _
    rw [Real.coe_toNNReal _ (by positivity)]
    dsimp [r]
    ring
  have hKsquare : (K : ℝ) ^ 2 = 16 * (H : ℝ) ^ 2 / (d : ℝ) := by
    rw [hKreal, div_pow, mul_pow, Real.sq_sqrt hdreal.le]
    norm_num
  have halg : -t ^ 2 / (8 * (K : ℝ) ^ 2) =
      -(d : ℝ) * t ^ 2 / (128 * (H : ℝ) ^ 2) := by
    rw [hKsquare]
    field_simp [hdreal.ne', hHreal.ne'] <;> ring
  rwa [halg] at htail

/-- The exact median-centered source form: absolute constants, d-1 scaling,
and all nonnegative Lipschitz constants and thresholds are covered. -/
theorem sphere_median_concentration {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ)
    (hd : 0 < d) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    {H : ℝ≥0} (hlip : LipschitzOnWith H a (sphere (0 : _) 1))
    (hlo : (1 / 2 : ℝ) ≤ μ.real {ω | a (v ω) ≤ 0})
    (hhi : (1 / 2 : ℝ) ≤ μ.real {ω | 0 ≤ a (v ω)})
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |a (v ω)|} ≤
      Real.exp 128 * Real.exp (-((d : ℝ) - 1) * t ^ 2 / (128 * (H : ℝ) ^ 2)) := by
  have hCe : 1 ≤ Real.exp (128 : ℝ) := Real.one_le_exp (by norm_num)
  by_cases hH : H = 0
  · simp only [hH, NNReal.coe_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, div_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hCe
  by_cases htzero : t = 0
  · simp only [htzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_div, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hCe
  have hHpos : 0 < H := pos_iff_ne_zero.mpr hH
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
  have htail := sphere_lipschitz_median_concentration_pos hv hd ha hHpos hlip hlo hhi htpos
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg t]) (by positivity)

end
end Task006.SphereConcentration
