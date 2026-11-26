import Bilevel.GaussianAffinity
import Bilevel.HellingerTesting

/-!
# The actual independent Gaussian sample law

The product density is identified with the product of the Gaussian probability
measures. Thus density testing bounds apply to genuine independent samples,
also in the presence of an independent random seed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Bilevel.GaussianProductLaw

open GaussianAffinity

theorem density_measurable (n : ℕ) (m : ℝ) (v : ℝ≥0) : Measurable (density n m v) := by
  unfold density
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDFReal m v).comp (measurable_pi_apply i))

theorem density_rectangle_integral (n : ℕ) (m : ℝ) (v : ℝ≥0)
    (s : Fin n → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    (∫ x in Set.pi Set.univ s, density n m v x) =
      ∏ i, ∫ z in s i, gaussianPDFReal m v z := by
  classical
  have hid : (Set.pi Set.univ s).indicator (density n m v) =
      fun x => ∏ i, (s i).indicator (gaussianPDFReal m v) (x i) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · have hxpi : x ∈ Set.pi Set.univ s := fun i _ => hx i
      rw [Set.indicator_of_mem hxpi]
      simp only [Set.indicator_of_mem (hx _), density]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      have hxpi : x ∉ Set.pi Set.univ s := by
        intro h
        exact hi (h i (Set.mem_univ i))
      rw [Set.indicator_of_not_mem hxpi]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_not_mem hi _)
  rw [← integral_indicator (MeasurableSet.univ_pi hs), hid,
    integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_indicator (hs i)

/-- The finite iid Gaussian law has exactly the product density. -/
theorem gaussian_pi_eq_withDensity (n : ℕ) (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin n => gaussianReal m v) =
      volume.withDensity (fun x => ENNReal.ofReal (density n m v x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (density_integrable n m v).restrict
      (Filter.Eventually.of_forall (density_nonnegative n m v)),
    density_rectangle_integral n m v s hs]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg (fun z => gaussianPDFReal_nonneg m v z))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral m hv (s i)).symm

/-- Integrals under actual iid samples equal density-weighted integrals. -/
theorem integral_gaussian_pi_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : (Fin n → ℝ) → E) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin n => gaussianReal m v)) =
      ∫ x, density n m v x • f x := by
  rw [gaussian_pi_eq_withDensity n m v hv,
    integral_withDensity_eq_integral_toReal_smul (density_measurable n m v).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (density_nonnegative n m v _)]

section Seed

variable {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]

def seededDensity (n : ℕ) (m : ℝ) (v : ℝ≥0) (sx : Seed × (Fin n → ℝ)) : ℝ :=
  density n m v sx.2

omit [MeasurableSpace Seed] in
theorem seededDensity_nonnegative (n : ℕ) (m : ℝ) (v : ℝ≥0) (sx : Seed × (Fin n → ℝ)) :
    0 ≤ seededDensity n m v sx := density_nonnegative n m v sx.2

theorem seededDensity_measurable (n : ℕ) (m : ℝ) (v : ℝ≥0) :
    Measurable (seededDensity (Seed := Seed) n m v) :=
  (density_measurable n m v).comp measurable_snd

theorem integrable_seed_pullback {E : Type*} [MeasurableSpace E] (κ : Measure E)
    (f : E → ℝ) (hf : Integrable f κ) :
    Integrable (fun sx : Seed × E => f sx.2) (ν.prod κ) := by
  simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := ν)).mul_prod hf

theorem integral_seed_pullback {E : Type*} [MeasurableSpace E] (κ : Measure E) [SFinite κ]
    (f : E → ℝ) (hf : Integrable f κ) :
    (∫ sx : Seed × E, f sx.2 ∂ν.prod κ) = ∫ x, f x ∂κ := by
  rw [integral_prod _ (integrable_seed_pullback ν κ f hf)]
  simp

theorem seededDensity_integrable (n : ℕ) (m : ℝ) (v : ℝ≥0) :
    Integrable (seededDensity n m v) (ν.prod volume) :=
  integrable_seed_pullback ν volume _ (density_integrable n m v)

theorem seededDensity_integral (n : ℕ) (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ sx, seededDensity n m v sx ∂ν.prod volume) = 1 := by
  rw [show seededDensity (Seed := Seed) n m v = fun sx => density n m v sx.2 from rfl,
    integral_seed_pullback ν volume _ (density_integrable n m v), density_integral n m v hv]

omit [IsProbabilityMeasure ν] in
/-- Adding an arbitrary independent random seed leaves the density unchanged
in the seed coordinate. -/
theorem gaussian_seed_eq_withDensity (n : ℕ) (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ν.prod (Measure.pi (fun _ : Fin n => gaussianReal m v)) =
      (ν.prod volume).withDensity (fun sx => ENNReal.ofReal (seededDensity n m v sx)) := by
  rw [gaussian_pi_eq_withDensity n m v hv]
  exact prod_withDensity_right (density_measurable n m v).ennreal_ofReal

omit [IsProbabilityMeasure ν] in
theorem integral_gaussian_seed_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : Seed × (Fin n → ℝ) → E) :
    (∫ sx, f sx ∂ν.prod (Measure.pi (fun _ : Fin n => gaussianReal m v))) =
      ∫ sx, seededDensity n m v sx • f sx ∂ν.prod volume := by
  rw [gaussian_seed_eq_withDensity ν n m v hv,
    integral_withDensity_eq_integral_toReal_smul (seededDensity_measurable n m v).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (seededDensity_nonnegative n m v _)]

/-- Independent private randomization does not alter the Gaussian affinity. -/
theorem seeded_affinity (n : ℕ) (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    HellingerTesting.affinity (seededDensity n δ v) (seededDensity n (-δ) v) (ν.prod volume) =
      Real.exp (-(n : ℝ) * δ ^ 2 / (2 * (v : ℝ))) := by
  rw [HellingerTesting.affinity_eq_integral_sqrt _ _ (seededDensity_nonnegative n δ v)]
  change (∫ sx : Seed × (Fin n → ℝ),
    Real.sqrt (density n δ v sx.2 * density n (-δ) v sx.2) ∂ν.prod volume) = _
  rw [integral_seed_pullback ν volume _ (product_affinity_integrable n δ v hv),
    product_affinity n δ v hv]

end Seed

end Bilevel.GaussianProductLaw
