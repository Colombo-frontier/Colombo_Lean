import Matvec.SourceIterationPolicy

/-!
# Extending a unit-right-hand-side solver to every right-hand side

Normalize the public input and rescale the returned vector. At input zero
the returned vector is zero for every transcript. The query horizon is
unchanged and the unit-input probability bound becomes a relative residual
bound for every right-hand side.
-/

namespace Matvec.SourceIterationPolicy
open MeasureTheory MeasurableSimulation
noncomputable section

variable {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Seed] {K : ℕ}

def homogeneousSource (solve : E → Seed → E) (r : E) (seed : Seed) : E :=
  ‖r‖ • solve (‖r‖⁻¹ • r) seed

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Seed] in
theorem homogeneousSource_zero (solve : E → Seed → E) (seed : Seed) :
    homogeneousSource solve 0 seed = 0 := by simp [homogeneousSource]

theorem measurable_homogeneousSource (solve : E → Seed → E)
    (hsolve : Measurable (fun p : E × Seed => solve p.1 p.2)) :
    Measurable (fun p : E × Seed => homogeneousSource solve p.1 p.2) := by
  unfold homogeneousSource
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Seed] in
theorem homogeneousSource_residual (H : E →L[ℝ] E) (solve : E → Seed → E)
    (r : E) (hr : r ≠ 0) (seed : Seed)
    (hgood : ‖H (solve (‖r‖⁻¹ • r) seed) - ‖r‖⁻¹ • r‖ ≤ 1 / 2) :
    ‖H (homogeneousSource solve r seed) - r‖ ≤ ‖r‖ / 2 := by
  have hnorm : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hu : ‖r‖ • (‖r‖⁻¹ • r) = r := by
    rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have heq : H (homogeneousSource solve r seed) - r =
      ‖r‖ • (H (solve (‖r‖⁻¹ • r) seed) - ‖r‖⁻¹ • r) := by
    rw [smul_sub, hu]
    simp only [homogeneousSource, map_smul]
  rw [heq, norm_smul, Real.norm_of_nonneg (norm_nonneg r)]
  nlinarith [mul_le_mul_of_nonneg_left hgood (norm_nonneg r)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem homogeneousSource_success (μ : Measure Seed) [IsProbabilityMeasure μ]
    (H : E →L[ℝ] E) (solve : E → Seed → E) (p : ℝ) (hp : p ≤ 1)
    (hunit : ∀ r, ‖r‖ = 1 →
      p ≤ μ.real {seed | ‖H (solve r seed) - r‖ ≤ 1 / 2}) (r : E) :
    p ≤ μ.real {seed | ‖H (homogeneousSource solve r seed) - r‖ ≤ ‖r‖ / 2} := by
  by_cases hr : r = 0
  · subst r
    simpa only [homogeneousSource_zero, map_zero, sub_self, norm_zero, zero_div,
      le_refl, Set.setOf_true, measureReal_univ_eq_one] using hp
  · have hu : ‖‖r‖⁻¹ • r‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
    apply (hunit (‖r‖⁻¹ • r) hu).trans
    exact measureReal_mono
      (fun seed hseed => homogeneousSource_residual H solve r hr seed hseed) (measure_ne_top _ _)

def homogeneousPolicy (base : Policy E E E K (E × Seed)) : Policy E E E K (E × Seed) :=
  (base.seedMap (fun p : E × Seed => (‖p.1‖⁻¹ • p.1, p.2)) (by fun_prop)).mapOutput
    (fun p out => ‖p.1‖ • out) (by fun_prop)

theorem homogeneousPolicy_run (base : Policy E E E K (E × Seed))
    (oracle : E → E) (r : E) (seed : Seed) :
    (homogeneousPolicy base).run oracle (r, seed) =
      homogeneousSource (fun r seed => base.run oracle (r, seed)) r seed := by
  simp only [homogeneousPolicy, Policy.mapOutput_run, Policy.seedMap_run, homogeneousSource]

theorem homogeneousPolicy_success (μ : Measure Seed) [IsProbabilityMeasure μ]
    (base : Policy E E E K (E × Seed)) (H : E →L[ℝ] E) (p : ℝ) (hp : p ≤ 1)
    (hunit : ∀ r, ‖r‖ = 1 →
      p ≤ μ.real {seed | ‖H (base.run H (r, seed)) - r‖ ≤ 1 / 2}) (r : E) :
    p ≤ μ.real {seed | ‖H ((homogeneousPolicy base).run H (r, seed)) - r‖ ≤ ‖r‖ / 2} := by
  simpa only [homogeneousPolicy_run] using
    homogeneousSource_success μ H (fun r seed => base.run H (r, seed)) p hp hunit r

end
end Matvec.SourceIterationPolicy
