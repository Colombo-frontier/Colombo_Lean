import Matvec.SourcePower
import Matvec.RandomStart

/-!
# A measurable spectral estimator built from a randomized source solver

The starts are actual normalized Gaussian vectors. Approximate inverse
applications are actual verified repetitions followed by adaptive refinement.
Every random seed is drawn from an explicit product measure.
-/

namespace Matvec

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def gaussianUnitStart (z : Fin (Module.finrank ℝ E) → ℝ) : E :=
  (stdOrthonormalBasis ℝ E).repr.symm
    ((WithLp.equiv 2 _).symm (RandomStart.normalizedVector z))

variable {E}

theorem gaussianUnitStart_norm_le (z : Fin (Module.finrank ℝ E) → ℝ) :
    ‖gaussianUnitStart E z‖ ≤ 1 := by
  unfold gaussianUnitStart
  rw [LinearIsometryEquiv.norm_map]
  by_cases hz : z = 0
  · subst z
    simp [RandomStart.normalizedVector]
  · have h := LowRank.euclidean_dot_self
      ((WithLp.equiv 2 _).symm (RandomStart.normalizedVector z))
    have hs := RandomStart.normalizedVector_on_sphere z hz
    change RandomStart.normalizedVector z ⬝ᵥ RandomStart.normalizedVector z = _ at h
    rw [hs] at h
    nlinarith [norm_nonneg ((WithLp.equiv 2 _).symm (RandomStart.normalizedVector z))]

theorem gaussianUnitStart_projection {v : E} (hv : ‖v‖ = 1)
    (hd : 0 < Module.finrank ℝ E) :
    RandomStart.intervalMass / 2 ≤ (LowRank.iidVectorLaw (Module.finrank ℝ E) 1).real
      {z | Real.sqrt (RandomStart.intervalMass / 2) / Real.sqrt (Module.finrank ℝ E) ≤
        |⟪v, gaussianUnitStart E z⟫_ℝ|} := by
  let b := stdOrthonormalBasis ℝ E
  have hv' : (fun i => b.repr v i) ⬝ᵥ (fun i => b.repr v i) = 1 := by
    have hh := LowRank.euclidean_dot_self (b.repr v)
    simpa only [b.repr.norm_map, hv, one_pow] using hh
  have h := RandomStart.random_start_probability hd (fun i => b.repr v i) hv'
  have hinner (z : Fin (Module.finrank ℝ E) → ℝ) :
      ⟪v, gaussianUnitStart E z⟫_ℝ = (fun i => b.repr v i) ⬝ᵥ RandomStart.normalizedVector z := by
    rw [← b.repr.inner_map_map v (gaussianUnitStart E z)]
    change ⟪b.repr v, b.repr (b.repr.symm ((WithLp.equiv 2 _).symm
      (RandomStart.normalizedVector z)))⟫_ℝ = _
    rw [b.repr.apply_symm_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    rfl
  simpa only [hinner] using h

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_gaussianUnitStart : Measurable (gaussianUnitStart E) :=
  (stdOrthonormalBasis ℝ E).repr.symm.continuous.measurable.comp
    ((PiLp.continuous_equiv_symm 2 _).measurable.comp
      (RandomStart.measurable_normalizedVector _))

def sourceStartComponent : ℝ := Real.sqrt (RandomStart.intervalMass / 2)
def sourceStartProbability : ℝ := RandomStart.intervalMass / 2

theorem sourceStart_constants_pos : 0 < sourceStartComponent ∧ 0 < sourceStartProbability :=
  ⟨Real.sqrt_pos.mpr (div_pos RandomStart.intervalMass_pos (by norm_num)),
    div_pos RandomStart.intervalMass_pos (by norm_num)⟩

variable {Seed : Type*} [MeasurableSpace Seed]

def refinedVerifiedSource (H : E →L[ℝ] E) (base : E → Seed → E) (R J : ℕ) :=
  refinedSource H (verifiedSource H base R) J

def sourceEstimator (H : E →L[ℝ] E) (base : E → Seed → E) (R : ℕ) :=
  let d := Module.finrank ℝ E
  let ν := sourceStartComponent
  let q := inversePowerLengthFor ν d
  let η := inversePowerAccuracyFor ν d
  let J := refinementLength η
  fun p : (Fin d → ℝ) × SeedBlock (SeedBlock (Fin (R + 1) → Seed) J) q =>
    sourcePowerEstimate (refinedVerifiedSource H base R J) q (gaussianUnitStart E p.1) p.2

def sourceEstimatorLaw (μ : Measure Seed) (R : ℕ) :
    Measure ((Fin (Module.finrank ℝ E) → ℝ) ×
      SeedBlock (SeedBlock (Fin (R + 1) → Seed)
        (refinementLength (inversePowerAccuracyFor sourceStartComponent (Module.finrank ℝ E))))
          (inversePowerLengthFor sourceStartComponent (Module.finrank ℝ E))) :=
  (LowRank.iidVectorLaw (Module.finrank ℝ E) 1).prod
    (seedBlockLaw (seedBlockLaw (Measure.pi (fun _ : Fin (R + 1) => μ))
      (refinementLength (inversePowerAccuracyFor sourceStartComponent (Module.finrank ℝ E))))
        (inversePowerLengthFor sourceStartComponent (Module.finrank ℝ E)))

theorem measurable_sourceEstimator (H : E →L[ℝ] E) (base : E → Seed → E)
    (hbase : Measurable (fun p : E × Seed => base p.1 p.2)) (R : ℕ) :
    Measurable (sourceEstimator H base R) :=
  (measurable_sourcePowerEstimate _
    (measurable_refinedSource H _ (measurable_verifiedSource H base hbase R) _) _).comp
      ((measurable_gaussianUnitStart.comp measurable_fst).prodMk measurable_snd)

/-- Source solver to spectral estimation, with concrete Gaussian starts and
all adaptive correction probabilities proved. The inverse and its symmetry
are mathematical facts about H; the executed estimator only queries H. -/
theorem sourceEstimator_probability [Nontrivial E]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (H M : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (hHM : ∀ x, H (M x) = x) (hMH : ∀ x, M (H x) = x)
    (base : E → Seed → E)
    (hbase : Measurable (fun p : E × Seed => base p.1 p.2))
    (hsuccess : ∀ r, 3 / 5 ≤ μ.real {seed | ‖H (base r seed) - r‖ ≤ ‖r‖ / 2})
    (hd : 2 ≤ Module.finrank ℝ E) (R : ℕ) :
    let d := Module.finrank ℝ E
    let q := inversePowerLengthFor sourceStartComponent d
    let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
    sourceStartProbability - (q : ℝ) * J * (2 / 5 : ℝ) ^ (R + 1) ≤
      (sourceEstimatorLaw (E := E) μ R).real
        {s | ‖M‖ / 2 ≤ sourceEstimator H base R s ∧ sourceEstimator H base R s ≤ 2 * ‖M‖} ∧
    (sourceEstimatorLaw (E := E) μ R).real
      {s | 2 * ‖M‖ < sourceEstimator H base R s} ≤
        (q : ℝ) * J * (2 / 5 : ℝ) ^ (R + 1) := by
  let d := Module.finrank ℝ E
  let ν := sourceStartComponent
  let q := inversePowerLengthFor ν d
  let η := inversePowerAccuracyFor ν d
  let J := refinementLength η
  let ampμ := Measure.pi (fun _ : Fin (R + 1) => μ)
  let app := refinedVerifiedSource H base R J
  have hν : 0 < ν := sourceStart_constants_pos.1
  obtain ⟨hq, _, hthreshold⟩ := inversePowerLengthFor_bounds ν hν d hd
  obtain ⟨hη, hsmall, haccuracy⟩ := inversePowerAccuracyFor_bounds ν hν d hd
  have hJ := (refinementLength_bounds η hη).2
  have hamp := measurable_verifiedSource H base hbase R
  have happ : Measurable (fun p : E × SeedBlock (Fin (R + 1) → Seed) J => app p.1 p.2) :=
    measurable_refinedSource H _ hamp J
  have hfail (g : E) : (seedBlockLaw ampμ J).real
      {seed | η * ‖M‖ * ‖g‖ < ‖app g seed - M g‖} ≤
      (J : ℝ) * (2 / 5 : ℝ) ^ (R + 1) :=
    refinedSource_failure ampμ H M _ hamp hMH _ (by positivity)
      (verifiedSource_failure μ H base hbase hsuccess R) J η hJ g
  have h := random_sourcePower_probability
    (LowRank.iidVectorLaw d 1) (gaussianUnitStart E) measurable_gaussianUnitStart gaussianUnitStart_norm_le
    (seedBlockLaw ampμ J) M (inverse_isSymmetric H M hH hHM) app happ
    ν η ((J : ℝ) * (2 / 5 : ℝ) ^ (R + 1)) sourceStartProbability d q hν (by omega) hq
    hη.le (by positivity) hfail
    (fun v hv => gaussianUnitStart_projection hv (by omega)) hsmall haccuracy hthreshold
  simpa only [mul_assoc] using h

end
end Matvec
