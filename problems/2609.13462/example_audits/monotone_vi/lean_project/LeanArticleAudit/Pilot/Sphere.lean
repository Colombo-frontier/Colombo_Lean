import LeanArticleAudit.Pilot.Operator
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.SubGaussian

/-!
# A spherical projection tail bound

Mathlib supplies standard finite-dimensional Gaussian measures, product
measures, the sub-Gaussian MGF abstraction, its Chernoff bound, and the finite
surface measure `Measure.toSphere` obtained from an additive Haar measure by
polar coordinates.  The last of these is a canonical starting point, but the
library currently has no theorem identifying its normalized projection law
(or its even moments), and no theorem identifying the direction of
`stdGaussian` with normalized `Measure.toSphere`.  The available Beta and
Gamma distribution files prove density normalization but do not connect those
laws to a spherical projection or Gaussian radius.

This foundational file exposes the MGF estimate as the field `projection_mgf`
of `CertifiedUniformUnitSphereProjectionMGF` and isolates the geometric
calculation as `UniformSphereEvenMomentRecurrenceBridge`.  The downstream
module `SphereRecurrence` proves that bridge by reflections and polynomial
coefficient comparison, then derives the unconditional `lem:sphere` headline.
-/

open MeasureTheory ProbabilityTheory Set Real Metric
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

section UniformLaw

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Geometric/probabilistic meaning of a random vector being uniform on the
unit sphere of a `k`-dimensional real inner-product space.  Using the space
itself is the coordinate reduction of the paper's embedded-subspace wording. -/
structure IsUniformUnitSphereLaw (k : ℕ) (v : Ω → E)
    (μ : Measure Ω) : Prop where
  dimension : Module.finrank ℝ E = k
  measurable : AEMeasurable v μ
  unit_ae : ∀ᵐ ω ∂μ, ‖v ω‖ = 1
  rotational_invariant : ∀ U : E ≃ₗᵢ[ℝ] E,
    Measure.map (fun ω ↦ U (v ω)) μ = Measure.map v μ

end UniformLaw

section Sphere

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Reflection invariance forces every odd one-dimensional projection moment
of a uniform sphere law to vanish.  No integrability premise is needed for the
identity; for a probability law, integrability also follows from `unit_ae`. -/
theorem uniformSphere_odd_projection_moment {μ : Measure Ω} {k : ℕ}
    {v : Ω → E} (hv : IsUniformUnitSphereLaw k v μ) (a : E) (n : ℕ) :
    ∫ ω, (inner ℝ (v ω) a) ^ (2 * n + 1) ∂μ = 0 := by
  let U : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  let f : E → ℝ := fun y => (inner ℝ y a) ^ (2 * n + 1)
  have hf : Continuous f := by fun_prop
  have hdist : Measure.map (fun ω => U (v ω)) μ = Measure.map v μ :=
    hv.rotational_invariant U
  have hsymm : (∫ ω, f (v ω) ∂μ) = ∫ ω, f (U (v ω)) ∂μ := by
    calc
      (∫ ω, f (v ω) ∂μ) = ∫ y, f y ∂Measure.map v μ :=
        (integral_map hv.measurable hf.aestronglyMeasurable).symm
      _ = ∫ y, f y ∂Measure.map (fun ω => U (v ω)) μ := by rw [hdist]
      _ = ∫ ω, f (U (v ω)) ∂μ :=
        integral_map (U.continuous.aemeasurable.comp_aemeasurable hv.measurable)
          hf.aestronglyMeasurable
  have hpoint : ∀ ω, f (U (v ω)) = -(f (v ω)) := by
    intro ω
    simp [f, U, pow_succ]
  change (∫ ω, f (v ω) ∂μ) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_neg] at hsymm
  linarith

/-- A uniform unit-sphere law together with the projection MGF estimate from
the paper's Gaussian/radial calculation.  This is explicitly a certificate
interface, not an unconditional proof of that calculation. -/
structure CertifiedUniformUnitSphereProjectionMGF (k : ℕ) (v : Ω → E)
    (μ : Measure Ω) extends IsUniformUnitSphereLaw k v μ where
  projection_mgf : ∀ (x : E) (R : ℝ), ‖x‖ ≤ R →
    HasSubgaussianMGF (fun ω ↦ inner ℝ (v ω) x)
      ⟨R ^ 2 / k, div_nonneg (sq_nonneg R) (Nat.cast_nonneg k)⟩ μ

/-- The single remaining geometric moment identity.  A two-plane rotation and
differentiation at angle zero should give this recurrence; together with the
proved odd-moment identity and the zeroth moment, it determines all projection
moments and yields the desired MGF estimate by the exponential power series.

This is a proposition only and is not assumed below, so it introduces no
additional hypothesis.  It is discharged in `SphereRecurrence`. -/
def UniformSphereEvenMomentRecurrenceBridge : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ), 1 ≤ k → ∀ (v : Ω → E),
    IsUniformUnitSphereLaw k v μ →
    ∀ (a : E) (n : ℕ),
      ((k : ℝ) + 2 * (n : ℝ)) *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * (n + 1)) ∂μ) =
        (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ)

/-- The scalar random variable obtained by projecting a random direction onto
a fixed vector. -/
def sphericalProjection (v : Ω → E) (x : E) (ω : Ω) : ℝ :=
  inner ℝ (v ω) x

/-- Two-sided Chernoff bound with the article's exact constant.  This helper
contains no sphere-specific assumptions: it is the fully checked implication
from the MGF estimate to the tail estimate. -/
theorem abs_tail_le_of_subgaussian_mgf {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c a : ℝ}
    (hc : 0 ≤ c) (ha : 0 < a)
    (hX : HasSubgaussianMGF X ⟨c, hc⟩ μ) :
    μ.real {ω | |X ω| > a} ≤ 2 * exp (-a ^ 2 / (2 * c)) := by
  have hpos := hX.measure_ge_le ha.le
  have hneg := hX.neg.measure_ge_le ha.le
  have hpos' : μ.real {ω | a ≤ X ω} ≤ exp (-a ^ 2 / (2 * c)) := by
    change μ.real {ω | a ≤ X ω} ≤ exp (-a ^ 2 / (2 * c)) at hpos
    exact hpos
  have hneg' : μ.real {ω | a ≤ -X ω} ≤ exp (-a ^ 2 / (2 * c)) := by
    change μ.real {ω | a ≤ (-X) ω} ≤ exp (-a ^ 2 / (2 * c)) at hneg
    simpa only [Pi.neg_apply] using hneg
  have hsubset : {ω | |X ω| > a} ⊆
      {ω | a ≤ X ω} ∪ {ω | a ≤ -X ω} := by
    intro ω hω
    simp only [mem_setOf_eq, mem_union]
    change a < |X ω| at hω
    by_cases hsign : 0 ≤ X ω
    · left
      rw [abs_of_nonneg hsign] at hω
      exact hω.le
    · right
      rw [abs_of_neg (lt_of_not_ge hsign)] at hω
      exact hω.le
  calc
    μ.real {ω | |X ω| > a} ≤
        μ.real ({ω | a ≤ X ω} ∪ {ω | a ≤ -X ω}) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ μ.real {ω | a ≤ X ω} + μ.real {ω | a ≤ -X ω} :=
      measureReal_union_le _ _
    _ ≤ exp (-a ^ 2 / (2 * c)) + exp (-a ^ 2 / (2 * c)) :=
      add_le_add hpos' hneg'
    _ = 2 * exp (-a ^ 2 / (2 * c)) := by ring

/-- Conditional/certificate form of `lem:sphere`: if `v` has a certified uniform law on the unit sphere of a
`k`-dimensional real inner-product space and `‖x‖ ≤ R`, then its projection
obeys the stated spherical tail estimate.

The strict event and constants `2` and `1/2` match the article verbatim.  The
downstream module `SphereRecurrence` constructs this MGF certificate from the
uniform-law hypotheses alone. -/
theorem conditional_spherical_tail_inequality {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 1 ≤ k) {v : Ω → E}
    (hv : CertifiedUniformUnitSphereProjectionMGF k v μ)
    (x : E) {R a : ℝ} (hx : ‖x‖ ≤ R) (ha : 0 < a) :
    μ.real {ω | |inner ℝ (v ω) x| > a} ≤
      2 * exp (-((k : ℝ) * a ^ 2) / (2 * R ^ 2)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have hc : 0 ≤ R ^ 2 / (k : ℝ) := div_nonneg (sq_nonneg R) hk0.le
  have htail := abs_tail_le_of_subgaussian_mgf hc ha (hv.projection_mgf x R hx)
  convert htail using 1
  congr 2
  by_cases hR0 : R = 0
  · simp [hR0]
  · field_simp

/-- Proposition-valued conditional certificate contract for hashing.  The
unconditional contract and proof live in `SphereRecurrence`. -/
def ConditionalSphericalTailClaim : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ), 1 ≤ k → ∀ (v : Ω → E),
    CertifiedUniformUnitSphereProjectionMGF k v μ →
    ∀ (x : E) (R a : ℝ), ‖x‖ ≤ R → 0 < a →
      μ.real {ω | |inner ℝ (v ω) x| > a} ≤
        2 * exp (-((k : ℝ) * a ^ 2) / (2 * R ^ 2))

/-- Kernel-checked headline for the conditional/certificate part of
`lem:sphere`; intentionally not named as an unconditional proof. -/
theorem conditionalSphericalTailClaim_proof : ConditionalSphericalTailClaim := by
  intro Ω E _ _ _ _ _ _ μ _ k hk v hv x R a hx ha
  exact conditional_spherical_tail_inequality hk hv x hx ha

end Sphere

end LeanArticleAudit.Pilot
