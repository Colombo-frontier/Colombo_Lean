import NoisyZO.SymmetricTaylor
import NoisyZO.HardFamily
import NoisyZO.Model
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Uniform probability measures on the Euclidean unit ball and sphere

The manuscript's smoothing argument uses a uniform point of the unit ball and
a uniform direction on the unit sphere.  Here both distributions are defined
from Lebesgue/Haar measure and normalized to probability measures.  We record
the support and central-symmetry properties needed by the Taylor argument.
-/

open MeasureTheory Metric Set
open scoped Gradient

namespace NoisyZO

noncomputable section

/-- Lebesgue measure restricted to the open Euclidean unit ball, bundled as a
finite measure. -/
def unitBallFiniteMeasure (d : ℕ) : FiniteMeasure (Point d) :=
  ⟨volume.restrict (ball 0 1), ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact Metric.isBounded_ball.measure_lt_top⟩⟩

theorem unitBallFiniteMeasure_ne_zero (d : ℕ) :
    unitBallFiniteMeasure d ≠ 0 := by
  intro hzero
  have hzero' : ((unitBallFiniteMeasure d : FiniteMeasure (Point d)) :
      Measure (Point d)) = 0 := congrArg FiniteMeasure.toMeasure hzero
  change volume.restrict (ball 0 1) = 0 at hzero'
  have huniv := congrArg (fun μ : Measure (Point d) ↦ μ univ) hzero'
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at huniv
  exact (measure_ball_pos (volume : Measure (Point d)) (0 : Point d)
    (show 0 < (1 : ℝ) by norm_num)).ne' (by simpa using huniv)

/-- The uniform probability distribution on the Euclidean unit ball. -/
def uniformUnitBall (d : ℕ) : ProbabilityMeasure (Point d) :=
  (unitBallFiniteMeasure d).normalize

theorem unitBallFiniteMeasure_map_neg (d : ℕ) :
    Measure.map (fun x : Point d ↦ -x)
        (unitBallFiniteMeasure d : Measure (Point d)) =
      (unitBallFiniteMeasure d : Measure (Point d)) := by
  change Measure.map (fun x : Point d ↦ -x)
      (volume.restrict (ball 0 1)) = volume.restrict (ball 0 1)
  calc
    Measure.map (fun x : Point d ↦ -x) (volume.restrict (ball 0 1)) =
        Measure.map (fun x : Point d ↦ -x)
          (volume.restrict ((fun x : Point d ↦ -x) ⁻¹' ball 0 1)) := by
            congr 2
            ext x
            simp [Metric.mem_ball, dist_eq_norm]
    _ = (Measure.map (fun x : Point d ↦ -x) volume).restrict (ball 0 1) :=
      (measurableEmbedding_neg.restrict_map volume (ball 0 1)).symm
    _ = volume.restrict (ball 0 1) := by
      rw [Measure.map_neg_eq_self]

theorem uniformUnitBall_isCentrallySymmetric (d : ℕ) :
    IsCentrallySymmetric (uniformUnitBall d : Measure (Point d)) := by
  have hrepr :=
    (unitBallFiniteMeasure d).normalize_eq_inv_mass_smul_of_nonzero
      (unitBallFiniteMeasure_ne_zero d)
  have hrepr' : (uniformUnitBall d : Measure (Point d)) =
      (unitBallFiniteMeasure d).mass⁻¹ •
        (unitBallFiniteMeasure d : Measure (Point d)) := by
    exact congrArg FiniteMeasure.toMeasure hrepr
  rw [IsCentrallySymmetric, hrepr',
    Measure.map_smul _ measurable_neg.aemeasurable,
    unitBallFiniteMeasure_map_neg]

theorem uniformUnitBall_norm_lt_one (d : ℕ) :
    ∀ᵐ x ∂(uniformUnitBall d : Measure (Point d)), ‖x‖ < 1 := by
  have hrepr :=
    (unitBallFiniteMeasure d).normalize_eq_inv_mass_smul_of_nonzero
      (unitBallFiniteMeasure_ne_zero d)
  have hrepr' : (uniformUnitBall d : Measure (Point d)) =
      (unitBallFiniteMeasure d).mass⁻¹ •
        (unitBallFiniteMeasure d : Measure (Point d)) := by
    exact congrArg FiniteMeasure.toMeasure hrepr
  rw [hrepr']
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simpa [Metric.mem_ball, dist_eq_norm] using hx

theorem uniformUnitBall_norm_le_one (d : ℕ) :
    ∀ᵐ x ∂(uniformUnitBall d : Measure (Point d)), ‖x‖ ≤ 1 :=
  (uniformUnitBall_norm_lt_one d).mono fun _ hx ↦ hx.le

/-- On the region used by the estimator, the normalized objective's gradient
is Bochner integrable under the concrete uniform-ball distribution. -/
theorem NormalizedObjective.integrable_gradient_affine_uniformUnitBall
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) (r : ℝ) (hx : ‖x‖ ≤ 1) (hr : |r| ≤ 1) :
    Integrable (fun v ↦ ∇ F.f (x + r • v))
      (uniformUnitBall d : Measure (Point d)) := by
  have hmeas : AEStronglyMeasurable (fun v ↦ ∇ F.f (x + r • v))
      (uniformUnitBall d : Measure (Point d)) :=
    (F.gradient_continuous.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᵐ v ∂(uniformUnitBall d : Measure (Point d)),
      ‖∇ F.f (x + r • v)‖ ≤ 9 := by
    filter_upwards [uniformUnitBall_norm_le_one d] with v hv
    apply F.gradient_norm_le_nine
    calc
      ‖x + r • v‖ ≤ ‖x‖ + ‖r • v‖ := norm_add_le _ _
      _ = ‖x‖ + |r| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 2 := by nlinarith [norm_nonneg v, abs_nonneg r]
  exact (integrable_const (9 : ℝ)).mono' hmeas hbound

/-- Odd Taylor coefficients vanish under the concrete uniform-ball law. -/
theorem uniformUnitBall_odd_taylor_term_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ Point d) F)
    (hm : Odd m) (r : ℝ) :
    (∫ v, A (fun _ ↦ r • v) ∂(uniformUnitBall d : Measure (Point d))) = 0 :=
  integral_scaled_multilinear_diagonal_eq_zero_of_odd
    (uniformUnitBall d : Measure (Point d))
    (uniformUnitBall_isCentrallySymmetric d) A hm r

/-- The concrete uniform-ball average of the Taylor remainder satisfies the
same dimension-free bound as its pointwise operator-norm estimate. -/
theorem norm_uniformUnitBall_holderTaylorRemainder_smul_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (m : ℕ) (x : Point d) (r L α : ℝ)
    (hL : 0 ≤ L) (hα : 0 < α)
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ m g u - iteratedFDeriv ℝ m g v‖ ≤
        L * ‖u - v‖ ^ α) :
    ‖∫ v, holderTaylorRemainder g m x (r • v)
        ∂(uniformUnitBall d : Measure (Point d))‖ ≤
      (Nat.factorial (m - 1) : ℝ)⁻¹ *
        (L * |r| ^ α * |r| ^ m) :=
  norm_integral_holderTaylorRemainder_smul_le
    (uniformUnitBall d : Measure (Point d)) g m x r L α hL hα
    (uniformUnitBall_norm_le_one d) hholder

/-- The surface measure induced by Euclidean volume on the unit sphere. -/
def unitSphereFiniteMeasure (d : ℕ) :
    FiniteMeasure (sphere (0 : Point d) 1) :=
  ⟨volume.toSphere, by infer_instance⟩

theorem unitSphere_nonempty {d : ℕ} (hd : 0 < d) :
    Nonempty (sphere (0 : Point d) 1) := by
  let i : Fin d := ⟨0, hd⟩
  refine ⟨⟨EuclideanSpace.single i 1, ?_⟩⟩
  simp

theorem unitSphereFiniteMeasure_ne_zero {d : ℕ} (hd : 0 < d) :
    unitSphereFiniteMeasure d ≠ 0 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro hzero
  have hzero' : ((unitSphereFiniteMeasure d :
      FiniteMeasure (sphere (0 : Point d) 1)) :
        Measure (sphere (0 : Point d) 1)) = 0 :=
    congrArg FiniteMeasure.toMeasure hzero
  change (volume : Measure (Point d)).toSphere = 0 at hzero'
  exact Measure.toSphere_ne_zero volume hzero'

/-- The normalized surface probability measure, still carried by the sphere
subtype. -/
def uniformUnitSphereSubtype (d : ℕ) (hd : 0 < d) :
    ProbabilityMeasure (sphere (0 : Point d) 1) := by
  letI : Nonempty (sphere (0 : Point d) 1) := unitSphere_nonempty hd
  exact (unitSphereFiniteMeasure d).normalize

/-- The uniform unit-sphere distribution viewed as a probability measure on
the ambient Euclidean space. -/
def uniformUnitSphere (d : ℕ) (hd : 0 < d) : ProbabilityMeasure (Point d) :=
  (uniformUnitSphereSubtype d hd).map Subtype.val

theorem uniformUnitSphere_norm_eq_one {d : ℕ} (hd : 0 < d) :
    ∀ᵐ u ∂(uniformUnitSphere d hd : Measure (Point d)), ‖u‖ = 1 := by
  have hp : MeasurableSet {u : Point d | ‖u‖ = 1} := by
    exact (measurableSet_singleton (1 : ℝ)).preimage continuous_norm.measurable
  rw [uniformUnitSphere, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (by fun_prop) hp).2
  exact Filter.Eventually.of_forall fun u ↦ by simpa using u.property

end

end NoisyZO
