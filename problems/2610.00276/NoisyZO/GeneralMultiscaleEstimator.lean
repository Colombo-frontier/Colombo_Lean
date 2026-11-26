import NoisyZO.SphericalEstimator
import NoisyZO.MultiscaleBias
import NoisyZO.GaussianFourNoise
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Chebyshev

/-!
# Concrete multiscale spherical estimator for every finite smoothness order

This module constructs a finite dyadic estimator for an arbitrary
`SmoothnessOrder`.  It uses `k` radii and Lagrange weights to cancel every
Taylor degree from `1` through `k - 1`; this is a slightly redundant variant
of the manuscript's even-degree rule, with the same rate and a raw-call
constant depending only on the fixed order.  The uniform-sphere mean,
Gaussian product law, bias, second moment, and all integrability obligations
are proved internally.
-/

open MeasureTheory
open scoped BigOperators Gradient

namespace NoisyZO

noncomputable section

def generalDyadicRadius {q : ℕ} (j : Fin q) : ℝ :=
  (2 : ℝ) ^ (-(j : ℤ))

theorem generalDyadicRadius_pos {q : ℕ} (j : Fin q) :
    0 < generalDyadicRadius j := by
  exact zpow_pos (by norm_num) _

theorem generalDyadicRadius_le_one {q : ℕ} (j : Fin q) :
    generalDyadicRadius j ≤ 1 := by
  exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

theorem generalDyadicRadius_injective (q : ℕ) :
    Function.Injective (generalDyadicRadius : Fin q → ℝ) := by
  intro i j hij
  have hexp : -(i : ℤ) = -(j : ℤ) := by
    exact (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)) hij
  have : (i : ℤ) = (j : ℤ) := by omega
  exact Fin.ext (by exact_mod_cast this)

def generalMultiscaleWeight {q : ℕ} (j : Fin q) : ℝ :=
  lagrangeWeight (generalDyadicRadius : Fin q → ℝ) j

theorem sum_generalMultiscaleWeight_eq_one {q : ℕ} (hq : 0 < q) :
    ∑ j : Fin q, generalMultiscaleWeight j = 1 := by
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  exact sum_lagrangeWeight_eq_one generalDyadicRadius
    (generalDyadicRadius_injective q)

theorem generalMultiscaleWeight_moment {q ell : ℕ}
    (hell_pos : 0 < ell) (hell : ell < q) :
    ∑ j : Fin q, generalMultiscaleWeight j * generalDyadicRadius j ^ ell = 0 := by
  exact sum_lagrangeWeight_mul_pow_eq_zero generalDyadicRadius
    (generalDyadicRadius_injective q) hell_pos (by simpa using hell)

def fullTaylorCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : ℕ) (g : Point d → E) (m : ℕ) (x : Point d) (ell : Fin m) : E :=
  ∫ v, ballTaylorTerm g (ell.val + 1) x 1 v
    ∂(uniformUnitBall d : Measure (Point d))

theorem ballSmoothedField_eq_full_indexed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : ℕ) (g : Point d → E) (m : ℕ) (hm : 0 < m)
    (x : Point d) (r : ℝ)
    (hsmooth : ContDiff ℝ m g)
    (hmain : Integrable (fun v ↦ g (x + r • v))
      (uniformUnitBall d : Measure (Point d))) :
    ballSmoothedField d g x r =
      g x + (∑ ell : Fin m, r ^ (ell.val + 1) • fullTaylorCoeff d g m x ell) +
        ∫ v, holderTaylorRemainder g m x (r • v)
          ∂(uniformUnitBall d : Measure (Point d)) := by
  rw [ballSmoothedField_eq_taylor_sum_add_remainder
    d g m hm x r hsmooth hmain]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  congr 1
  · rw [integral_ballTaylorTerm_radius_factor]
    simp only [Fin.val_zero, Nat.cast_zero, pow_zero, one_smul, ballTaylorTerm,
      Nat.factorial_zero, Nat.cast_one, inv_one]
    calc
      (∫ v, (iteratedFDeriv ℝ 0 g x) (fun _ ↦ v)
          ∂(uniformUnitBall d : Measure (Point d))) =
          ∫ _v : Point d, g x ∂(uniformUnitBall d : Measure (Point d)) := by
        apply integral_congr_ae
        filter_upwards with v
        exact iteratedFDeriv_zero_apply (fun _ : Fin 0 ↦ v)
      _ = g x := by simp
  · apply Finset.sum_congr rfl
    intro ell _hell
    exact integral_ballTaylorTerm_radius_factor d g (ell.val + 1) x r

def fullMultiscaleBallField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : ℕ) (g : Point d → E) (m : ℕ) (x : Point d) (h : ℝ) : E :=
  ∑ j : Fin (m + 1), generalMultiscaleWeight j •
    ballSmoothedField d g x (h * generalDyadicRadius j)

theorem fullMultiscaleBallField_eq_value_add_remainders
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : ℕ) (g : Point d → E) (m : ℕ) (hm : 0 < m)
    (x : Point d) (h : ℝ)
    (hsmooth : ContDiff ℝ m g)
    (hmain : ∀ j : Fin (m + 1),
      Integrable (fun v ↦ g (x + (h * generalDyadicRadius j) • v))
        (uniformUnitBall d : Measure (Point d))) :
    fullMultiscaleBallField d g m x h = g x +
      ∑ j : Fin (m + 1), generalMultiscaleWeight j •
        (∫ v, holderTaylorRemainder g m x
            ((h * generalDyadicRadius j) • v)
          ∂(uniformUnitBall d : Measure (Point d))) := by
  let mean : Fin (m + 1) → E := fun j ↦
    ballSmoothedField d g x (h * generalDyadicRadius j)
  let err : Fin (m + 1) → E := fun j ↦
    ∫ v, holderTaylorRemainder g m x
        ((h * generalDyadicRadius j) • v)
      ∂(uniformUnitBall d : Measure (Point d))
  let coeff : Fin m → E := fun ell ↦
    h ^ (ell.val + 1) • fullTaylorCoeff d g m x ell
  have hexpansion : ∀ j,
      mean j = g x +
        (∑ ell : Fin m,
          generalDyadicRadius j ^ (ell.val + 1) • coeff ell) + err j := by
    intro j
    rw [show mean j = ballSmoothedField d g x
        (h * generalDyadicRadius j) by rfl,
      ballSmoothedField_eq_full_indexed d g m hm x
        (h * generalDyadicRadius j) hsmooth (hmain j)]
    congr 2
    apply Finset.sum_congr rfl
    intro ell _hell
    dsimp only [coeff]
    rw [mul_pow, smul_smul]
    rw [mul_comm]
  have hcancel := weighted_expansion_cancellation
    (J := m) (generalMultiscaleWeight : Fin (m + 1) → ℝ)
    generalDyadicRadius
    (sum_generalMultiscaleWeight_eq_one (by omega : 0 < m + 1))
    (fun ell ↦ generalMultiscaleWeight_moment
      (by omega : 0 < ell.val + 1) (by omega : ell.val + 1 < m + 1))
    mean err (g x) coeff hexpansion
  simpa only [fullMultiscaleBallField, mean, err] using hcancel

theorem norm_fullMultiscaleBallField_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : ℕ) (g : Point d → E) (m : ℕ) (hm : 0 < m)
    (x : Point d) (h L alpha : ℝ) (hL : 0 ≤ L) (halpha : 0 < alpha)
    (hsmooth : ContDiff ℝ m g)
    (hmain : ∀ j : Fin (m + 1),
      Integrable (fun v ↦ g (x + (h * generalDyadicRadius j) • v))
        (uniformUnitBall d : Measure (Point d)))
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ m g u - iteratedFDeriv ℝ m g v‖ ≤
        L * ‖u - v‖ ^ alpha) :
    ‖fullMultiscaleBallField d g m x h - g x‖ ≤
      ∑ j : Fin (m + 1), |generalMultiscaleWeight j| *
        ((Nat.factorial (m - 1) : ℝ)⁻¹ *
          (L * |h * generalDyadicRadius j| ^ alpha *
            |h * generalDyadicRadius j| ^ m)) := by
  rw [fullMultiscaleBallField_eq_value_add_remainders
    d g m hm x h hsmooth hmain]
  simp only [add_sub_cancel_left]
  apply weighted_remainder_norm_bound
  intro j
  exact norm_ballTaylorRemainder_le d g m x
    (h * generalDyadicRadius j) L alpha hL halpha hholder

def generalMultiscaleBiasConstant (o : SmoothnessOrder) : ℝ :=
  (Nat.factorial (o.k - 2) : ℝ)⁻¹ *
    ∑ j : Fin ((o.k - 1) + 1),
      |generalMultiscaleWeight j| *
        generalDyadicRadius j ^ (o.beta - 1)

theorem generalMultiscaleBiasConstant_nonneg (o : SmoothnessOrder) :
    0 ≤ generalMultiscaleBiasConstant o := by
  unfold generalMultiscaleBiasConstant
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro j _hj
    exact mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (generalDyadicRadius_pos j).le _)

theorem NormalizedObjective.norm_fullMultiscaleBallField_sub_gradient_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hx : ‖x‖ ≤ 1) :
    ‖fullMultiscaleBallField d (∇ F.f) (o.k - 1) x h - ∇ F.f x‖ ≤
      generalMultiscaleBiasConstant o * h ^ (o.beta - 1) := by
  have hk := o.two_le_k
  have hm : 0 < o.k - 1 := by omega
  rw [fullMultiscaleBallField_eq_value_add_remainders
    d (∇ F.f) (o.k - 1) hm x h F.gradient_contDiff]
  · simp only [add_sub_cancel_left]
    have hraw := weighted_remainder_norm_bound
      (generalMultiscaleWeight : Fin ((o.k - 1) + 1) → ℝ)
      (fun j ↦ ∫ v, holderTaylorRemainder (∇ F.f) (o.k - 1) x
          ((h * generalDyadicRadius j) • v)
        ∂(uniformUnitBall d : Measure (Point d)))
      (fun j ↦ (Nat.factorial (o.k - 2) : ℝ)⁻¹ *
        |h * generalDyadicRadius j| ^ (o.beta - 1))
      (fun j ↦ F.norm_ballSmoothedGradient_remainder_le x
        (h * generalDyadicRadius j))
    refine hraw.trans_eq ?_
    unfold generalMultiscaleBiasConstant
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    have hr : 0 < generalDyadicRadius j := generalDyadicRadius_pos j
    rw [abs_of_pos (mul_pos hh hr), Real.mul_rpow hh.le hr.le]
    ring
  · intro j
    apply F.integrable_gradient_affine_uniformUnitBall x
      (h * generalDyadicRadius j) hx
    rw [abs_of_pos (mul_pos hh (generalDyadicRadius_pos j))]
    calc
      h * generalDyadicRadius j ≤ 1 * generalDyadicRadius j :=
        mul_le_mul_of_nonneg_right hh1 (generalDyadicRadius_pos j).le
      _ ≤ 1 := by simpa using generalDyadicRadius_le_one j

def fullMultiscaleSphericalSignal
    (d : ℕ) (f : Point d → ℝ) (m : ℕ)
    (x : Point d) (h : ℝ) (u : Point d) : Point d :=
  ∑ j : Fin (m + 1), generalMultiscaleWeight j •
    centralDifferenceSignal d f x (h * generalDyadicRadius j) u

theorem integral_fullMultiscaleSphericalSignal_eq_ballField
    {d : ℕ} (hd : 0 < d) (f : Point d → ℝ) (hf : ContDiff ℝ 1 f)
    (m : ℕ) (x : Point d) {h : ℝ} (hh : 0 < h) :
    (∫ u, fullMultiscaleSphericalSignal d f m x h u
      ∂(uniformUnitSphere d hd : Measure (Point d))) =
        fullMultiscaleBallField d (∇ f) m x h := by
  unfold fullMultiscaleSphericalSignal fullMultiscaleBallField
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _hj
    rw [integral_smul]
    rw [integral_centralDifferenceSignal_eq_ballSmoothedField hd f hf x
      (mul_pos hh (generalDyadicRadius_pos j))]
  · intro j _hj
    have hj : Integrable
        (centralDifferenceSignal d f x (h * generalDyadicRadius j))
        (uniformUnitSphere d hd : Measure (Point d)) := by
      apply continuous_integrable_uniformUnitSphere hd
      unfold centralDifferenceSignal
      have hfc : Continuous f := hf.continuous
      fun_prop
    apply (hj.smul (generalMultiscaleWeight j)).congr
    filter_upwards with u
    rfl

def fullMultiscaleNoiseMeasure (m : ℕ) :
    Measure (Fin (m + 1) → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin (m + 1) ↦ independentGaussianPair)

instance fullMultiscaleNoiseMeasure_isProbability (m : ℕ) :
    IsProbabilityMeasure (fullMultiscaleNoiseMeasure m) := by
  unfold fullMultiscaleNoiseMeasure
  infer_instance

instance fullMultiscaleNoiseMeasure_isFinite (m : ℕ) :
    IsFiniteMeasure (fullMultiscaleNoiseMeasure m) := by
  infer_instance

def fullMultiscaleSphericalNoise
    (d m : ℕ) (h : ℝ) (ξ : Fin (m + 1) → ℝ × ℝ)
    (u : Point d) : Point d :=
  ∑ j : Fin (m + 1),
    (generalMultiscaleWeight j *
      ((d : ℝ) / (2 * h * generalDyadicRadius j)) *
        gaussianPairDifference (ξ j)) • u

def fullMultiscaleSphericalEstimator
    (d : ℕ) (f : Point d → ℝ) (m : ℕ)
    (x : Point d) (h : ℝ)
    (z : (Fin (m + 1) → ℝ × ℝ) × Point d) : Point d :=
  fullMultiscaleSphericalSignal d f m x h z.2 +
    fullMultiscaleSphericalNoise d m h z.1 z.2

def generalMultiscaleSignalWeightSum (o : SmoothnessOrder) : ℝ :=
  ∑ j : Fin ((o.k - 1) + 1), |generalMultiscaleWeight j|

theorem generalMultiscaleSignalWeightSum_nonneg (o : SmoothnessOrder) :
    0 ≤ generalMultiscaleSignalWeightSum o := by
  unfold generalMultiscaleSignalWeightSum
  exact Finset.sum_nonneg fun j _hj ↦ abs_nonneg _

theorem NormalizedObjective.norm_fullMultiscaleSphericalSignal_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (u : Point d) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) :
    ‖fullMultiscaleSphericalSignal d F.f (o.k - 1) x h u‖ ≤
      9 * (d : ℝ) * generalMultiscaleSignalWeightSum o := by
  unfold fullMultiscaleSphericalSignal generalMultiscaleSignalWeightSum
  calc
    ‖∑ j : Fin ((o.k - 1) + 1), generalMultiscaleWeight j •
        centralDifferenceSignal d F.f x (h * generalDyadicRadius j) u‖ ≤
        ∑ j : Fin ((o.k - 1) + 1),
          ‖generalMultiscaleWeight j •
            centralDifferenceSignal d F.f x (h * generalDyadicRadius j) u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin ((o.k - 1) + 1),
        |generalMultiscaleWeight _j| * (9 * (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      have hrpos : 0 < h * generalDyadicRadius j :=
        mul_pos hh (generalDyadicRadius_pos j)
      apply norm_centralDifferenceSignal_le d F.f x hrpos u hu
      have hrle : |h * generalDyadicRadius j| ≤ 1 := by
        rw [abs_of_pos hrpos]
        calc
          h * generalDyadicRadius j ≤ 1 * generalDyadicRadius j :=
            mul_le_mul_of_nonneg_right hh1 (generalDyadicRadius_pos j).le
          _ ≤ 1 := by simpa using generalDyadicRadius_le_one j
      simpa [abs_of_pos hrpos] using
        F.abs_central_difference_le x hrle u hu hx
    _ = 9 * (d : ℝ) *
        ∑ j : Fin ((o.k - 1) + 1), |generalMultiscaleWeight j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

def generalMultiscaleNoiseConstant (o : SmoothnessOrder) : ℝ :=
  (((o.k - 1) + 1 : ℕ) : ℝ) / 2 *
    ∑ j : Fin ((o.k - 1) + 1),
      generalMultiscaleWeight j ^ 2 / generalDyadicRadius j ^ 2

theorem generalMultiscaleNoiseConstant_nonneg (o : SmoothnessOrder) :
    0 ≤ generalMultiscaleNoiseConstant o := by
  unfold generalMultiscaleNoiseConstant
  positivity

theorem integral_gaussianPairDifference_eval_sq
    {q : ℕ} (j : Fin q) :
    (∫ ξ : Fin q → ℝ × ℝ, gaussianPairDifference (ξ j) ^ 2
      ∂Measure.pi (fun _ : Fin q ↦ independentGaussianPair)) = 2 := by
  calc
    (∫ ξ : Fin q → ℝ × ℝ, gaussianPairDifference (ξ j) ^ 2
      ∂Measure.pi (fun _ : Fin q ↦ independentGaussianPair)) =
        ∫ z, gaussianPairDifference z ^ 2 ∂independentGaussianPair := by
      exact integral_comp_eval
        (μ := fun _ : Fin q ↦ independentGaussianPair) (i := j)
        gaussianPairDifference_sq_integrable.aestronglyMeasurable
    _ = 2 := integral_gaussianPairDifference_sq

theorem gaussianPairDifference_eval_sq_integrable
    {q : ℕ} (j : Fin q) :
    Integrable (fun ξ : Fin q → ℝ × ℝ ↦
      gaussianPairDifference (ξ j) ^ 2)
      (Measure.pi (fun _ : Fin q ↦ independentGaussianPair)) := by
  exact integrable_comp_eval
    (μ := fun _ : Fin q ↦ independentGaussianPair) (i := j)
    gaussianPairDifference_sq_integrable

theorem integral_gaussianPairDifference_eval
    {q : ℕ} (j : Fin q) :
    (∫ ξ : Fin q → ℝ × ℝ, gaussianPairDifference (ξ j)
      ∂Measure.pi (fun _ : Fin q ↦ independentGaussianPair)) = 0 := by
  calc
    (∫ ξ : Fin q → ℝ × ℝ, gaussianPairDifference (ξ j)
      ∂Measure.pi (fun _ : Fin q ↦ independentGaussianPair)) =
        ∫ z, gaussianPairDifference z ∂independentGaussianPair := by
      exact integral_comp_eval
        (μ := fun _ : Fin q ↦ independentGaussianPair) (i := j)
        gaussianPairDifference_integrable.aestronglyMeasurable
    _ = 0 := integral_gaussianPairDifference

theorem gaussianPairDifference_eval_integrable
    {q : ℕ} (j : Fin q) :
    Integrable (fun ξ : Fin q → ℝ × ℝ ↦ gaussianPairDifference (ξ j))
      (Measure.pi (fun _ : Fin q ↦ independentGaussianPair)) := by
  exact integrable_comp_eval
    (μ := fun _ : Fin q ↦ independentGaussianPair) (i := j)
    gaussianPairDifference_integrable

theorem norm_fullMultiscaleSphericalNoise_sq_le
    (d m : ℕ) {h : ℝ} (hh : h ≠ 0)
    (ξ : Fin (m + 1) → ℝ × ℝ) (u : Point d) (hu : ‖u‖ = 1) :
    ‖fullMultiscaleSphericalNoise d m h ξ u‖ ^ 2 ≤
      ((m + 1 : ℕ) : ℝ) *
        ∑ j : Fin (m + 1),
          (generalMultiscaleWeight j *
            ((d : ℝ) / (2 * h * generalDyadicRadius j)) *
              gaussianPairDifference (ξ j)) ^ 2 := by
  unfold fullMultiscaleSphericalNoise
  rw [← Finset.sum_smul, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  have hcheb := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin (m + 1))))
    (f := fun j : Fin (m + 1) ↦
      generalMultiscaleWeight j *
        ((d : ℝ) / (2 * h * generalDyadicRadius j)) *
          gaussianPairDifference (ξ j))
  simpa using hcheb

theorem integral_norm_fullMultiscaleSphericalNoise_sq_le
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    {h : ℝ} (hh : 0 < h) (u : Point d) (hu : ‖u‖ = 1) :
    (∫ ξ, ‖fullMultiscaleSphericalNoise d (o.k - 1) h ξ u‖ ^ 2
      ∂fullMultiscaleNoiseMeasure (o.k - 1)) ≤
        generalMultiscaleNoiseConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
  let q : ℕ := (o.k - 1) + 1
  let μ : Measure (Fin q → ℝ × ℝ) :=
    Measure.pi (fun _ : Fin q ↦ independentGaussianPair)
  let rhs : (Fin q → ℝ × ℝ) → ℝ := fun ξ ↦
    (q : ℝ) * ∑ j : Fin q,
      (generalMultiscaleWeight j *
        ((d : ℝ) / (2 * h * generalDyadicRadius j)) *
          gaussianPairDifference (ξ j)) ^ 2
  have hrhsInt : Integrable rhs μ := by
    dsimp only [rhs, μ]
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _hj
    convert (gaussianPairDifference_eval_sq_integrable j).const_mul
      ((generalMultiscaleWeight j *
        ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2) using 1
    funext ξ
    ring
  have hnoiseMeas : AEStronglyMeasurable
      (fun ξ : Fin q → ℝ × ℝ ↦
        ‖fullMultiscaleSphericalNoise d (o.k - 1) h ξ u‖ ^ 2) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [q, μ]
    unfold fullMultiscaleSphericalNoise gaussianPairDifference
    fun_prop
  have hpoint : ∀ ξ : Fin q → ℝ × ℝ,
      ‖fullMultiscaleSphericalNoise d (o.k - 1) h ξ u‖ ^ 2 ≤ rhs ξ := by
    intro ξ
    exact norm_fullMultiscaleSphericalNoise_sq_le d (o.k - 1) hh.ne' ξ u hu
  have hnoiseInt : Integrable
      (fun ξ : Fin q → ℝ × ℝ ↦
        ‖fullMultiscaleSphericalNoise d (o.k - 1) h ξ u‖ ^ 2) μ := by
    apply hrhsInt.mono' hnoiseMeas
    filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ξ
  have hint :
      (∫ ξ : Fin q → ℝ × ℝ, rhs ξ ∂μ) =
        (q : ℝ) * ∑ j : Fin q,
          (generalMultiscaleWeight j *
            ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2 * 2 := by
    dsimp only [rhs]
    rw [integral_const_mul]
    rw [integral_finsetSum]
    · apply congrArg
      apply Finset.sum_congr rfl
      intro j _hj
      rw [show (fun ξ : Fin q → ℝ × ℝ ↦
          (generalMultiscaleWeight j *
            ((d : ℝ) / (2 * h * generalDyadicRadius j)) *
              gaussianPairDifference (ξ j)) ^ 2) =
          fun ξ ↦
            (generalMultiscaleWeight j *
              ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2 *
                gaussianPairDifference (ξ j) ^ 2 by
            funext ξ
            ring,
        integral_const_mul,
        integral_gaussianPairDifference_eval_sq]
    · intro j _hj
      convert (gaussianPairDifference_eval_sq_integrable j).const_mul
        ((generalMultiscaleWeight j *
          ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2) using 1
      funext ξ
      ring
  calc
    (∫ ξ, ‖fullMultiscaleSphericalNoise d (o.k - 1) h ξ u‖ ^ 2
      ∂fullMultiscaleNoiseMeasure (o.k - 1)) =
        ∫ ξ : Fin q → ℝ × ℝ,
          ‖fullMultiscaleSphericalNoise d (o.k - 1) h ξ u‖ ^ 2 ∂μ := by rfl
    _ ≤ ∫ ξ : Fin q → ℝ × ℝ, rhs ξ ∂μ :=
      integral_mono hnoiseInt hrhsInt hpoint
    _ = (q : ℝ) * ∑ j : Fin q,
          (generalMultiscaleWeight j *
            ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2 * 2 := hint
    _ = generalMultiscaleNoiseConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
      dsimp only [q]
      unfold generalMultiscaleNoiseConstant
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _hj
      field_simp [hh.ne', (generalDyadicRadius_pos j).ne']

def fullMultiscaleSampleMeasure (d m : ℕ) (hd : 0 < d) :
    Measure ((Fin (m + 1) → ℝ × ℝ) × Point d) :=
  (fullMultiscaleNoiseMeasure m).prod
    (uniformUnitSphere d hd : Measure (Point d))

instance fullMultiscaleSampleMeasure_isProbability
    (d m : ℕ) (hd : 0 < d) :
    IsProbabilityMeasure (fullMultiscaleSampleMeasure d m hd) := by
  unfold fullMultiscaleSampleMeasure
  infer_instance

theorem fullMultiscaleSphericalNoise_integrable
    (d m : ℕ) (hd : 0 < d) (h : ℝ) :
    Integrable (fun z ↦ fullMultiscaleSphericalNoise d m h z.1 z.2)
      (fullMultiscaleSampleMeasure d m hd) := by
  unfold fullMultiscaleSphericalNoise fullMultiscaleSampleMeasure
  apply integrable_finsetSum
  intro j _hj
  let c : ℝ := generalMultiscaleWeight j *
    ((d : ℝ) / (2 * h * generalDyadicRadius j))
  have hscalar : Integrable
      (fun ξ : Fin (m + 1) → ℝ × ℝ ↦
        c * gaussianPairDifference (ξ j))
      (fullMultiscaleNoiseMeasure m) := by
    exact (gaussianPairDifference_eval_integrable j).const_mul c
  have hu : Integrable (fun u : Point d ↦ u)
      (uniformUnitSphere d hd : Measure (Point d)) :=
    continuous_integrable_uniformUnitSphere hd (fun u : Point d ↦ u) continuous_id
  exact hscalar.smul_prod hu

theorem integral_fullMultiscaleSphericalNoise_eq_zero
    (d m : ℕ) (hd : 0 < d) (h : ℝ) :
    (∫ z, fullMultiscaleSphericalNoise d m h z.1 z.2
      ∂fullMultiscaleSampleMeasure d m hd) = 0 := by
  unfold fullMultiscaleSphericalNoise fullMultiscaleSampleMeasure
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _hj
    let c : ℝ := generalMultiscaleWeight j *
      ((d : ℝ) / (2 * h * generalDyadicRadius j))
    change (∫ z, (c * gaussianPairDifference (z.1 j)) • z.2
      ∂(fullMultiscaleNoiseMeasure m).prod
        (uniformUnitSphere d hd : Measure (Point d))) = 0
    have hscalar :
        (∫ ξ : Fin (m + 1) → ℝ × ℝ,
          c * gaussianPairDifference (ξ j)
            ∂fullMultiscaleNoiseMeasure m) = 0 := by
      unfold fullMultiscaleNoiseMeasure
      rw [integral_const_mul, integral_gaussianPairDifference_eval, mul_zero]
    calc
      (∫ z, (c * gaussianPairDifference (z.1 j)) • z.2
        ∂(fullMultiscaleNoiseMeasure m).prod
          (uniformUnitSphere d hd : Measure (Point d))) =
          (∫ ξ : Fin (m + 1) → ℝ × ℝ,
              c * gaussianPairDifference (ξ j)
                ∂fullMultiscaleNoiseMeasure m) •
            ∫ u : Point d, u
              ∂(uniformUnitSphere d hd : Measure (Point d)) := by
        exact integral_prod_smul
          (fun ξ : Fin (m + 1) → ℝ × ℝ ↦
            c * gaussianPairDifference (ξ j))
          (fun u : Point d ↦ u)
      _ = 0 := by rw [hscalar, zero_smul]
  · intro j _hj
    let c : ℝ := generalMultiscaleWeight j *
      ((d : ℝ) / (2 * h * generalDyadicRadius j))
    have hscalar : Integrable
        (fun ξ : Fin (m + 1) → ℝ × ℝ ↦
          c * gaussianPairDifference (ξ j))
        (fullMultiscaleNoiseMeasure m) := by
      exact (gaussianPairDifference_eval_integrable j).const_mul c
    have hu : Integrable (fun u : Point d ↦ u)
        (uniformUnitSphere d hd : Measure (Point d)) :=
      continuous_integrable_uniformUnitSphere hd (fun u : Point d ↦ u) continuous_id
    exact hscalar.smul_prod hu

theorem fullMultiscaleSphericalSignal_sample_integrable
    {d : ℕ} (hd : 0 < d) (f : Point d → ℝ) (hf : Continuous f)
    (m : ℕ) (x : Point d) (h : ℝ) :
    Integrable (fun z : (Fin (m + 1) → ℝ × ℝ) × Point d ↦
      fullMultiscaleSphericalSignal d f m x h z.2)
      (fullMultiscaleSampleMeasure d m hd) := by
  have hsphere : Integrable (fullMultiscaleSphericalSignal d f m x h)
      (uniformUnitSphere d hd : Measure (Point d)) := by
    apply continuous_integrable_uniformUnitSphere hd
    unfold fullMultiscaleSphericalSignal centralDifferenceSignal
    fun_prop
  exact hsphere.comp_snd (fullMultiscaleNoiseMeasure m)

theorem fullMultiscaleSphericalEstimator_integrable
    {d : ℕ} (hd : 0 < d) (f : Point d → ℝ) (hf : Continuous f)
    (m : ℕ) (x : Point d) (h : ℝ) :
    Integrable (fullMultiscaleSphericalEstimator d f m x h)
      (fullMultiscaleSampleMeasure d m hd) := by
  exact (fullMultiscaleSphericalSignal_sample_integrable hd f hf m x h).add
    (fullMultiscaleSphericalNoise_integrable d m hd h)

theorem integral_fullMultiscaleSphericalEstimator_eq_ballField
    {d : ℕ} (hd : 0 < d) (f : Point d → ℝ) (hf : ContDiff ℝ 1 f)
    (m : ℕ) (x : Point d) {h : ℝ} (hh : 0 < h) :
    (∫ z, fullMultiscaleSphericalEstimator d f m x h z
      ∂fullMultiscaleSampleMeasure d m hd) =
        fullMultiscaleBallField d (∇ f) m x h := by
  unfold fullMultiscaleSphericalEstimator
  rw [integral_add
    (fullMultiscaleSphericalSignal_sample_integrable hd f hf.continuous m x h)
    (fullMultiscaleSphericalNoise_integrable d m hd h)]
  have hsignal :
      (∫ z : (Fin (m + 1) → ℝ × ℝ) × Point d,
        fullMultiscaleSphericalSignal d f m x h z.2
          ∂fullMultiscaleSampleMeasure d m hd) =
        ∫ u, fullMultiscaleSphericalSignal d f m x h u
          ∂(uniformUnitSphere d hd : Measure (Point d)) := by
    unfold fullMultiscaleSampleMeasure
    rw [integral_fun_snd]
    simp
  rw [hsignal,
    integral_fullMultiscaleSphericalSignal_eq_ballField hd f hf m x hh,
    integral_fullMultiscaleSphericalNoise_eq_zero, add_zero]

def fullMultiscaleNoiseSqEnvelope
    (o : SmoothnessOrder) (d : ℕ) (h : ℝ)
    (ξ : Fin ((o.k - 1) + 1) → ℝ × ℝ) : ℝ :=
  (((o.k - 1) + 1 : ℕ) : ℝ) *
    ∑ j : Fin ((o.k - 1) + 1),
      (generalMultiscaleWeight j *
        ((d : ℝ) / (2 * h * generalDyadicRadius j)) *
          gaussianPairDifference (ξ j)) ^ 2

theorem fullMultiscaleNoiseSqEnvelope_integrable
    (o : SmoothnessOrder) (d : ℕ) (h : ℝ) :
    Integrable (fullMultiscaleNoiseSqEnvelope o d h)
      (fullMultiscaleNoiseMeasure (o.k - 1)) := by
  unfold fullMultiscaleNoiseSqEnvelope fullMultiscaleNoiseMeasure
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro j _hj
  convert (gaussianPairDifference_eval_sq_integrable j).const_mul
    ((generalMultiscaleWeight j *
      ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2) using 1
  funext ξ
  ring

theorem integral_fullMultiscaleNoiseSqEnvelope
    (o : SmoothnessOrder) (d : ℕ) {h : ℝ} (hh : 0 < h) :
    (∫ ξ, fullMultiscaleNoiseSqEnvelope o d h ξ
      ∂fullMultiscaleNoiseMeasure (o.k - 1)) =
        generalMultiscaleNoiseConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
  unfold fullMultiscaleNoiseSqEnvelope fullMultiscaleNoiseMeasure
  rw [integral_const_mul, integral_finsetSum]
  · rw [Finset.mul_sum]
    unfold generalMultiscaleNoiseConstant
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show (fun ξ : Fin ((o.k - 1) + 1) → ℝ × ℝ ↦
        (generalMultiscaleWeight j *
          ((d : ℝ) / (2 * h * generalDyadicRadius j)) *
            gaussianPairDifference (ξ j)) ^ 2) =
        fun ξ ↦
          (generalMultiscaleWeight j *
            ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2 *
              gaussianPairDifference (ξ j) ^ 2 by
          funext ξ
          ring,
      integral_const_mul,
      integral_gaussianPairDifference_eval_sq]
    field_simp [hh.ne', (generalDyadicRadius_pos j).ne']
  · intro j _hj
    convert (gaussianPairDifference_eval_sq_integrable j).const_mul
      ((generalMultiscaleWeight j *
        ((d : ℝ) / (2 * h * generalDyadicRadius j))) ^ 2) using 1
    funext ξ
    ring

theorem fullMultiscaleSphericalNoise_sq_sample_integrable
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d) {h : ℝ} (hh : 0 < h) :
    Integrable (fun z ↦
      ‖fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
  have henv : Integrable
      (fun z : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d ↦
        fullMultiscaleNoiseSqEnvelope o d h z.1)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    exact (fullMultiscaleNoiseSqEnvelope_integrable o d h).comp_fst
      (uniformUnitSphere d hd : Measure (Point d))
  have hmeas : AEStronglyMeasurable (fun z ↦
      ‖fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    apply Continuous.aestronglyMeasurable
    unfold fullMultiscaleSphericalNoise gaussianPairDifference
    fun_prop
  apply henv.mono' hmeas
  have hp : MeasurableSet
      {z : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d | ‖z.2‖ = 1} := by
    exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
  have huProd : ∀ᵐ z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd,
      ‖z.2‖ = 1 := by
    unfold fullMultiscaleSampleMeasure
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards with _ξ
    exact uniformUnitSphere_norm_eq_one hd
  filter_upwards [huProd] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_fullMultiscaleSphericalNoise_sq_le
    d (o.k - 1) hh.ne' z.1 z.2 hz

theorem integral_norm_fullMultiscaleSphericalNoise_sq_sample_le
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d) {h : ℝ} (hh : 0 < h) :
    (∫ z, ‖fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2‖ ^ 2
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) ≤
        generalMultiscaleNoiseConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
  let env : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d → ℝ :=
    fun z ↦ fullMultiscaleNoiseSqEnvelope o d h z.1
  have hnoise := fullMultiscaleSphericalNoise_sq_sample_integrable
    (o := o) hd hh
  have henv : Integrable env
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    exact (fullMultiscaleNoiseSqEnvelope_integrable o d h).comp_fst
      (uniformUnitSphere d hd : Measure (Point d))
  have hpoint : ∀ᵐ z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd,
      ‖fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2‖ ^ 2 ≤ env z := by
    have hp : MeasurableSet
        {z : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d | ‖z.2‖ = 1} := by
      exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
    have huProd : ∀ᵐ z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd,
        ‖z.2‖ = 1 := by
      unfold fullMultiscaleSampleMeasure
      rw [Measure.ae_prod_iff_ae_ae hp]
      filter_upwards with _ξ
      exact uniformUnitSphere_norm_eq_one hd
    filter_upwards [huProd] with z hz
    exact
      norm_fullMultiscaleSphericalNoise_sq_le
        d (o.k - 1) hh.ne' z.1 z.2 hz
  calc
    (∫ z, ‖fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2‖ ^ 2
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) ≤
        ∫ z, env z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd :=
      integral_mono_ae hnoise henv hpoint
    _ = ∫ ξ, fullMultiscaleNoiseSqEnvelope o d h ξ
          ∂fullMultiscaleNoiseMeasure (o.k - 1) := by
      unfold env fullMultiscaleSampleMeasure
      rw [integral_fun_fst]
      simp
    _ = generalMultiscaleNoiseConstant o * (d : ℝ) ^ 2 / h ^ 2 :=
      integral_fullMultiscaleNoiseSqEnvelope o d hh

def generalMultiscaleMomentConstant (o : SmoothnessOrder) : ℝ :=
  162 * generalMultiscaleSignalWeightSum o ^ 2 +
    2 * generalMultiscaleNoiseConstant o

theorem generalMultiscaleMomentConstant_nonneg (o : SmoothnessOrder) :
    0 ≤ generalMultiscaleMomentConstant o := by
  unfold generalMultiscaleMomentConstant
  exact add_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by norm_num) (generalMultiscaleNoiseConstant_nonneg o))

theorem NormalizedObjective.integral_norm_fullMultiscaleSphericalEstimator_sq_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1) :
    (∫ z, ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) ≤
        generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
  let signal : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d → Point d :=
    fun z ↦ fullMultiscaleSphericalSignal d F.f (o.k - 1) x h z.2
  let noise : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d → Point d :=
    fun z ↦ fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2
  let A : ℝ := 9 * (d : ℝ) * generalMultiscaleSignalWeightSum o
  let env : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d → ℝ :=
    fun z ↦ 2 * A ^ 2 + 2 * ‖noise z‖ ^ 2
  have hnoiseSq : Integrable (fun z ↦ ‖noise z‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    simpa only [noise] using
      fullMultiscaleSphericalNoise_sq_sample_integrable (o := o) hd hh
  have henv : Integrable env
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    exact (integrable_const (2 * A ^ 2)).add (hnoiseSq.const_mul 2)
  have hestMeas : AEStronglyMeasurable
      (fun z ↦ ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    apply Continuous.aestronglyMeasurable
    unfold fullMultiscaleSphericalEstimator fullMultiscaleSphericalSignal
      fullMultiscaleSphericalNoise centralDifferenceSignal gaussianPairDifference
    have hfc : Continuous F.f := F.smooth.continuous
    fun_prop
  have hp : MeasurableSet
      {z : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d | ‖z.2‖ = 1} := by
    exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
  have huProd : ∀ᵐ z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd,
      ‖z.2‖ = 1 := by
    unfold fullMultiscaleSampleMeasure
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards with _ξ
    exact uniformUnitSphere_norm_eq_one hd
  have hpoint : ∀ᵐ z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd,
      ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2 ≤
        env z := by
    filter_upwards [huProd] with z hz
    have hs : ‖signal z‖ ≤ A := by
      exact F.norm_fullMultiscaleSphericalSignal_le x hh hh1 z.2 hz hx
    have hnorm : ‖signal z + noise z‖ ≤ ‖signal z‖ + ‖noise z‖ :=
      norm_add_le _ _
    have hsq : ‖signal z + noise z‖ ^ 2 ≤
        (‖signal z‖ + ‖noise z‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    change ‖signal z + noise z‖ ^ 2 ≤ 2 * A ^ 2 + 2 * ‖noise z‖ ^ 2
    calc
      ‖signal z + noise z‖ ^ 2 ≤
          (‖signal z‖ + ‖noise z‖) ^ 2 := hsq
      _ ≤ 2 * ‖signal z‖ ^ 2 + 2 * ‖noise z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖signal z‖ - ‖noise z‖)]
      _ ≤ 2 * A ^ 2 + 2 * ‖noise z‖ ^ 2 := by
        gcongr
  have hestInt : Integrable
      (fun z ↦ ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    apply henv.mono' hestMeas
    filter_upwards [hpoint] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  have hnoiseMoment : (∫ z, ‖noise z‖ ^ 2
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) ≤
      generalMultiscaleNoiseConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
    simpa only [noise] using
      integral_norm_fullMultiscaleSphericalNoise_sq_sample_le (o := o) hd hh
  have henvIntegral : (∫ z, env z
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) =
      2 * A ^ 2 + 2 * (∫ z, ‖noise z‖ ^ 2
        ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    dsimp only [env]
    rw [integral_add (integrable_const (2 * A ^ 2)) (hnoiseSq.const_mul 2)]
    have hn : (∫ z, 2 * ‖noise z‖ ^ 2
        ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) =
        2 * (∫ z, ‖noise z‖ ^ 2
          ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
      exact integral_const_mul (μ := fullMultiscaleSampleMeasure d (o.k - 1) hd)
        (2 : ℝ) (fun z ↦ ‖noise z‖ ^ 2)
    rw [hn]
    simp
  have hhSq : h ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have hdScale : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 / h ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hh)]
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sub_nonneg.mpr hhSq)]
  calc
    (∫ z, ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) ≤
        ∫ z, env z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd :=
      integral_mono_ae hestInt henv hpoint
    _ = 2 * A ^ 2 + 2 * (∫ z, ‖noise z‖ ^ 2
        ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) := henvIntegral
    _ ≤ 2 * A ^ 2 + 2 *
        (generalMultiscaleNoiseConstant o * (d : ℝ) ^ 2 / h ^ 2) := by
      gcongr
    _ = 162 * generalMultiscaleSignalWeightSum o ^ 2 * (d : ℝ) ^ 2 +
        2 * generalMultiscaleNoiseConstant o * ((d : ℝ) ^ 2 / h ^ 2) := by
      dsimp only [A]
      ring
    _ ≤ 162 * generalMultiscaleSignalWeightSum o ^ 2 *
          ((d : ℝ) ^ 2 / h ^ 2) +
        2 * generalMultiscaleNoiseConstant o * ((d : ℝ) ^ 2 / h ^ 2) := by
      gcongr
    _ = generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
      unfold generalMultiscaleMomentConstant
      ring

theorem NormalizedObjective.norm_integral_fullMultiscaleSphericalEstimator_sub_gradient_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1) :
    ‖(∫ z, fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) - ∇ F.f x‖ ≤
        generalMultiscaleBiasConstant o * h ^ (o.beta - 1) := by
  rw [integral_fullMultiscaleSphericalEstimator_eq_ballField hd F.f
    (F.smooth.of_le (by
      norm_cast
      exact le_trans (by omega : 1 ≤ 2) o.two_le_k))
    (o.k - 1) x hh]
  exact F.norm_fullMultiscaleBallField_sub_gradient_le x hh hh1 hx

theorem NormalizedObjective.norm_fullMultiscaleSphericalEstimator_sq_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (z : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d)
    (hz : ‖z.2‖ = 1) (hx : ‖x‖ ≤ 1) :
    ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2 ≤
      2 * (9 * (d : ℝ) * generalMultiscaleSignalWeightSum o) ^ 2 +
        2 * ‖fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2‖ ^ 2 := by
  let signal : Point d :=
    fullMultiscaleSphericalSignal d F.f (o.k - 1) x h z.2
  let noise : Point d :=
    fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2
  let A : ℝ := 9 * (d : ℝ) * generalMultiscaleSignalWeightSum o
  have hs : ‖signal‖ ≤ A :=
    F.norm_fullMultiscaleSphericalSignal_le x hh hh1 z.2 hz hx
  have hnorm : ‖signal + noise‖ ≤ ‖signal‖ + ‖noise‖ := norm_add_le _ _
  have hsq : ‖signal + noise‖ ^ 2 ≤ (‖signal‖ + ‖noise‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
  change ‖signal + noise‖ ^ 2 ≤ 2 * A ^ 2 + 2 * ‖noise‖ ^ 2
  calc
    ‖signal + noise‖ ^ 2 ≤ (‖signal‖ + ‖noise‖) ^ 2 := hsq
    _ ≤ 2 * ‖signal‖ ^ 2 + 2 * ‖noise‖ ^ 2 := by
      nlinarith [sq_nonneg (‖signal‖ - ‖noise‖)]
    _ ≤ 2 * A ^ 2 + 2 * ‖noise‖ ^ 2 := by gcongr

theorem NormalizedObjective.fullMultiscaleSphericalEstimator_sq_integrable
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1) :
    Integrable (fun z ↦
      ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
  let noise : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d → Point d :=
    fun z ↦ fullMultiscaleSphericalNoise d (o.k - 1) h z.1 z.2
  let A : ℝ := 9 * (d : ℝ) * generalMultiscaleSignalWeightSum o
  let env : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d → ℝ :=
    fun z ↦ 2 * A ^ 2 + 2 * ‖noise z‖ ^ 2
  have hnoiseSq : Integrable (fun z ↦ ‖noise z‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    simpa only [noise] using
      fullMultiscaleSphericalNoise_sq_sample_integrable (o := o) hd hh
  have henv : Integrable env
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) :=
    (integrable_const (2 * A ^ 2)).add (hnoiseSq.const_mul 2)
  have hmeas : AEStronglyMeasurable
      (fun z ↦ ‖fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    apply Continuous.aestronglyMeasurable
    unfold fullMultiscaleSphericalEstimator fullMultiscaleSphericalSignal
      fullMultiscaleSphericalNoise centralDifferenceSignal gaussianPairDifference
    have hfc : Continuous F.f := F.smooth.continuous
    fun_prop
  apply henv.mono' hmeas
  have hp : MeasurableSet
      {z : (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d | ‖z.2‖ = 1} := by
    exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
  have huProd : ∀ᵐ z ∂fullMultiscaleSampleMeasure d (o.k - 1) hd,
      ‖z.2‖ = 1 := by
    unfold fullMultiscaleSampleMeasure
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards with _ξ
    exact uniformUnitSphere_norm_eq_one hd
  filter_upwards [huProd] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact F.norm_fullMultiscaleSphericalEstimator_sq_le x hh hh1 z hz hx

end

end NoisyZO
