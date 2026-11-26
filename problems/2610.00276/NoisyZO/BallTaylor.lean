import NoisyZO.UniformMeasures
import NoisyZO.GradientHolder

/-!
# Taylor expansion under the uniform-ball law

This file integrates the pointwise vector Taylor formula under the concrete
uniform unit-ball probability measure.  Every Taylor coefficient is proved
integrable from its multilinear operator norm, odd degrees vanish by central
symmetry, and the averaged remainder inherits the pointwise Hölder bound.
-/

open MeasureTheory
open scoped BigOperators Gradient

namespace NoisyZO

noncomputable section

/-- The ball-smoothed value of a vector field at scale `r`. -/
def ballSmoothedField
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (x : Point d) (r : ℝ) : F :=
  ∫ v, g (x + r • v) ∂(uniformUnitBall d : Measure (Point d))

/-- One homogeneous Taylor term before averaging over the ball. -/
def ballTaylorTerm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Point d → F) (k : ℕ) (x : Point d) (r : ℝ) (v : Point d) : F :=
  (Nat.factorial k : ℝ)⁻¹ •
    iteratedFDeriv ℝ k g x (fun _ ↦ r • v)

/-- Every fixed Taylor coefficient is integrable under the uniform-ball law.
The proof uses the multilinear operator norm and `‖V‖ ≤ 1` almost surely. -/
theorem integrable_ballTaylorTerm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (k : ℕ) (x : Point d) (r : ℝ) :
    Integrable (ballTaylorTerm g k x r)
      (uniformUnitBall d : Measure (Point d)) := by
  let A := iteratedFDeriv ℝ k g x
  let C : ℝ := |(Nat.factorial k : ℝ)⁻¹| * (‖A‖ * |r| ^ k)
  have hmeas : AEStronglyMeasurable (ballTaylorTerm g k x r)
      (uniformUnitBall d : Measure (Point d)) := by
    apply Continuous.aestronglyMeasurable
    unfold ballTaylorTerm
    fun_prop
  have hbound : ∀ᵐ v ∂(uniformUnitBall d : Measure (Point d)),
      ‖ballTaylorTerm g k x r v‖ ≤ C := by
    filter_upwards [uniformUnitBall_norm_le_one d] with v hv
    have hrv : ‖r • v‖ ≤ |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg r) hv
    have heval := A.le_opNorm (fun _ : Fin k ↦ r • v)
    have heval' : ‖A (fun _ : Fin k ↦ r • v)‖ ≤ ‖A‖ * |r| ^ k := by
      calc
        ‖A (fun _ : Fin k ↦ r • v)‖ ≤
            ‖A‖ * ∏ _i : Fin k, ‖r • v‖ := heval
        _ = ‖A‖ * ‖r • v‖ ^ k := by simp
        _ ≤ ‖A‖ * |r| ^ k := by
          gcongr
    rw [ballTaylorTerm, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left heval' (abs_nonneg _)
  exact (integrable_const C).mono' hmeas hbound

/-- The averaged vector Taylor expansion under the uniform unit-ball law. -/
theorem ballSmoothedField_eq_taylor_sum_add_remainder
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (m : ℕ) (hm : 0 < m)
    (x : Point d) (r : ℝ)
    (hsmooth : ContDiff ℝ m g)
    (hmain : Integrable (fun v ↦ g (x + r • v))
      (uniformUnitBall d : Measure (Point d))) :
    ballSmoothedField d g x r =
      (∑ k ∈ Finset.range (m + 1),
        ∫ v, ballTaylorTerm g k x r v
          ∂(uniformUnitBall d : Measure (Point d))) +
      ∫ v, holderTaylorRemainder g m x (r • v)
        ∂(uniformUnitBall d : Measure (Point d)) := by
  let μ : Measure (Point d) := uniformUnitBall d
  let poly : Point d → F := fun v ↦
    ∑ k ∈ Finset.range (m + 1), ballTaylorTerm g k x r v
  let rem : Point d → F := fun v ↦ holderTaylorRemainder g m x (r • v)
  have hpoint : ∀ v, g (x + r • v) = poly v + rem v := by
    intro v
    have htaylor := vector_taylor_eq_sum_add_holderRemainder
      g m hm x (r • v) (fun t _ ↦ hsmooth.contDiffAt)
    dsimp only [poly, rem]
    rw [Finset.sum_range_succ]
    simpa only [ballTaylorTerm] using htaylor
  have hpoly : Integrable poly μ := by
    dsimp only [poly, μ]
    apply integrable_finsetSum
    intro k _hk
    exact integrable_ballTaylorTerm d g k x r
  have hremEq : rem = fun v ↦ g (x + r • v) - poly v := by
    funext v
    have hp := hpoint v
    rw [hp]
    abel
  have hrem : Integrable rem μ := by
    rw [hremEq]
    exact hmain.sub hpoly
  rw [ballSmoothedField]
  change (∫ v, g (x + r • v) ∂μ) = _
  calc
    (∫ v, g (x + r • v) ∂μ) = ∫ v, poly v + rem v ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (∫ v, poly v ∂μ) + ∫ v, rem v ∂μ := integral_add hpoly hrem
    _ = (∑ k ∈ Finset.range (m + 1),
          ∫ v, ballTaylorTerm g k x r v ∂μ) +
        ∫ v, rem v ∂μ := by
      rw [show (∫ v, poly v ∂μ) =
          ∑ k ∈ Finset.range (m + 1),
            ∫ v, ballTaylorTerm g k x r v ∂μ by
        dsimp only [poly]
        apply integral_finsetSum
        intro k _hk
        exact integrable_ballTaylorTerm d g k x r]
    _ = (∑ k ∈ Finset.range (m + 1),
          ∫ v, ballTaylorTerm g k x r v
            ∂(uniformUnitBall d : Measure (Point d))) +
        ∫ v, holderTaylorRemainder g m x (r • v)
          ∂(uniformUnitBall d : Measure (Point d)) := by rfl

/-- Odd Taylor terms in the concrete ball-smoothed expansion are zero. -/
theorem integral_ballTaylorTerm_eq_zero_of_odd
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (k : ℕ) (hk : Odd k)
    (x : Point d) (r : ℝ) :
    (∫ v, ballTaylorTerm g k x r v
      ∂(uniformUnitBall d : Measure (Point d))) = 0 := by
  unfold ballTaylorTerm
  rw [integral_smul]
  rw [uniformUnitBall_odd_taylor_term_eq_zero d
    (iteratedFDeriv ℝ k g x) hk r, smul_zero]

/-- Radius dependence factors out of each homogeneous Taylor term. -/
theorem ballTaylorTerm_radius_factor
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Point d → F) (k : ℕ) (x : Point d) (r : ℝ) (v : Point d) :
    ballTaylorTerm g k x r v =
      r ^ k • ballTaylorTerm g k x 1 v := by
  unfold ballTaylorTerm
  rw [multilinear_diagonal_smul]
  simp only [one_smul]
  module

theorem integral_ballTaylorTerm_radius_factor
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (k : ℕ) (x : Point d) (r : ℝ) :
    (∫ v, ballTaylorTerm g k x r v
        ∂(uniformUnitBall d : Measure (Point d))) =
      r ^ k • ∫ v, ballTaylorTerm g k x 1 v
        ∂(uniformUnitBall d : Measure (Point d)) := by
  have hfun : ballTaylorTerm g k x r =
      fun v ↦ r ^ k • ballTaylorTerm g k x 1 v := by
    funext v
    exact ballTaylorTerm_radius_factor g k x r v
  rw [hfun, integral_smul]

/-- The radius-independent quadratic coefficient in a second-order
ball-smoothed expansion. -/
def ballSecondCoeff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (x : Point d) : F :=
  ∫ v, ballTaylorTerm g 2 x 1 v
    ∂(uniformUnitBall d : Measure (Point d))

/-- The explicit second-order ball-smoothed expansion: the linear term
vanishes and the quadratic term is homogeneous in `r²`. -/
theorem ballSmoothedField_eq_secondOrder
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (x : Point d) (r : ℝ)
    (hsmooth : ContDiff ℝ 2 g)
    (hmain : Integrable (fun v ↦ g (x + r • v))
      (uniformUnitBall d : Measure (Point d))) :
    ballSmoothedField d g x r =
      g x + r ^ 2 • ballSecondCoeff d g x +
        ∫ v, holderTaylorRemainder g 2 x (r • v)
          ∂(uniformUnitBall d : Measure (Point d)) := by
  have h := ballSmoothedField_eq_taylor_sum_add_remainder
    d g 2 (by norm_num) x r hsmooth hmain
  have hzero :
      (∫ v, ballTaylorTerm g 0 x r v
        ∂(uniformUnitBall d : Measure (Point d))) = g x := by
    simp [ballTaylorTerm]
  have hone :
      (∫ v, ballTaylorTerm g 1 x r v
        ∂(uniformUnitBall d : Measure (Point d))) = 0 :=
    integral_ballTaylorTerm_eq_zero_of_odd d g 1 (by simp) x r
  have htwo :
      (∫ v, ballTaylorTerm g 2 x r v
        ∂(uniformUnitBall d : Measure (Point d))) =
        r ^ 2 • ballSecondCoeff d g x := by
    exact integral_ballTaylorTerm_radius_factor d g 2 x r
  rw [show 2 + 1 = 3 by norm_num, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, hzero, hone, htwo, add_zero] at h
  simpa only [add_assoc] using h

/-- After uniform-ball averaging, the exact expansion contains only even
Taylor degrees. -/
theorem ballSmoothedField_eq_even_taylor_sum_add_remainder
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (m : ℕ) (hm : 0 < m)
    (x : Point d) (r : ℝ)
    (hsmooth : ContDiff ℝ m g)
    (hmain : Integrable (fun v ↦ g (x + r • v))
      (uniformUnitBall d : Measure (Point d))) :
    ballSmoothedField d g x r =
      (∑ k ∈ (Finset.range (m + 1)).filter Even,
        ∫ v, ballTaylorTerm g k x r v
          ∂(uniformUnitBall d : Measure (Point d))) +
      ∫ v, holderTaylorRemainder g m x (r • v)
        ∂(uniformUnitBall d : Measure (Point d)) := by
  classical
  rw [ballSmoothedField_eq_taylor_sum_add_remainder
    d g m hm x r hsmooth hmain]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases heven : Even k
  · simp [heven]
  · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
    rw [integral_ballTaylorTerm_eq_zero_of_odd d g k hodd x r]
    simp [heven]

/-- The concrete averaged Taylor remainder obeys the dimension-free Hölder
operator-norm estimate. -/
theorem norm_ballTaylorRemainder_le
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
  norm_uniformUnitBall_holderTaylorRemainder_smul_le
    d g m x r L α hL hα hholder

/-- Sharp cubic averaged Taylor remainder at `β = 4`. -/
theorem norm_ballTaylorRemainder_two_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (x : Point d) (r : ℝ)
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ 2 g u - iteratedFDeriv ℝ 2 g v‖ ≤ ‖u - v‖) :
    ‖∫ v, holderTaylorRemainder g 2 x (r • v)
        ∂(uniformUnitBall d : Measure (Point d))‖ ≤ |r| ^ 3 / 6 :=
  norm_integral_holderTaylorRemainder_two_smul_le
    (uniformUnitBall d : Measure (Point d)) g x r
    (uniformUnitBall_norm_le_one d) hholder

/-- Exact even-degree uniform-ball expansion for the gradient of a normalized
objective on the estimator's region.  Smoothness and integrability are now
discharged from the fields of `NormalizedObjective`. -/
theorem NormalizedObjective.ballSmoothedGradient_eq_even_taylor
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) (r : ℝ) (hx : ‖x‖ ≤ 1) (hr : |r| ≤ 1) :
    ballSmoothedField d (∇ F.f) x r =
      (∑ k ∈ (Finset.range ((o.k - 1) + 1)).filter Even,
        ∫ v, ballTaylorTerm (∇ F.f) k x r v
          ∂(uniformUnitBall d : Measure (Point d))) +
      ∫ v, holderTaylorRemainder (∇ F.f) (o.k - 1) x (r • v)
        ∂(uniformUnitBall d : Measure (Point d)) := by
  apply ballSmoothedField_eq_even_taylor_sum_add_remainder
  · exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by omega : 1 < 2) o.two_le_k)
  · exact F.gradient_contDiff
  · exact F.integrable_gradient_affine_uniformUnitBall x r hx hr

/-- The averaged gradient-Taylor remainder has the manuscript's
`|r|^(β-1)` order with no dimension-dependent norm conversion. -/
theorem NormalizedObjective.norm_ballSmoothedGradient_remainder_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) (r : ℝ) :
    ‖∫ v, holderTaylorRemainder (∇ F.f) (o.k - 1) x (r • v)
        ∂(uniformUnitBall d : Measure (Point d))‖ ≤
      (Nat.factorial (o.k - 2) : ℝ)⁻¹ * |r| ^ (o.beta - 1) := by
  have hk1 : 1 ≤ o.k := le_trans (by omega) o.two_le_k
  have hfac : (o.k - 1) - 1 = o.k - 2 := by omega
  have hexp : o.alpha + ((o.k - 1 : ℕ) : ℝ) = o.beta - 1 := by
    rw [Nat.cast_sub hk1]
    push_cast
    linarith [o.beta_eq]
  have hpow : |r| ^ o.alpha * |r| ^ (o.k - 1) =
      |r| ^ (o.beta - 1) := by
    by_cases hr0 : r = 0
    · subst r
      simp [o.alpha_pos.ne',
        ne_of_gt (sub_pos.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) o.beta_gt_two))]
    · rw [← Real.rpow_natCast, ← Real.rpow_add (abs_pos.mpr hr0), hexp]
  have h := norm_ballTaylorRemainder_le d (∇ F.f) (o.k - 1) x r 1 o.alpha
    (by norm_num) o.alpha_pos (fun u v ↦ by simpa using F.gradient_higher_holder u v)
  rw [hfac] at h
  calc
    ‖∫ v, holderTaylorRemainder (∇ F.f) (o.k - 1) x (r • v)
        ∂(uniformUnitBall d : Measure (Point d))‖ ≤
        (Nat.factorial (o.k - 2) : ℝ)⁻¹ *
          (1 * |r| ^ o.alpha * |r| ^ (o.k - 1)) := h
    _ = (Nat.factorial (o.k - 2) : ℝ)⁻¹ * |r| ^ (o.beta - 1) := by
      rw [one_mul, hpow]

end

end NoisyZO
