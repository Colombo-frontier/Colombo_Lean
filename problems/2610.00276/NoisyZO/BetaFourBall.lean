import NoisyZO.BallTaylor
import NoisyZO.BetaFour

/-!
# The `β = 4` multiscale ball combination

This file connects the manuscript's explicit weights `-1/3, 4/3` to the
uniform-ball Taylor expansion.  The weights preserve the constant term,
cancel the quadratic term, and leave a dimension-free cubic bias.
-/

open MeasureTheory
open scoped Gradient

namespace NoisyZO

noncomputable section

/-- The two-scale ball-smoothed vector field with the manuscript's explicit
`β = 4` weights. -/
def betaFourBallField
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (x : Point d) (h : ℝ) : F :=
  (-1 / 3 : ℝ) • ballSmoothedField d g x h +
    (4 / 3 : ℝ) • ballSmoothedField d g x (h / 2)

/-- Exact cancellation of the quadratic Taylor coefficient in the two-scale
ball-smoothed field. -/
theorem betaFourBallField_eq_value_add_remainders
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (x : Point d) (h : ℝ)
    (hsmooth : ContDiff ℝ 2 g)
    (houter : Integrable (fun v ↦ g (x + h • v))
      (uniformUnitBall d : Measure (Point d)))
    (hinner : Integrable (fun v ↦ g (x + (h / 2) • v))
      (uniformUnitBall d : Measure (Point d))) :
    betaFourBallField d g x h = g x +
      (-1 / 3 : ℝ) •
        (∫ v, holderTaylorRemainder g 2 x (h • v)
          ∂(uniformUnitBall d : Measure (Point d))) +
      (4 / 3 : ℝ) •
        (∫ v, holderTaylorRemainder g 2 x ((h / 2) • v)
          ∂(uniformUnitBall d : Measure (Point d))) := by
  rw [betaFourBallField,
    ballSmoothedField_eq_secondOrder d g x h hsmooth houter,
    ballSmoothedField_eq_secondOrder d g x (h / 2) hsmooth hinner]
  module

/-- If the second derivative of the vector field is Lipschitz with constant
one, the two-scale averaged field has the manuscript's sharp cubic bias
`|h|³ / 12`. -/
theorem norm_betaFourBallField_sub_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (d : ℕ) (g : Point d → F) (x : Point d) (h : ℝ)
    (hsmooth : ContDiff ℝ 2 g)
    (houter : Integrable (fun v ↦ g (x + h • v))
      (uniformUnitBall d : Measure (Point d)))
    (hinner : Integrable (fun v ↦ g (x + (h / 2) • v))
      (uniformUnitBall d : Measure (Point d)))
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ 2 g u - iteratedFDeriv ℝ 2 g v‖ ≤ ‖u - v‖) :
    ‖betaFourBallField d g x h - g x‖ ≤ |h| ^ 3 / 12 := by
  let rOuter : F :=
    ∫ v, holderTaylorRemainder g 2 x (h • v)
      ∂(uniformUnitBall d : Measure (Point d))
  let rInner : F :=
    ∫ v, holderTaylorRemainder g 2 x ((h / 2) • v)
      ∂(uniformUnitBall d : Measure (Point d))
  have hexact := betaFourBallField_eq_value_add_remainders
    d g x h hsmooth houter hinner
  have hOuterBound : ‖rOuter‖ ≤ |h| ^ 3 / 6 := by
    have hr := norm_ballTaylorRemainder_two_le d g x h hholder
    dsimp only [rOuter]
    exact hr
  have hInnerBound : ‖rInner‖ ≤ |h / 2| ^ 3 / 6 := by
    have hr := norm_ballTaylorRemainder_two_le d g x (h / 2) hholder
    dsimp only [rInner]
    exact hr
  rw [hexact]
  change ‖g x + (-1 / 3 : ℝ) • rOuter + (4 / 3 : ℝ) • rInner - g x‖ ≤ _
  rw [show g x + (-1 / 3 : ℝ) • rOuter + (4 / 3 : ℝ) • rInner - g x =
      (-1 / 3 : ℝ) • rOuter + (4 / 3 : ℝ) • rInner by module]
  calc
    ‖(-1 / 3 : ℝ) • rOuter + (4 / 3 : ℝ) • rInner‖ ≤
        ‖(-1 / 3 : ℝ) • rOuter‖ + ‖(4 / 3 : ℝ) • rInner‖ := norm_add_le _ _
    _ = (1 / 3 : ℝ) * ‖rOuter‖ + (4 / 3 : ℝ) * ‖rInner‖ := by
      simp [norm_smul]
    _ ≤ (1 / 3 : ℝ) * (|h| ^ 3 / 6) +
        (4 / 3 : ℝ) * (|h / 2| ^ 3 / 6) := by
      gcongr
    _ = |h| ^ 3 / 12 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- For a normalized objective with `β = 4`, the concrete two-scale
uniform-ball average of the gradient has dimension-free cubic bias. -/
theorem NormalizedObjective.norm_betaFourBallField_sub_gradient_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (x : Point d) (h : ℝ)
    (hx : ‖x‖ ≤ 1) (hh : |h| ≤ 1) :
    ‖betaFourBallField d (∇ F.f) x h - ∇ F.f x‖ ≤ |h| ^ 3 / 12 := by
  have hk : o.k = 3 := o.k_eq_three_of_beta_eq_four hbeta
  have hk2 : o.k - 1 = 2 := by omega
  have halpha : o.alpha = 1 := o.alpha_eq_one_of_beta_eq_four hbeta
  apply norm_betaFourBallField_sub_le
  · simpa [hk] using F.gradient_contDiff
  · exact F.integrable_gradient_affine_uniformUnitBall x h hx hh
  · apply F.integrable_gradient_affine_uniformUnitBall x (h / 2) hx
    calc
      |h / 2| = |h| / 2 := by rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 1 / 2 := by gcongr
      _ ≤ 1 := by norm_num
  · intro u v
    rw [← hk2]
    simpa [halpha] using F.gradient_higher_holder u v

end

end NoisyZO
