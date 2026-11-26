import NoisyZO.BetaFourAlgorithm
import NoisyZO.UnitBallProjection

/-!
# Explicit projected four-query algorithm

This module instantiates the abstract recursive transition by the radial
projection of one concrete stochastic-gradient step.  Continuity, feasibility,
and the projection inequality are therefore proved properties rather than
premises of the rate theorem.
-/

namespace NoisyZO

noncomputable section

open scoped Gradient

/-- One explicit projected update driven by a uniform direction and four
Gaussian oracle noises. -/
def betaFourProjectedTransition
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) (x : Point d) (z : FourQuerySample d) : Point d :=
  unitBallProjection
    (x - (4 / (t + 2 : ℝ)) •
      betaFourSphericalEstimator d F.f x h z.1
        z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2)

/-- The explicit transition is jointly continuous in the current state and
fresh sample. -/
theorem continuous_betaFourProjectedTransition
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) :
    Continuous (fun p : Point d × FourQuerySample d ↦
      betaFourProjectedTransition F h t p.1 p.2) := by
  unfold betaFourProjectedTransition betaFourSphericalEstimator
    betaFourSphericalSignal betaFourSphericalNoise centralDifferenceSignal
    centralDifferenceNoise
  apply continuous_unitBallProjection.comp
  have hf : Continuous F.f := F.smooth.continuous
  fun_prop

/-- Every explicit transition lands in the feasible unit ball. -/
theorem norm_betaFourProjectedTransition_le_one
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) (x : Point d) (z : FourQuerySample d) :
    ‖betaFourProjectedTransition F h t x z‖ ≤ 1 :=
  norm_unitBallProjection_le_one _

/-- The explicit transition satisfies the projected-step inequality against
the objective minimizer. -/
theorem NormalizedObjective.betaFourProjectedTransition_sub_minimizer_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) (x : Point d) (z : FourQuerySample d) :
    ‖betaFourProjectedTransition F h t x z - F.minimizer‖ ≤
      ‖(x - (4 / (t + 2 : ℝ)) •
        betaFourSphericalEstimator d F.f x h z.1
          z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) - F.minimizer‖ := by
  exact norm_unitBallProjection_sub_le _ _ F.minimizer_mem

/-- With the balanced bandwidth, the fully explicit recursive projected
algorithm attains the `β = 4` upper rate.  The surface-to-ball smoothing
identity used by the estimator mean is proved in `SphereBallDivergence`. -/
theorem NormalizedObjective.betaFourProjectedStateLaw_balanced_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (n : ℕ) (hn : 0 < n) (hbudget : d ^ 2 ≤ n + 1) :
    betaFourWeightedLawGap F hd
        (betaFourProjectedTransition F (betaFourBandwidth d n)) n ≤
      (131905 / 144 : ℝ) *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by
  apply F.betaFourStateLaw_balanced_rate hbeta hd n hn hbudget
    (betaFourProjectedTransition F (betaFourBandwidth d n))
  · exact fun t ↦ continuous_betaFourProjectedTransition F _ t
  · exact fun t x z ↦ norm_betaFourProjectedTransition_le_one F _ t x z
  · exact fun t x z ↦ F.betaFourProjectedTransition_sub_minimizer_le _ t x z

end

end NoisyZO
