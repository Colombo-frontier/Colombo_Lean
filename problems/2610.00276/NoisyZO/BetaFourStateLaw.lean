import NoisyZO.BetaFourLawStep

/-!
# Recursive laws of the four-query projected algorithm

The current iterate law is pushed through a fresh independent
uniform-direction/four-Gaussian sample at every step.  The resulting theorem
turns the measure-level law step into the exact scalar recurrence used by the
SGD telescope.
-/

open MeasureTheory
open scoped Gradient

namespace NoisyZO

noncomputable section

/-- Recursive marginal law of iterates generated from `0` by independent
fresh samples. -/
def betaFourStateLaw {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d) :
    ℕ → Measure (Point d)
  | 0 => Measure.dirac 0
  | t + 1 =>
      ((betaFourStateLaw hd xnext t).prod
        ((uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure)).map
          (fun p ↦ xnext t p.1 p.2)

/-- Every recursively constructed state law is a probability measure. -/
theorem betaFourStateLaw_isProbability {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d) (t : ℕ) :
    IsProbabilityMeasure (betaFourStateLaw hd xnext t) := by
  induction t with
  | zero =>
      simp only [betaFourStateLaw]
      infer_instance
  | succ t ih =>
      let _ : IsProbabilityMeasure (betaFourStateLaw hd xnext t) := ih
      simp only [betaFourStateLaw]
      infer_instance

/-- If every transition projects into the unit ball, every positive-time
state law is supported there.  The initial Dirac law at zero has the same
property. -/
theorem betaFourStateLaw_mem_unitBall
    {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (hnextContinuous : ∀ t, Continuous (fun p : Point d × FourQuerySample d ↦
      xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    (t : ℕ) :
    ∀ᵐ x ∂betaFourStateLaw hd xnext t, ‖x‖ ≤ 1 := by
  cases t with
  | zero =>
      simp [betaFourStateLaw]
  | succ t =>
      have hp : MeasurableSet {x : Point d | ‖x‖ ≤ 1} :=
        measurableSet_Iic.preimage continuous_norm.measurable
      rw [betaFourStateLaw,
        ae_map_iff (hnextContinuous t).measurable.aemeasurable hp]
      exact Filter.Eventually.of_forall fun p ↦ hnextBall t p.1 p.2

/-- Mean squared distance of the recursive state law. -/
def betaFourLawDistance
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (t : ℕ) : ℝ :=
  ∫ x, ‖x - F.minimizer‖ ^ 2 ∂betaFourStateLaw hd xnext t

/-- Expected objective gap of the recursive state law. -/
def betaFourLawGap
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (t : ℕ) : ℝ :=
  ∫ x, F.f x - F.f F.minimizer ∂betaFourStateLaw hd xnext t

set_option maxHeartbeats 800000 in
/-- The recursive marginal laws satisfy the manuscript's expected one-step
recurrence with the concrete estimator constants. -/
theorem NormalizedObjective.betaFourStateLaw_recurrence
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (hnextContinuous : ∀ t, Continuous (fun p : Point d × FourQuerySample d ↦
      xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    {h : ℝ}
    (hprojection : ∀ t x z,
      ‖xnext t x z - F.minimizer‖ ≤
        ‖(x - (4 / (t + 2 : ℝ)) •
          betaFourSphericalEstimator d F.f x h z.1
            z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) - F.minimizer‖)
    (hh : 0 < h) (hh1 : h ≤ 1) (t : ℕ) :
    betaFourLawDistance F hd xnext (t + 1) ≤
      (1 - (4 / (t + 2 : ℝ)) / 2) * betaFourLawDistance F hd xnext t -
        2 * (4 / (t + 2 : ℝ)) * betaFourLawGap F hd xnext t +
        2 * (4 / (t + 2 : ℝ)) * (h ^ 3 / 12) ^ 2 +
        (4 / (t + 2 : ℝ)) ^ 2 * (229 * d ^ 2 / h ^ 2) := by
  let μ : Measure (Point d) := betaFourStateLaw hd xnext t
  let _ : IsProbabilityMeasure μ := betaFourStateLaw_isProbability hd xnext t
  have hstep := F.betaFourGaussian_law_step hbeta hd μ
    (4 / (t + 2 : ℝ)) (by positivity) hh hh1 (xnext t)
    (hnextContinuous t) (hnextBall t) (hprojection t)
    (betaFourStateLaw_mem_unitBall hd xnext hnextContinuous hnextBall t)
  have hmap :
      (∫ x, ‖x - F.minimizer‖ ^ 2
        ∂betaFourStateLaw hd xnext (t + 1)) =
      ∫ p, ‖xnext t p.1 p.2 - F.minimizer‖ ^ 2
        ∂μ.prod ((uniformUnitSphere d hd : Measure (Point d)).prod
          fourNoiseMeasure) := by
    rw [betaFourStateLaw]
    exact integral_map (hnextContinuous t).measurable.aemeasurable (by fun_prop)
  rw [betaFourLawDistance, hmap]
  simpa only [betaFourLawDistance, betaFourLawGap, μ] using hstep

end

end NoisyZO
