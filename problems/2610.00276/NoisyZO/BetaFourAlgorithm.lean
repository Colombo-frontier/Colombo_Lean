import NoisyZO.BetaFourStateLaw
import NoisyZO.BetaFourUpper

/-!
# Recursive-law weighted output bound

The concrete recursive state-law recurrence is now fed directly into the
weighted SGD telescope.  The returned quantity is the weighted average of
the expected iterate gaps; a pathwise Jensen construction of an explicit
trajectory output can use this theorem verbatim.
-/

open MeasureTheory
open scoped BigOperators Gradient

namespace NoisyZO

noncomputable section

/-- Weighted average of expected gaps for the recursive iterate laws. -/
def betaFourWeightedLawGap
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (n : ℕ) : ℝ :=
  2 / ((n : ℝ) * (n + 1)) *
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) * betaFourLawGap F hd xnext k

/-- The recursively generated four-query laws obey the exact
`B² + 4M/(n+1)` weighted-gap guarantee. -/
theorem NormalizedObjective.betaFourStateLaw_weighted_gap_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (n : ℕ) (hn : 0 < n)
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
    (hh : 0 < h) (hh1 : h ≤ 1) :
    betaFourWeightedLawGap F hd xnext n ≤
      (h ^ 3 / 12) ^ 2 +
        4 * (229 * d ^ 2 / h ^ 2) / (n + 1) := by
  let R : ℕ → ℝ := fun t ↦ betaFourLawDistance F hd xnext (t - 1)
  let Δ : ℕ → ℝ := fun t ↦ betaFourLawGap F hd xnext (t - 1)
  have hM : 0 ≤ 229 * (d : ℝ) ^ 2 / h ^ 2 := by positivity
  have hR : ∀ t, 0 ≤ R t := by
    intro t
    dsimp only [R, betaFourLawDistance]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hstep : ∀ k < n,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) * Δ (k + 1) +
          2 * (4 / (k + 2 : ℝ)) * (h ^ 3 / 12) ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 * (229 * d ^ 2 / h ^ 2) := by
    intro k _hk
    have hrec := F.betaFourStateLaw_recurrence hbeta hd xnext
      hnextContinuous hnextBall hprojection hh hh1 k
    have hkidx : k + 2 - 1 = k + 1 := by omega
    simpa only [R, Δ, hkidx, Nat.add_sub_cancel] using hrec
  apply biased_sgd_final_bound_of_expected_steps n hn R Δ
    (h ^ 3 / 12) (229 * d ^ 2 / h ^ 2)
    (betaFourWeightedLawGap F hd xnext n) hM hR hstep
  dsimp only [betaFourWeightedLawGap, Δ]
  rfl

/-- At the balanced bandwidth, the recursive four-query laws attain the
explicit `β = 4` rate without assuming the scalar recurrence separately. -/
theorem NormalizedObjective.betaFourStateLaw_balanced_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (n : ℕ) (hn : 0 < n) (hbudget : d ^ 2 ≤ n + 1)
    (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (hnextContinuous : ∀ t, Continuous (fun p : Point d × FourQuerySample d ↦
      xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    (hprojection : ∀ t x z,
      ‖xnext t x z - F.minimizer‖ ≤
        ‖(x - (4 / (t + 2 : ℝ)) •
          betaFourSphericalEstimator d F.f x (betaFourBandwidth d n) z.1
            z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) - F.minimizer‖) :
    betaFourWeightedLawGap F hd xnext n ≤
      (131905 / 144 : ℝ) *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by
  let ratio : ℝ := (d : ℝ) ^ 2 / (n + 1 : ℝ)
  have hratio : 0 < ratio := by dsimp [ratio]; positivity
  have hratioOne : ratio ≤ 1 := by
    have hbudgetR : (d : ℝ) ^ 2 ≤ n + 1 := by exact_mod_cast hbudget
    dsimp only [ratio]
    exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).2 hbudgetR
  have hh : 0 < betaFourBandwidth d n := by
    dsimp only [betaFourBandwidth]
    positivity
  have hh1 : betaFourBandwidth d n ≤ 1 := by
    dsimp only [betaFourBandwidth]
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (le_of_lt hratio) hratioOne
        (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hmain := F.betaFourStateLaw_weighted_gap_le hbeta hd n hn xnext
    hnextContinuous hnextBall hprojection hh hh1
  calc
    betaFourWeightedLawGap F hd xnext n ≤
        ((betaFourBandwidth d n) ^ 3 / 12) ^ 2 +
          4 * (229 * (d : ℝ) ^ 2 / (betaFourBandwidth d n) ^ 2) /
            (n + 1 : ℝ) := hmain
    _ = ((ratio ^ (1 / 8 : ℝ)) ^ 3 / 12) ^ 2 +
        4 * (229 * ratio / (ratio ^ (1 / 8 : ℝ)) ^ 2) := by
      dsimp [ratio, betaFourBandwidth]
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn1]
    _ = (131905 / 144 : ℝ) * ratio ^ (3 / 4 : ℝ) :=
      betaFour_balanced_tradeoff hratio
    _ = (131905 / 144 : ℝ) *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by rfl

end

end NoisyZO
