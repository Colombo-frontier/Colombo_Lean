import FreshGradientMinimax.RobinBlockMaps
import FreshGradientMinimax.BoundedEnergyRegularity

/-! The original clipped multi-chain Q_delta and its genuine partial gradients. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def robinMultiEnergy (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : ℝ :=
  boundedEnergy δ 1000 (robinBlockEdges n k (clipVector 2 u) y)

def robinMultiSlope (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * (n + 3)) :=
  boundedSlope δ 1000 (robinBlockEdges n k (clipVector 2 u) y)

def robinMultiPullback (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * 2 + 1) :=
  ((robinPrimalMap n k)†) (robinMultiSlope n k δ u y)

def robinMultiGradientU (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * 2 + 1) :=
  weightedClipGradient 2 (robinMultiPullback n k δ u y) u

def robinMultiGradientY (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * (n + 2)) :=
  ((robinDualMap n k)†) (robinMultiSlope n k δ u y)

theorem robinMultiEnergy_hasFDerivAt_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (robinMultiEnergy n k δ u) (innerSL ℝ (robinMultiGradientY n k δ u y)) y :=
  affineBoundedEnergy_hasFDerivAt _ _ hδ (by norm_num) y

theorem robinMultiEnergy_hasFDerivAt_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (fun v => robinMultiEnergy n k δ v y) (innerSL ℝ (robinMultiGradientU n k δ u y)) u := by
  have hd := affineBoundedEnergy_hasFDerivAt (robinPrimalMap n k) (robinDualMap n k y)
    (b := 1000) hδ (by norm_num) (clipVector 2 u)
  have hc := clipped_scalar_hasFDerivAt (by norm_num : (0 : ℝ) < 2) u _ hd
  simpa only [robinMultiEnergy, robinMultiGradientU, robinMultiPullback, robinMultiSlope,
    robinBlockEdges, affineBoundedEnergy, affineBoundedGradient, add_comm] using hc

theorem robinMultiEnergy_gradient_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    gradient (fun v => robinMultiEnergy n k δ v y) u = robinMultiGradientU n k δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (robinMultiEnergy_hasFDerivAt_u n k hδ u y)).gradient

theorem robinMultiEnergy_gradient_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    gradient (robinMultiEnergy n k δ u) y = robinMultiGradientY n k δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (robinMultiEnergy_hasFDerivAt_y n k hδ u y)).gradient

theorem robinMultiEnergy_joint_contDiff (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid (k * (n + 2)) => robinMultiEnergy n k δ z.1 z.2) := by
  apply (boundedEnergy_contDiff hδ (by norm_num : (0 : ℝ) ≤ 1000)).comp
  have hc := (clipVector_contDiff (n := k * 2 + 1) 2).of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  exact ((robinDualMap n k).contDiff.comp contDiff_snd).add
    ((robinPrimalMap n k).contDiff.comp (hc.comp contDiff_fst))

theorem robinMultiEnergy_convex_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    ConvexOn ℝ Set.univ (robinMultiEnergy n k δ u) := affineBoundedEnergy_convex _ _ hδ (by norm_num)

theorem robinMultiPullback_coordinate {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) (i : Fin (k * 2 + 1)) :
    |robinMultiPullback n k δ u y i| ≤ (28 / 3) * 1000 :=
  robinPrimalMap_adjoint_coordinate hn (by norm_num) _
    (fun e => boundedFlatSlope_bound hδ (by norm_num) _) i

theorem robinMultiGradientU_norm {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiGradientU n k δ u y‖ ≤ 14000 * Real.sqrt (k + 1 : ℕ) := by
  have h := robinPrimalMap_adjoint_bounded_norm hn (by norm_num : (0 : ℝ) ≤ 1000)
    (robinMultiSlope n k δ u y) (fun e => boundedFlatSlope_bound hδ (by norm_num) _)
  have hw := weightedClipGradient_norm 2 (robinMultiPullback n k δ u y) u
  have hs := Real.sqrt_le_sqrt (Nat.cast_le.mpr (show k ≤ k + 1 by omega) : (k : ℝ) ≤ (k + 1 : ℕ))
  change ‖robinMultiGradientU n k δ u y‖ ≤ ‖robinMultiPullback n k δ u y‖ at hw
  change ‖robinMultiPullback n k δ u y‖ ≤ _ at h
  nlinarith only [hw, h, hs, Real.sqrt_nonneg (k + 1 : ℕ)]

end FreshGradientMinimax
