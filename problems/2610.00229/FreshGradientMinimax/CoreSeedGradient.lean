import FreshGradientMinimax.CoreChainSmooth

/-! The actual gradient and smoothness of the seed D_T in (22). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def coreSeed {n : ℕ} (u : Euclid (n + 1)) : ℝ := squareLinkSeed (fun i => u i)

def coreSeedDerivative {n : ℕ} (u : Euclid (n + 1)) : Euclid (n + 1) →L[ℝ] ℝ :=
  -coreDensity (u 0) • EuclideanSpace.proj (𝕜 := ℝ) 0 - coreThetaMass •
    ∑ e : Fin n, coreGateDeriv (u e.castSucc) • EuclideanSpace.proj (𝕜 := ℝ) e.castSucc

def coreSeedGradient {n : ℕ} (u : Euclid (n + 1)) : Euclid (n + 1) :=
  -coreDensity (u 0) • EuclideanSpace.single 0 1 - coreThetaMass •
    ∑ e : Fin n, coreGateDeriv (u e.castSucc) • EuclideanSpace.single e.castSucc 1

theorem coreSeed_hasFDerivAt {n : ℕ} (u : Euclid (n + 1)) :
    HasFDerivAt coreSeed (coreSeedDerivative u) u := by
  have hseed := ((coreTheta_hasDerivAt (u 0)).comp_hasFDerivAt u
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).hasFDerivAt).neg
  have hsum : HasFDerivAt (fun v : Euclid (n + 1) => ∑ e : Fin n, coreGate (v e.castSucc))
      (∑ e : Fin n, coreGateDeriv (u e.castSucc) • EuclideanSpace.proj (𝕜 := ℝ) e.castSucc) u := by
    apply HasFDerivAt.sum
    intro e _
    exact (coreGate_hasDerivAt (u e.castSucc)).comp_hasFDerivAt u
      (EuclideanSpace.proj (𝕜 := ℝ) e.castSucc).hasFDerivAt
  convert hseed.sub (hsum.const_mul coreThetaMass) using 1
  simp only [coreSeedDerivative, neg_smul]

theorem coreSeedDerivative_eq_inner {n : ℕ} (u : Euclid (n + 1)) :
    coreSeedDerivative u = innerSL ℝ (coreSeedGradient u) := by
  ext v
  simp [coreSeedDerivative, coreSeedGradient, innerSL_apply, inner_sub_left, sum_inner,
    real_inner_smul_left, EuclideanSpace.inner_single_left, EuclideanSpace.proj]

theorem coreSeed_gradient {n : ℕ} (u : Euclid (n + 1)) :
    gradient coreSeed u = coreSeedGradient u := by
  have hd := coreSeed_hasFDerivAt u
  rw [coreSeedDerivative_eq_inner] at hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem coreSeedGradient_decomposition {n : ℕ} (u : Euclid (n + 1)) :
    coreSeedGradient u = -coreDensity (u 0) • EuclideanSpace.single 0 1 -
      coreThetaMass • pathPadLeft n (adjacentVector (fun a _ => coreGateDeriv a) u) := by
  unfold coreSeedGradient
  rw [adjacent_sum_left (fun a _ => coreGateDeriv a) u]

theorem coreSeedGradient_apply {n : ℕ} (u : Euclid (n + 1)) (j : Fin (n + 1)) :
    coreSeedGradient u j = (if (0 : Fin (n + 1)) = j then -coreDensity (u 0) else 0) -
      coreThetaMass * ∑ e : Fin n, if e.castSucc = j then coreGateDeriv (u e.castSucc) else 0 := by
  change (EuclideanSpace.proj (𝕜 := ℝ) j) (coreSeedGradient u) = _
  unfold coreSeedGradient
  rw [map_sub, map_smul, map_smul, map_sum]
  simp [EuclideanSpace.proj, EuclideanSpace.single_apply, eq_comm]

theorem coreSeed_contDiff {n : ℕ} {m : ℕ∞} : ContDiff ℝ m (@coreSeed n) := by
  have hp (i : Fin (n + 1)) : ContDiff ℝ m (fun u : Euclid (n + 1) => u i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  apply ((coreTheta_contDiff.comp (hp 0)).neg).sub
  apply contDiff_const.mul
  apply ContDiff.sum
  intro e _
  exact coreGate_contDiff.comp (hp e.castSucc)

theorem coreSeed_gradient_contDiff {n : ℕ} {m : ℕ∞} :
    ContDiff ℝ m (gradient (@coreSeed n)) :=
  euclid_gradient_contDiff (coreSeed_contDiff (m := m + 1))

end FreshGradientMinimax
