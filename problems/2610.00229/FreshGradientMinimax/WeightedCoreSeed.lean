import FreshGradientMinimax.WeightedCoreLinks
import FreshGradientMinimax.CoreSeedBounds

/-! Seed truncations with a common, dimension-uniform derivative certificate. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def weightedCoreSeed {n : ℕ} (w : Euclid n) (u : Euclid (n + 1)) : ℝ :=
  -coreTheta (u 0) - coreThetaMass * ∑ e : Fin n, w e * coreGate (u e.castSucc)

def weightedCoreSeedDerivative {n : ℕ} (w : Euclid n) (u : Euclid (n + 1)) : Euclid (n + 1) →L[ℝ] ℝ :=
  -coreDensity (u 0) • EuclideanSpace.proj (𝕜 := ℝ) 0 - coreThetaMass •
    ∑ e : Fin n, (w e * coreGateDeriv (u e.castSucc)) • EuclideanSpace.proj (𝕜 := ℝ) e.castSucc

def weightedCoreSeedGradient {n : ℕ} (w : Euclid n) (u : Euclid (n + 1)) : Euclid (n + 1) :=
  -coreDensity (u 0) • EuclideanSpace.single 0 1 - coreThetaMass •
    ∑ e : Fin n, (w e * coreGateDeriv (u e.castSucc)) • EuclideanSpace.single e.castSucc 1

theorem weightedCoreSeed_hasFDerivAt {n : ℕ} (w : Euclid n) (u : Euclid (n + 1)) :
    HasFDerivAt (weightedCoreSeed w) (weightedCoreSeedDerivative w u) u := by
  have hseed := ((coreTheta_hasDerivAt (u 0)).comp_hasFDerivAt u
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).hasFDerivAt).neg
  have hsum : HasFDerivAt (fun v : Euclid (n + 1) => ∑ e : Fin n, w e * coreGate (v e.castSucc))
      (∑ e : Fin n, (w e * coreGateDeriv (u e.castSucc)) • EuclideanSpace.proj (𝕜 := ℝ) e.castSucc) u := by
    apply HasFDerivAt.sum
    intro e _
    simpa only [smul_smul] using ((coreGate_hasDerivAt (u e.castSucc)).comp_hasFDerivAt u
      (EuclideanSpace.proj (𝕜 := ℝ) e.castSucc).hasFDerivAt).const_mul (w e)
  convert hseed.sub (hsum.const_mul coreThetaMass) using 1
  simp only [weightedCoreSeedDerivative, neg_smul]

theorem weightedCoreSeedDerivative_eq_inner {n : ℕ} (w : Euclid n) (u : Euclid (n + 1)) :
    weightedCoreSeedDerivative w u = innerSL ℝ (weightedCoreSeedGradient w u) := by
  ext v
  simp [weightedCoreSeedDerivative, weightedCoreSeedGradient, innerSL_apply, inner_sub_left,
    sum_inner, real_inner_smul_left, EuclideanSpace.inner_single_left, EuclideanSpace.proj]

theorem weightedCoreSeed_gradient {n : ℕ} (w : Euclid n) (u : Euclid (n + 1)) :
    gradient (weightedCoreSeed w) u = weightedCoreSeedGradient w u := by
  have hd := weightedCoreSeed_hasFDerivAt w u
  rw [weightedCoreSeedDerivative_eq_inner] at hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem weightedCoreSeedGradient_decomposition {n : ℕ} (w : Euclid n) (u : Euclid (n + 1)) :
    weightedCoreSeedGradient w u = -coreDensity (u 0) • EuclideanSpace.single 0 1 - coreThetaMass •
      pathPadLeft n (coordinateMultiplier (fun e => w e) (adjacentVector (fun a _ => coreGateDeriv a) u)) := by
  unfold weightedCoreSeedGradient
  rw [weighted_adjacent_sum_left w (fun a _ => coreGateDeriv a) u]

theorem weightedCoreSeedGradient_norm {n : ℕ} (w : Euclid n) (hw : ∀ e, |w e| ≤ 1)
    (u : Euclid (n + 1)) : ‖weightedCoreSeedGradient w u‖ ≤ 49 * Real.sqrt (n + 1 : ℝ) := by
  have hm0 : 0 ≤ coreThetaMass := (coreTheta_pos 0).le.trans (coreTheta_le_mass 0)
  have hv := euclid_norm_le_of_coordinate_bound (adjacentVector (fun a _ => coreGateDeriv a) u)
    (by norm_num : (0 : ℝ) ≤ 16) (fun e => coreGateDeriv_bound (u e.castSucc))
  have hwv := coordinateMultiplier_norm_bound (fun e => w e) (by norm_num : (0 : ℝ) ≤ 1) hw
    (adjacentVector (fun a _ => coreGateDeriv a) u)
  rw [one_mul] at hwv
  have hp := mul_le_mul coreThetaMass_lt_three.le (hwv.trans hv) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 3)
  have hs := Real.sqrt_le_sqrt (show (n : ℝ) ≤ n + 1 by linarith)
  have h1 : (1 : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [weightedCoreSeedGradient_decomposition]
  have h := norm_sub_le (-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))
    (coreThetaMass • pathPadLeft n (coordinateMultiplier (fun e => w e) (adjacentVector (fun a _ => coreGateDeriv a) u)))
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (coreDensity_pos _),
    EuclideanSpace.norm_single, norm_one, mul_one, abs_of_nonneg hm0, pathPadLeft_norm] at h
  nlinarith only [h, hp, hs, h1, coreDensity_le_one (u 0)]

theorem weightedCoreSeedGradient_sub_norm {n : ℕ} (w : Euclid n) (hw : ∀ e, |w e| ≤ 1)
    (u v : Euclid (n + 1)) : ‖weightedCoreSeedGradient w u - weightedCoreSeedGradient w v‖ ≤ 1537 * ‖u - v‖ := by
  have hm0 : 0 ≤ coreThetaMass := (coreTheta_pos 0).le.trans (coreTheta_le_mass 0)
  have hv := initialVector_sub_norm_le (by norm_num : (0 : ℝ) ≤ 512) coreGateDeriv_sub_le u v
  have hwv := coordinateMultiplier_norm_bound (fun e => w e) (by norm_num : (0 : ℝ) ≤ 1) hw
    (adjacentVector (fun a _ => coreGateDeriv a) u - adjacentVector (fun a _ => coreGateDeriv a) v)
  rw [one_mul] at hwv
  have hp := mul_le_mul coreThetaMass_lt_three.le (hwv.trans hv) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 3)
  rw [weightedCoreSeedGradient_decomposition, weightedCoreSeedGradient_decomposition]
  have he : (-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) -
      coreThetaMass • pathPadLeft n (coordinateMultiplier (fun e => w e) (adjacentVector (fun a _ => coreGateDeriv a) u))) -
      (-coreDensity (v 0) • EuclideanSpace.single 0 1 -
      coreThetaMass • pathPadLeft n (coordinateMultiplier (fun e => w e) (adjacentVector (fun a _ => coreGateDeriv a) v))) =
      (-coreDensity (u 0) • EuclideanSpace.single 0 1 - -coreDensity (v 0) • EuclideanSpace.single 0 1) -
      coreThetaMass • pathPadLeft n (coordinateMultiplier (fun e => w e)
        (adjacentVector (fun a _ => coreGateDeriv a) u - adjacentVector (fun a _ => coreGateDeriv a) v)) := by
    rw [map_sub, map_sub, smul_sub]
    abel
  rw [he]
  have h := norm_sub_le
    (-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) - -coreDensity (v 0) • EuclideanSpace.single 0 1)
    (coreThetaMass • pathPadLeft n (coordinateMultiplier (fun e => w e)
      (adjacentVector (fun a _ => coreGateDeriv a) u - adjacentVector (fun a _ => coreGateDeriv a) v)))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm0, pathPadLeft_norm] at h
  nlinarith only [h, hp, coreChain_seed_sub_norm u v]

theorem weightedCoreSeed_full {n : ℕ} (u : Euclid (n + 1)) :
    weightedCoreSeed ((WithLp.equiv 2 _).symm (fun _ : Fin n => (1 : ℝ))) u = coreSeed u := by
  simp [weightedCoreSeed, coreSeed, squareLinkSeed]

end FreshGradientMinimax
