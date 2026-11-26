import FreshGradientMinimax.CoreChainNorm
import FreshGradientMinimax.CoreScalarLipschitz
import FreshGradientMinimax.SparsePairNorm

/-! Dimension-independent smoothness of the actual chain. The Hessian is the
Fréchet derivative of its actual Euclidean gradient. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem coreChainGradient_decomposition {n : ℕ} (u : Euclid (n + 1)) :
    coreChainGradient u = -coreDensity (u 0) • EuclideanSpace.single 0 1 +
      (pathPadLeft n (adjacentVector coreLinkTermD1 u) +
        pathPadRight n (adjacentVector coreLinkTermD2 u)) := by
  rw [coreChainGradient, Finset.sum_add_distrib, adjacent_sum_left, adjacent_sum_right]

theorem coreChain_seed_sub_norm {n : ℕ} (u v : Euclid (n + 1)) :
    ‖-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) -
      -coreDensity (v 0) • EuclideanSpace.single 0 1‖ ≤ ‖u - v‖ := by
  rw [← sub_smul, norm_smul, EuclideanSpace.norm_single]
  simp only [Real.norm_eq_abs, abs_one, mul_one, neg_sub_neg]
  have h := coreDensity_sub_le (v 0) (u 0)
  rw [abs_sub_comm (v 0) (u 0)] at h
  exact h.trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (u - v) 0)

theorem coreChainGradient_sub_norm {n : ℕ} (u v : Euclid (n + 1)) :
    ‖coreChainGradient u - coreChainGradient v‖ ≤ 5101 * ‖u - v‖ := by
  have h1 := adjacentVector_sub_norm_le
    (by norm_num : (0 : ℝ) ≤ 3072) (by norm_num : (0 : ℝ) ≤ 32)
    (by norm_num : (0 : ℝ) ≤ 5000) (by norm_num) coreLinkTermD1_sub_le u v
  have h2 := adjacentVector_sub_norm_le
    (by norm_num : (0 : ℝ) ≤ 32) (by norm_num : (0 : ℝ) ≤ 6)
    (by norm_num : (0 : ℝ) ≤ 100) (by norm_num) coreLinkTermD2_sub_le u v
  rw [coreChainGradient_decomposition, coreChainGradient_decomposition]
  have he : (-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) +
      (pathPadLeft n (adjacentVector coreLinkTermD1 u) + pathPadRight n (adjacentVector coreLinkTermD2 u))) -
      (-coreDensity (v 0) • EuclideanSpace.single 0 1 +
      (pathPadLeft n (adjacentVector coreLinkTermD1 v) + pathPadRight n (adjacentVector coreLinkTermD2 v))) =
      (-coreDensity (u 0) • EuclideanSpace.single 0 1 - -coreDensity (v 0) • EuclideanSpace.single 0 1) +
      (pathPadLeft n (adjacentVector coreLinkTermD1 u - adjacentVector coreLinkTermD1 v) +
        pathPadRight n (adjacentVector coreLinkTermD2 u - adjacentVector coreLinkTermD2 v)) := by
    rw [map_sub, map_sub]; abel
  rw [he]
  have h := norm_add_le
    (-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) -
      -coreDensity (v 0) • EuclideanSpace.single 0 1)
    (pathPadLeft n (adjacentVector coreLinkTermD1 u - adjacentVector coreLinkTermD1 v) +
      pathPadRight n (adjacentVector coreLinkTermD2 u - adjacentVector coreLinkTermD2 v))
  have hh := norm_add_le
    (pathPadLeft n (adjacentVector coreLinkTermD1 u - adjacentVector coreLinkTermD1 v))
    (pathPadRight n (adjacentVector coreLinkTermD2 u - adjacentVector coreLinkTermD2 v))
  rw [pathPadLeft_norm, pathPadRight_norm] at hh
  linarith only [h, hh, h1, h2, coreChain_seed_sub_norm u v]

theorem coreChain_gradient_lipschitz (n : ℕ) : LipschitzWith 5101 (gradient (@coreChain n)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro u v
  simpa only [coreChain_gradient, NNReal.coe_ofNat] using coreChainGradient_sub_norm u v

theorem coreChain_contDiff {n : ℕ} {m : ℕ∞} : ContDiff ℝ m (@coreChain n) := by
  have hp (i : Fin (n + 1)) : ContDiff ℝ m (fun u : Euclid (n + 1) => u i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  apply ((coreTheta_contDiff.comp (hp 0)).neg).add
  apply ContDiff.sum
  intro e _
  exact ((coreGate_contDiff.comp (hp e.castSucc).neg).mul
    (coreTheta_contDiff.comp (hp e.succ).neg)).sub
    ((coreGate_contDiff.comp (hp e.castSucc)).mul (coreTheta_contDiff.comp (hp e.succ)))

theorem euclid_gradient_contDiff {n : ℕ} {f : Euclid n → ℝ} {m : ℕ∞}
    (hf : ContDiff ℝ (m + 1) f) : ContDiff ℝ m (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Euclid n)).symm.contDiff.comp
    (hf.fderiv_right (by simp))

theorem coreChain_gradient_contDiff {n : ℕ} {m : ℕ∞} :
    ContDiff ℝ m (gradient (@coreChain n)) :=
  euclid_gradient_contDiff (coreChain_contDiff (m := m + 1))

theorem coreChain_hessian_bound {n : ℕ} (u : Euclid (n + 1)) :
    ‖fderiv ℝ (gradient (@coreChain n)) u‖ ≤ 10 ^ 6 := by
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := u) (coreChain_gradient_lipschitz n)
  norm_num only [NNReal.coe_ofNat] at h
  linarith only [h]

end FreshGradientMinimax
