import FreshGradientMinimax.CoreSeedGradient

/-! The original seed constants 49 sqrt(T) and 1537 from Lemma C.1. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem coreSeedGradient_coordinate_bound {n : ℕ} (u : Euclid (n + 1)) (j : Fin (n + 1)) :
    |coreSeedGradient u j| ≤ 49 := by
  classical
  have hm0 : 0 ≤ coreThetaMass := (coreTheta_pos 0).le.trans (coreTheta_le_mass 0)
  have hs0 : 0 ≤ ∑ e : Fin n, if e.castSucc = j then coreGateDeriv (u e.castSucc) else 0 := by
    apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact coreGateDeriv_nonneg _
    · rfl
  have hs1 := sum_injective_fiber_le (fun e : Fin n => e.castSucc) (Fin.castSucc_injective n)
    (fun e => coreGateDeriv (u e.castSucc)) j (by norm_num : (0 : ℝ) ≤ 16)
    (fun e => (le_abs_self _).trans (coreGateDeriv_bound _))
  have hp := mul_le_mul coreThetaMass_lt_three.le hs1 hs0 (by norm_num : (0 : ℝ) ≤ 3)
  have hseed : |if (0 : Fin (n + 1)) = j then -coreDensity (u 0) else 0| ≤ 1 := by
    split_ifs
    · rw [abs_neg, abs_of_pos (coreDensity_pos _)]
      exact coreDensity_le_one _
    · norm_num
  rw [coreSeedGradient_apply]
  have h := abs_sub (if (0 : Fin (n + 1)) = j then -coreDensity (u 0) else 0)
    (coreThetaMass * ∑ e : Fin n, if e.castSucc = j then coreGateDeriv (u e.castSucc) else 0)
  rw [abs_of_nonneg (mul_nonneg hm0 hs0)] at h
  linarith only [h, hp, hseed]

theorem coreSeed_gradient_norm {n : ℕ} (u : Euclid (n + 1)) :
    ‖gradient coreSeed u‖ ≤ 49 * Real.sqrt (n + 1 : ℝ) := by
  rw [coreSeed_gradient]
  simpa only [Nat.cast_add, Nat.cast_one] using euclid_norm_le_of_coordinate_bound
    (coreSeedGradient u) (by norm_num : (0 : ℝ) ≤ 49) (coreSeedGradient_coordinate_bound u)

theorem coreSeedGradient_sub_norm {n : ℕ} (u v : Euclid (n + 1)) :
    ‖coreSeedGradient u - coreSeedGradient v‖ ≤ 1537 * ‖u - v‖ := by
  have hm0 : 0 ≤ coreThetaMass := (coreTheta_pos 0).le.trans (coreTheta_le_mass 0)
  have hv := initialVector_sub_norm_le (by norm_num : (0 : ℝ) ≤ 512) coreGateDeriv_sub_le u v
  have hp := mul_le_mul coreThetaMass_lt_three.le hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  rw [coreSeedGradient_decomposition, coreSeedGradient_decomposition]
  have he : (-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) -
      coreThetaMass • pathPadLeft n (adjacentVector (fun a _ => coreGateDeriv a) u)) -
      (-coreDensity (v 0) • EuclideanSpace.single 0 1 -
      coreThetaMass • pathPadLeft n (adjacentVector (fun a _ => coreGateDeriv a) v)) =
      (-coreDensity (u 0) • EuclideanSpace.single 0 1 - -coreDensity (v 0) • EuclideanSpace.single 0 1) -
      coreThetaMass • pathPadLeft n (adjacentVector (fun a _ => coreGateDeriv a) u -
        adjacentVector (fun a _ => coreGateDeriv a) v) := by
    rw [map_sub, smul_sub]; abel
  rw [he]
  have h := norm_sub_le
    (-coreDensity (u 0) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) -
      -coreDensity (v 0) • EuclideanSpace.single 0 1)
    (coreThetaMass • pathPadLeft n (adjacentVector (fun a _ => coreGateDeriv a) u -
      adjacentVector (fun a _ => coreGateDeriv a) v))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm0, pathPadLeft_norm] at h
  nlinarith only [h, hp, coreChain_seed_sub_norm u v]

theorem coreSeed_gradient_lipschitz (n : ℕ) : LipschitzWith 1537 (gradient (@coreSeed n)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro u v
  simpa only [coreSeed_gradient, NNReal.coe_ofNat] using coreSeedGradient_sub_norm u v

theorem coreSeed_hessian_bound {n : ℕ} (u : Euclid (n + 1)) :
    ‖fderiv ℝ (gradient (@coreSeed n)) u‖ ≤ 1537 :=
  norm_fderiv_le_of_lipschitz ℝ (coreSeed_gradient_lipschitz n)

end FreshGradientMinimax
