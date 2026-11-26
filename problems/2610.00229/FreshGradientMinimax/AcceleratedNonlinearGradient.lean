import FreshGradientMinimax.CorePairGradient
import FreshGradientMinimax.EuclidDropFirst
import FreshGradientMinimax.AcceleratedPrimal

/-! The nonlinear seed and disjoint links have their actual Euclidean
gradient, with constants independent of the number of links. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def acceleratedNonlinearTail {k : ℕ} (q : Euclid (k * 2 + 1)) : Euclid (k * 2) :=
  euclidJoin (fun i => corePairGradient (euclidBlock i (euclidDropFirst (k * 2) q)))

def acceleratedNonlinearGradient {k : ℕ} (q : Euclid (k * 2 + 1)) : Euclid (k * 2 + 1) :=
  -coreDensity (q 0) • EuclideanSpace.single 0 1 + pathPadRight (k * 2) (acceleratedNonlinearTail q)

theorem acceleratedNonlinear_hasFDerivAt {k : ℕ} (q : Euclid (k * 2 + 1)) :
    HasFDerivAt acceleratedNonlinear (innerSL ℝ (acceleratedNonlinearGradient q)) q := by
  have hs := (block_function_hasFDerivAt corePair_hasFDerivAt (euclidDropFirst (k * 2) q)).comp q
    (euclidDropFirst (k * 2)).hasFDerivAt
  have hseed := ((coreTheta_hasDerivAt (q 0)).comp_hasFDerivAt q
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k * 2 + 1))).hasFDerivAt).neg
  have h := hseed.add hs
  simp only [Function.comp_def, euclidDropFirst_block_zero, euclidDropFirst_block_one] at h
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [acceleratedNonlinearGradient, acceleratedNonlinearTail, ← euclidDropFirst_adjoint,
    ContinuousLinearMap.adjoint_inner_left, innerSL_apply, inner_add_left,
    real_inner_smul_left, EuclideanSpace.inner_single_left, EuclideanSpace.proj]

theorem acceleratedNonlinear_gradient {k : ℕ} (q : Euclid (k * 2 + 1)) :
    gradient acceleratedNonlinear q = acceleratedNonlinearGradient q :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedNonlinear_hasFDerivAt q)).gradient

theorem acceleratedNonlinearGradient_zero {k : ℕ} (q : Euclid (k * 2 + 1)) :
    acceleratedNonlinearGradient q 0 = -coreDensity (q 0) := by
  simp [acceleratedNonlinearGradient]

theorem acceleratedNonlinearGradient_succ {k : ℕ} (q : Euclid (k * 2 + 1)) (j : Fin (k * 2)) :
    acceleratedNonlinearGradient q j.succ = acceleratedNonlinearTail q j := by
  simp [acceleratedNonlinearGradient, EuclideanSpace.single_apply, (Fin.succ_ne_zero j).symm]

theorem acceleratedNonlinearGradient_coordinate {k : ℕ} (q : Euclid (k * 2 + 1)) (j : Fin (k * 2 + 1)) :
    |acceleratedNonlinearGradient q j| ≤ 96 := by
  refine Fin.cases ?_ (fun a => ?_) j
  · rw [acceleratedNonlinearGradient_zero, abs_neg, abs_of_pos (coreDensity_pos _)]
    exact (coreDensity_le_one _).trans (by norm_num)
  · rw [acceleratedNonlinearGradient_succ]
    obtain ⟨⟨i,b⟩, rfl⟩ := finProdFinEquiv.surjective a
    rw [acceleratedNonlinearTail, euclidJoin_apply]
    exact corePairGradient_coordinate _ b

theorem acceleratedNonlinearGradient_norm {k : ℕ} (q : Euclid (k * 2 + 1)) :
    ‖acceleratedNonlinearGradient q‖ ≤ 103 * Real.sqrt (k + 1 : ℕ) := by
  have ht := euclidJoin_norm_bound (by norm_num : (0 : ℝ) ≤ 102)
    (fun i : Fin k => corePairGradient (euclidBlock i (euclidDropFirst (k * 2) q)))
    (fun _ => corePairGradient_norm _)
  have hs : 1 ≤ Real.sqrt (k + 1 : ℕ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hmono := Real.sqrt_le_sqrt (Nat.cast_le.mpr (show k ≤ k + 1 by omega) : (k : ℝ) ≤ (k + 1 : ℕ))
  have h := norm_add_le (-coreDensity (q 0) • EuclideanSpace.single (0 : Fin (k * 2 + 1)) (1 : ℝ))
    (pathPadRight (k * 2) (acceleratedNonlinearTail q))
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (coreDensity_pos _),
    EuclideanSpace.norm_single, norm_one, mul_one, pathPadRight_norm] at h
  change ‖acceleratedNonlinearGradient q‖ ≤ _ at h
  change ‖acceleratedNonlinearTail q‖ ≤ _ at ht
  linarith only [h, ht, hs, hmono, coreDensity_le_one (q 0)]

theorem acceleratedNonlinearGradient_difference {k : ℕ} (q p : Euclid (k * 2 + 1)) :
    ‖acceleratedNonlinearGradient q - acceleratedNonlinearGradient p‖ ≤ 3201 * ‖q - p‖ := by
  have ht := block_function_gradient_difference (by norm_num : (0 : ℝ) ≤ 3200)
    corePairGradient_difference (euclidDropFirst (k * 2) q) (euclidDropFirst (k * 2) p)
  change ‖acceleratedNonlinearTail q - acceleratedNonlinearTail p‖ ≤ _ at ht
  rw [← map_sub] at ht
  have hd := euclidDropFirst_norm (q - p)
  have hs := coreChain_seed_sub_norm q p
  have he : acceleratedNonlinearGradient q - acceleratedNonlinearGradient p =
      (-coreDensity (q 0) • EuclideanSpace.single 0 1 - -coreDensity (p 0) • EuclideanSpace.single 0 1) +
        pathPadRight (k * 2) (acceleratedNonlinearTail q - acceleratedNonlinearTail p) := by
    simp only [acceleratedNonlinearGradient, map_sub]
    abel
  rw [he]
  have h := norm_add_le
    (-coreDensity (q 0) • EuclideanSpace.single (0 : Fin (k * 2 + 1)) (1 : ℝ) -
      -coreDensity (p 0) • EuclideanSpace.single 0 1)
    (pathPadRight (k * 2) (acceleratedNonlinearTail q - acceleratedNonlinearTail p))
  rw [pathPadRight_norm] at h
  linarith only [h, hs, ht, hd]

end FreshGradientMinimax
