import Bilevel.RadialSecond
import Bilevel.WrappedChain

/-! Smoothness of the compressed rotated objective from the actual chain rule. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem wrappedGradient_operator (ν R : ℝ) (u h : E) :
    wrappedGradient ν R u h = compressDerivative R u h + ν • compress R u := by
  simp only [wrappedGradient, compressDerivative_apply, compress, smul_smul, sub_smul]
  simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem wrappedGradient_bound (ν R G : ℝ) (hν : 0 ≤ ν) (hR : 0 < R)
    (u h : E) (hh : ‖h‖ ≤ G) : ‖wrappedGradient ν R u h‖ ≤ G + ν * R := by
  rw [wrappedGradient_operator]
  calc
    _ ≤ ‖compressDerivative R u h‖ + ‖ν • compress R u‖ := norm_add_le _ _
    _ ≤ ‖h‖ + ν * R := add_le_add (compressDerivative_norm_le R hR u h) (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hν]
      exact mul_le_mul_of_nonneg_left (compress_norm_le_radius R hR u) hν)
    _ ≤ _ := add_le_add_right hh _

theorem wrappedGradient_difference (ν R G L : ℝ) (hν : 0 ≤ ν) (hR : 0 < R)
    (u w h k : E) (hk : ‖k‖ ≤ G) (hhk : ‖h - k‖ ≤ L * ‖u - w‖) :
    ‖wrappedGradient ν R u h - wrappedGradient ν R w k‖ ≤
      (L + 4 * G / R + ν) * ‖u - w‖ := by
  have he : wrappedGradient ν R u h - wrappedGradient ν R w k =
      compressDerivative R u (h - k) + (compressDerivative R u - compressDerivative R w) k +
        ν • (compress R u - compress R w) := by
    simp only [wrappedGradient_operator, map_sub, ContinuousLinearMap.sub_apply, smul_sub]
    abel
  have h0 := (compressDerivative_norm_le R hR u (h - k)).trans hhk
  have h1 : ‖(compressDerivative R u - compressDerivative R w) k‖ ≤
      (4 / R) * ‖u - w‖ * G :=
    (compressDerivative_difference_apply R hR u w k).trans
      (mul_le_mul_of_nonneg_left hk (by positivity))
  have h2 : ‖ν • (compress R u - compress R w)‖ ≤ ν * ‖u - w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hν]
    exact mul_le_mul_of_nonneg_left (by
      simpa using (compress_lipschitz R hR).norm_sub_le u w) hν
  rw [he]
  have ht := (norm_add_le
    (compressDerivative R u (h - k) + (compressDerivative R u - compressDerivative R w) k)
    (ν • (compress R u - compress R w))).trans (add_le_add_right (norm_add_le _ _) _)
  calc
    _ ≤ L * ‖u - w‖ + (4 / R) * ‖u - w‖ * G + ν * ‖u - w‖ := by linarith
    _ = _ := by ring

end Bilevel.RadialWrapper
namespace Bilevel.WrappedChain
open ZeroChain RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem coordinates_lipschitz (n : ℕ) (R : ℝ) (hR : 0 < R) (U : Space n →ₗᵢ[ℝ] E)
    (u w : E) : ‖coordinates n R U u - coordinates n R U w‖ ≤ ‖u - w‖ := by
  have hp : ‖U.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact U.norm_toContinuousLinearMap_le
  change ‖U.toContinuousLinearMap.adjoint (compress R u) -
    U.toContinuousLinearMap.adjoint (compress R w)‖ ≤ _
  rw [← map_sub]
  exact (U.toContinuousLinearMap.adjoint.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by
      simpa using (compress_lipschitz R hR).norm_sub_le u w))

theorem gradient_difference_bound (n : ℕ) (a β ν R G L : ℝ)
    (hν : 0 ≤ ν) (hR : 0 < R) (hL : 0 ≤ L)
    (hbound : ∀ z : Space n, ‖gradient (ScaledZeroChain.value n a β) z‖ ≤ G)
    (hlip : ∀ x y : Space n, ‖gradient (ScaledZeroChain.value n a β) x -
      gradient (ScaledZeroChain.value n a β) y‖ ≤ L * ‖x - y‖)
    (U : Space n →ₗᵢ[ℝ] E) (u w : E) :
    ‖gradient (value n a β ν R U) u - gradient (value n a β ν R U) w‖ ≤
      (L + 4 * G / R + ν) * ‖u - w‖ := by
  rw [(value_hasGradientAt n a β ν R hR U u).gradient,
    (value_hasGradientAt n a β ν R hR U w).gradient]
  apply wrappedGradient_difference ν R G L hν hR u w
    (carriedGradient n a β R U u) (carriedGradient n a β R U w)
  · simpa only [carriedGradient, U.norm_map] using hbound (coordinates n R U w)
  · simp only [carriedGradient, ← map_sub, U.norm_map]
    exact (hlip _ _).trans (mul_le_mul_of_nonneg_left (coordinates_lipschitz n R hR U u w) hL)

end Bilevel.WrappedChain
