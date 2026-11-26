import NCConcave16991.MixedHaarWordReservoir
import Mathlib.Algebra.Order.Floor.Semiring

/-! # A finite ambient dimension for the genuine common reservoir event -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

def wordAmbientDimension (n H N U : ℕ) (a : ℝ) : ℕ :=
  U + 1 + ⌈6 * (wordSliceCount n H N : ℝ) / a⌉₊

theorem wordAmbientDimension_gt (n H N U : ℕ) (a : ℝ) :
    U < wordAmbientDimension n H N U a := by
  unfold wordAmbientDimension
  omega

theorem wordAmbientDimension_pos (n H N U : ℕ) (a : ℝ) :
    0 < wordAmbientDimension n H N U a := (Nat.zero_le U).trans_lt (wordAmbientDimension_gt _ _ _ _ _)

theorem wordAmbientDimension_coefficient (n H N U : ℕ) {a : ℝ} (ha : 0 < a) :
    (wordSliceCount n H N : ℝ) / ((wordAmbientDimension n H N U a : ℝ) * a) ≤ 1 / 6 := by
  have hD : (0 : ℝ) < wordAmbientDimension n H N U a := by
    exact_mod_cast wordAmbientDimension_pos n H N U a
  have hceil : 6 * (wordSliceCount n H N : ℝ) / a ≤ (wordAmbientDimension n H N U a : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show ⌈6 * (wordSliceCount n H N : ℝ) / a⌉₊ ≤ wordAmbientDimension n H N U a by
      unfold wordAmbientDimension
      omega)
  have hh := (div_le_iff₀ ha).mp hceil
  apply (div_le_iff₀ (mul_pos hD ha)).mpr
  nlinarith only [hh]

theorem word_reservoir_projection_small (n H N U : ℕ) {a : ℝ} (ha : 0 < a)
    (i : Fin (wordAmbientDimension n H N U a)) :
    (wordReservoirLaw n H N (wordAmbientDimension n H N U a)).real {f |
      a ≤ ‖(wordReservoirSpan f).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2} ≤ 1 / 6 :=
  (word_reservoir_projection_tail (wordAmbientDimension_pos _ _ _ _ _) i ha).trans
    (wordAmbientDimension_coefficient n H N U ha)

end NCConcave16991.MixedHaar
