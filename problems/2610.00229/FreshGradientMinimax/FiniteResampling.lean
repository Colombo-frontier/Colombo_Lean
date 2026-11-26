import FreshGradientMinimax.PathIncidence
import Mathlib.Algebra.Order.BigOperators.Expect

/-! Exact averaging under one-coordinate resampling of a finite independent
label list. This avoids a conditional probability or sphere-concentration
assumption in the adaptive hiding argument. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def resampleSwap {I J : Type*} [DecidableEq I] (i : I) : ((I → J) × J) ≃ ((I → J) × J) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

theorem expect_resample {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [Nonempty J]
    (i : I) (f : (I → J) → ℝ) :
    (𝔼 z, f z) = 𝔼 z, 𝔼 j, f (Function.update z i j) := by
  have he := Fintype.expect_equiv (resampleSwap (J := J) i)
    (fun p : (I → J) × J => f p.1)
    (fun p : (I → J) × J => f (Function.update p.1 i p.2))
    (fun p => by simp [resampleSwap])
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

theorem expect_coordinate_square {D : ℕ} (x : Euclid D) :
    (𝔼 j : Fin D, (x j) ^ 2) = ‖x‖ ^ 2 / D := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, ← euclid_norm_sq]

theorem expect_hidden_coordinate_square {m D : ℕ} [NeZero D]
    (q : (Fin m → Fin D) → Euclid D) (i : Fin m)
    (hind : ∀ z j, q (Function.update z i j) = q z) :
    (𝔼 z, (q z (z i)) ^ 2) = (𝔼 z, ‖q z‖ ^ 2) / D := by
  calc
    _ = 𝔼 z : Fin m → Fin D, 𝔼 j : Fin D,
        (q (Function.update z i j) ((Function.update z i j) i)) ^ 2 :=
      expect_resample i (fun z : Fin m → Fin D => (q z (z i)) ^ 2)
    _ = 𝔼 z : Fin m → Fin D, 𝔼 j : Fin D, (q z j) ^ 2 := by
      apply Finset.expect_congr rfl
      intro z _
      apply Finset.expect_congr rfl
      intro j _
      rw [hind z j, Function.update_self]
    _ = _ := by
      simp only [expect_coordinate_square]
      rw [← Finset.expect_div]

theorem expect_hidden_coordinate_square_le {m D : ℕ} [NeZero D]
    (q : (Fin m → Fin D) → Euclid D) (i : Fin m)
    (hind : ∀ z j, q (Function.update z i j) = q z)
    {B : ℝ} (hq : ∀ z, ‖q z‖ ≤ B) :
    (𝔼 z, (q z (z i)) ^ 2) ≤ B ^ 2 / D := by
  rw [expect_hidden_coordinate_square q i hind]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg D)
  apply Finset.expect_le Finset.univ_nonempty
  intro z _
  exact pow_le_pow_left₀ (norm_nonneg _) (hq z) 2

end FreshGradientMinimax
