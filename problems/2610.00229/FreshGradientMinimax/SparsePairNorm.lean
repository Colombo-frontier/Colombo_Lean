import FreshGradientMinimax.PathCoordinates

/-! Euclidean estimates for vectors of adjacent-coordinate functions.
The two coordinate restrictions have norm at most one, independent of length. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def adjacentVector {n : ℕ} (f : ℝ → ℝ → ℝ) (u : Euclid (n + 1)) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun e => f (u e.castSucc) (u e.succ))

@[simp]
theorem adjacentVector_apply {n : ℕ} (f : ℝ → ℝ → ℝ) (u : Euclid (n + 1)) (e : Fin n) :
    adjacentVector f u e = f (u e.castSucc) (u e.succ) := rfl

theorem euclid_sum_single {n : ℕ} (x : Euclid n) :
    (∑ e : Fin n, x e • EuclideanSpace.single e (1 : ℝ)) = x := by
  ext j
  change (EuclideanSpace.proj (𝕜 := ℝ) j) (∑ e : Fin n, x e • EuclideanSpace.single e (1 : ℝ)) = _
  rw [map_sum]
  simp [EuclideanSpace.proj, EuclideanSpace.single_apply, eq_comm]

theorem sum_castSucc_sq_le {n : ℕ} (x : Euclid (n + 1)) :
    (∑ e : Fin n, (x e.castSucc) ^ 2) ≤ ‖x‖ ^ 2 := by
  rw [euclid_norm_sq, Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem sum_succ_sq_le {n : ℕ} (x : Euclid (n + 1)) :
    (∑ e : Fin n, (x e.succ) ^ 2) ≤ ‖x‖ ^ 2 := by
  rw [euclid_norm_sq, Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem square_le_of_abs_le_pair {z x y A B : ℝ}
    (hz : |z| ≤ A * |x| + B * |y|) : z ^ 2 ≤ 2 * A ^ 2 * x ^ 2 + 2 * B ^ 2 * y ^ 2 := by
  have h := mul_self_le_mul_self (abs_nonneg z) hz
  have he : (A * |x| + B * |y|) ^ 2 + (A * |x| - B * |y|) ^ 2 =
      2 * A ^ 2 * x ^ 2 + 2 * B ^ 2 * y ^ 2 := by nlinarith only [sq_abs x, sq_abs y]
  nlinarith only [h, he, sq_abs z, sq_nonneg (A * |x| - B * |y|)]

theorem adjacentVector_sub_norm_le {n : ℕ} {f : ℝ → ℝ → ℝ} {A B C : ℝ}
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) (hC : 0 ≤ C) (hAB : 2 * (A ^ 2 + B ^ 2) ≤ C ^ 2)
    (hf : ∀ a b c d, |f a b - f c d| ≤ A * |a - c| + B * |b - d|)
    (u v : Euclid (n + 1)) : ‖adjacentVector f u - adjacentVector f v‖ ≤ C * ‖u - v‖ := by
  have he (e : Fin n) : (adjacentVector f u e - adjacentVector f v e) ^ 2 ≤
      2 * A ^ 2 * ((u - v) e.castSucc) ^ 2 + 2 * B ^ 2 * ((u - v) e.succ) ^ 2 :=
    square_le_of_abs_le_pair (hf _ _ _ _)
  have hs : ‖adjacentVector f u - adjacentVector f v‖ ^ 2 ≤
      2 * A ^ 2 * (∑ e : Fin n, ((u - v) e.castSucc) ^ 2) +
      2 * B ^ 2 * (∑ e : Fin n, ((u - v) e.succ) ^ 2) := by
    rw [euclid_norm_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => he e)
  have h1 := mul_le_mul_of_nonneg_left (sum_castSucc_sq_le (u - v)) (by positivity : 0 ≤ 2 * A ^ 2)
  have h2 := mul_le_mul_of_nonneg_left (sum_succ_sq_le (u - v)) (by positivity : 0 ≤ 2 * B ^ 2)
  have h3 := mul_le_mul_of_nonneg_right hAB (sq_nonneg ‖u - v‖)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  nlinarith only [hs, h1, h2, h3]

theorem adjacent_sum_left {n : ℕ} (f : ℝ → ℝ → ℝ) (u : Euclid (n + 1)) :
    (∑ e : Fin n, f (u e.castSucc) (u e.succ) • EuclideanSpace.single e.castSucc (1 : ℝ)) =
      pathPadLeft n (adjacentVector f u) := by
  rw [← euclid_sum_single (adjacentVector f u), map_sum]
  simp only [map_smul, pathPadLeft_single, adjacentVector_apply]

theorem adjacent_sum_right {n : ℕ} (f : ℝ → ℝ → ℝ) (u : Euclid (n + 1)) :
    (∑ e : Fin n, f (u e.castSucc) (u e.succ) • EuclideanSpace.single e.succ (1 : ℝ)) =
      pathPadRight n (adjacentVector f u) := by
  rw [← euclid_sum_single (adjacentVector f u), map_sum]
  simp only [map_smul, pathPadRight_single, adjacentVector_apply]

theorem initialVector_sub_norm_le {n : ℕ} {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ a b, |f a - f b| ≤ C * |a - b|)
    (u v : Euclid (n + 1)) :
    ‖adjacentVector (fun a _ => f a) u - adjacentVector (fun a _ => f a) v‖ ≤ C * ‖u - v‖ := by
  have he (e : Fin n) : (f (u e.castSucc) - f (v e.castSucc)) ^ 2 ≤
      C ^ 2 * ((u - v) e.castSucc) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hf (u e.castSucc) (v e.castSucc)) 2
    simpa only [sq_abs, mul_pow] using h
  have hs : ‖adjacentVector (fun a _ => f a) u - adjacentVector (fun a _ => f a) v‖ ^ 2 ≤
      C ^ 2 * (∑ e : Fin n, ((u - v) e.castSucc) ^ 2) := by
    rw [euclid_norm_sq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ => he e)
  have hb := mul_le_mul_of_nonneg_left (sum_castSucc_sq_le (u - v)) (sq_nonneg C)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  nlinarith only [hs, hb]

theorem euclid_norm_le_of_coordinate_bound {n : ℕ} (x : Euclid n) {C : ℝ}
    (hC : 0 ≤ C) (hx : ∀ i, |x i| ≤ C) : ‖x‖ ≤ C * Real.sqrt (n : ℝ) := by
  have hs : ‖x‖ ^ 2 ≤ C ^ 2 * (n : ℝ) := by
    rw [euclid_norm_sq]
    calc
      _ ≤ ∑ _i : Fin n, C ^ 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hx i) 2)
      _ = _ := by simp; ring
  have hr := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  nlinarith only [hs, hr]

end FreshGradientMinimax
