import Smoothness2601.PrefixProducts
import Mathlib.Analysis.Calculus.MeanValue

/-! Generic two-coordinate sparse estimates, independent of any profile. -/
noncomputable section
namespace Smoothness2601.SparseCoordinates
open scoped BigOperators RealInnerProductSpace
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))
def basis {n : ℕ} (i : Fin (n+1)) : Space n := EuclideanSpace.single i 1
theorem inner_basis {n : ℕ} (i : Fin (n+1)) (v : Space n) : ⟪basis i,v⟫ = v i := by
  simp [basis,EuclideanSpace.inner_single_left]

theorem scalar_lip_of_deriv_bound (f : ℝ → ℝ) (K : ℝ)
    (hf : Differentiable ℝ f) (hb : ∀ x, |deriv f x| ≤ K) (x y : ℝ) :
    |f x - f y| ≤ K * |x - y| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Set.univ) => hf z)
    (fun z (_ : z ∈ Set.univ) => by simpa only [Real.norm_eq_abs] using hb z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

theorem product_lip (f g : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ x, |f x| ≤ K) (hg : ∀ x, |g x| ≤ K)
    (hfl : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hgl : ∀ x y, |g x - g y| ≤ K * |x - y|) (a b c d : ℝ) :
    |f a * g b - f c * g d| ≤ K ^ 2 * (|a - c| + |b - d|) := by
  have he : f a * g b - f c * g d = (f a - f c) * g b + f c * (g b - g d) := by ring
  rw [he]
  have h0 : |(f a - f c) * g b| ≤ (K * |a - c|) * K := by
    rw [abs_mul]
    exact mul_le_mul (hfl a c) (hg b) (abs_nonneg _) (by positivity)
  have h1 : |f c * (g b - g d)| ≤ K * (K * |b - d|) := by
    rw [abs_mul]
    exact mul_le_mul (hf c) (hgl b d) (abs_nonneg _) hK
  exact (abs_add _ _).trans (by nlinarith)

theorem norm_sum_basis_sq {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Fin (n + 1)) (hf : Function.Injective f) (a : ι → ℝ) :
    ‖∑ i, a i • basis (f i)‖ ^ 2 = ∑ i, (a i) ^ 2 := by
  classical
  have hi (i j : ι) : ⟪basis (f i), basis (f j)⟫ = if i = j then (1 : ℝ) else 0 := by
    rw [inner_basis]
    simp [basis, hf.eq_iff]
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hi,
    mul_ite, mul_one, mul_zero]
  simp [pow_two]

theorem norm_sq_coordinates {n : ℕ} (d : Space n) : ‖d‖ ^ 2 = ∑ j, (d j) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2
    (fun _ : Fin (n + 1) => ℝ) d

/-- The two shifted coordinate windows each occur only once in the Euclidean
sum of squares. This is where the chain length disappears. -/
theorem adjacent_squares_le {n : ℕ} (d : Space n) :
    (∑ i : Fin n, ((d i.castSucc) ^ 2 + (d i.succ) ^ 2)) ≤ 2 * ‖d‖ ^ 2 := by
  have hc : (∑ i : Fin n, (d i.castSucc) ^ 2) ≤ ‖d‖ ^ 2 := by
    rw [norm_sq_coordinates, Fin.sum_univ_castSucc]
    linarith [sq_nonneg (d (Fin.last n))]
  have hs : (∑ i : Fin n, (d i.succ) ^ 2) ≤ ‖d‖ ^ 2 := by
    rw [norm_sq_coordinates, Fin.sum_univ_succ]
    linarith [sq_nonneg (d 0)]
  rw [Finset.sum_add_distrib]
  linarith

theorem norm_sparse_coefficients_le {n : ℕ} (f : Fin n → Fin (n + 1))
    (hf : Function.Injective f) (a : Fin n → ℝ) (d : Space n) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M * (|d i.castSucc| + |d i.succ|)) :
    ‖∑ i, a i • basis (f i)‖ ≤ 2 * M * ‖d‖ := by
  have hi (i : Fin n) : (a i) ^ 2 ≤ 2 * M ^ 2 * ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) := by
    have hsq := (sq_le_sq₀ (abs_nonneg (a i))
      (show 0 ≤ M * (|d i.castSucc| + |d i.succ|) by positivity)).mpr (ha i)
    rw [sq_abs, mul_pow] at hsq
    have htwo : (|d i.castSucc| + |d i.succ|) ^ 2 ≤
        2 * ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) := by
      nlinarith [sq_abs (d i.castSucc), sq_abs (d i.succ),
        sq_nonneg (|d i.castSucc| - |d i.succ|)]
    have hh := mul_le_mul_of_nonneg_left htwo (sq_nonneg M)
    nlinarith
  have hs : ‖∑ i, a i • basis (f i)‖ ^ 2 ≤ (2 * M * ‖d‖) ^ 2 := by
    rw [norm_sum_basis_sq f hf]
    calc
      _ ≤ ∑ i : Fin n, 2 * M ^ 2 * ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ = 2 * M ^ 2 * ∑ i : Fin n, ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * M ^ 2 * (2 * ‖d‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (adjacent_squares_le d) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

end Smoothness2601.SparseCoordinates
