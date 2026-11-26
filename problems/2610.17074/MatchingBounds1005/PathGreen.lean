import MatchingBounds1005.BlockGradientBound
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.Interval.Finset.Fin

/-!
# Actual path matrices and their Green functions

The path has `n+1` vertices and `n` edges. Its Laplacian is constructed from
the actual incidence matrix, not postulated by an inverse estimate.
-/
noncomputable section
open scoped Matrix BigOperators InnerProductSpace

namespace MatchingBounds1005.PathGreen

def incidence (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℝ :=
  fun i j => (if j = i.succ then 1 else 0) - (if j = i.castSucc then 1 else 0)

def laplacian (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (incidence n)ᵀ * incidence n

def shiftedPath (h : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun _ => h ^ 2) + laplacian n

def pathMatrix (L h : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  L • shiftedPath h n

def green (h : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (shiftedPath h n)⁻¹

theorem incidence_mulVec (n : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin n) :
    (incidence n *ᵥ v) i = v i.succ - v i.castSucc := by
  simp [Matrix.mulVec, dotProduct, incidence, sub_mul, Finset.sum_sub_distrib]

theorem laplacian_energy (n : ℕ) (v : Fin (n + 1) → ℝ) :
    dotProduct v (laplacian n *ᵥ v) = ∑ i : Fin n, (v i.succ - v i.castSucc) ^ 2 := by
  rw [laplacian, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, incidence_mulVec, pow_two]

theorem laplacian_posSemidef (n : ℕ) : (laplacian n).PosSemidef := by
  simpa [laplacian, Matrix.conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self (incidence n)

theorem shiftedPath_posDef (h : ℝ) (hh : 0 < h) (n : ℕ) : (shiftedPath h n).PosDef := by
  apply Matrix.PosDef.add_posSemidef _ (laplacian_posSemidef n)
  exact Matrix.posDef_diagonal_iff.mpr (fun _ => sq_pos_of_pos hh)

theorem shiftedPath_det_ne (h : ℝ) (hh : 0 < h) (n : ℕ) : (shiftedPath h n).det ≠ 0 :=
  ne_of_gt (shiftedPath_posDef h hh n).det_pos

theorem shiftedPath_green (h : ℝ) (hh : 0 < h) (n : ℕ) :
    shiftedPath h n * green h n = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (shiftedPath_det_ne h hh n))

theorem green_shiftedPath (h : ℝ) (hh : 0 < h) (n : ℕ) :
    green h n * shiftedPath h n = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (shiftedPath_det_ne h hh n))

theorem shiftedPath_energy (h : ℝ) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    dotProduct v (shiftedPath h n *ᵥ v) =
      h ^ 2 * (∑ i, (v i) ^ 2) + ∑ i : Fin n, (v i.succ - v i.castSucc) ^ 2 := by
  rw [shiftedPath, Matrix.add_mulVec, dotProduct_add, laplacian_energy]
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.mul_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem shiftedPath_coercive (h : ℝ) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    h ^ 2 * (∑ i, (v i) ^ 2) ≤ dotProduct v (shiftedPath h n *ᵥ v) := by
  rw [shiftedPath_energy]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem laplacian_mulVec_entry (n : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (laplacian n *ᵥ v) i = ∑ j : Fin n,
      ((if i = j.succ then 1 else 0) - (if i = j.castSucc then 1 else 0)) *
        (v j.succ - v j.castSucc) := by
  rw [laplacian, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incidence]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact incidence_mulVec n v j

theorem laplacian_at_min (n : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hi : ∀ j, v i ≤ v j) : (laplacian n *ᵥ v) i ≤ 0 := by
  rw [laplacian_mulVec_entry]
  apply Finset.sum_nonpos
  intro j _
  have hne : j.castSucc ≠ j.succ := by
    intro heq
    have hv := congrArg Fin.val heq
    simp at hv
  by_cases hs : i = j.succ
  · have hc : i ≠ j.castSucc := by rw [hs]; exact Ne.symm hne
    simp only [if_pos hs, if_neg hc, sub_zero, one_mul]
    simpa [hs] using sub_nonpos.mpr (hi j.castSucc)
  · by_cases hc : i = j.castSucc
    · simp only [if_neg hs, if_pos hc]
      have hv := hi j.succ
      rw [hc] at hv
      linarith
    · simp [hs, hc]

/-- Discrete maximum principle for the actual shifted path matrix. -/
theorem maximum_principle (h : ℝ) (hh : 0 < h) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ (shiftedPath h n *ᵥ v) i) : ∀ i, 0 ≤ v i := by
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hm' : ∀ j, v m ≤ v j := fun j => hm j (Finset.mem_univ _)
  have hlap := laplacian_at_min n v m hm'
  have hrow := hv m
  simp only [shiftedPath, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, Pi.mul_apply] at hrow
  have hm0 : 0 ≤ v m := by nlinarith [sq_pos_of_pos hh]
  intro i
  exact hm0.trans (hm' i)

theorem green_mulVec_solve (h : ℝ) (hh : 0 < h) (n : ℕ) (b : Fin (n + 1) → ℝ) :
    shiftedPath h n *ᵥ (green h n *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, shiftedPath_green h hh n, Matrix.one_mulVec]

theorem green_mulVec_nonneg (h : ℝ) (hh : 0 < h) (n : ℕ) (b : Fin (n + 1) → ℝ)
    (hb : ∀ i, 0 ≤ b i) : ∀ i, 0 ≤ (green h n *ᵥ b) i := by
  apply maximum_principle h hh n
  rw [green_mulVec_solve h hh n]
  exact hb

theorem green_nonneg (h : ℝ) (hh : 0 < h) (n : ℕ) (i j : Fin (n + 1)) :
    0 ≤ green h n i j := by
  have hcol := green_mulVec_nonneg h hh n (Pi.single j 1)
    (fun k => by simp [Pi.single_apply]; split_ifs <;> norm_num) i
  simpa only [Matrix.mulVec_single_one] using hcol

theorem incidence_one (n : ℕ) : incidence n *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  funext i
  simp [incidence_mulVec]

theorem sum_laplacian_mulVec (n : ℕ) (v : Fin (n + 1) → ℝ) :
    ∑ i, (laplacian n *ᵥ v) i = 0 := by
  have hz : dotProduct (fun _ => (1 : ℝ)) (laplacian n *ᵥ v) = 0 := by
    rw [laplacian, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      incidence_one, zero_dotProduct]
  simpa only [dotProduct, one_mul] using hz

theorem green_column_mass (h : ℝ) (hh : 0 < h) (n : ℕ) (j : Fin (n + 1)) :
    h ^ 2 * (∑ i, green h n i j) = 1 := by
  have hsol := green_mulVec_solve h hh n (Pi.single j 1)
  have hsum := congrArg (fun v : Fin (n + 1) → ℝ => ∑ i, v i) hsol
  simp only [Matrix.mulVec_single_one, shiftedPath, Matrix.add_mulVec, Pi.add_apply,
    Finset.sum_add_distrib, Matrix.mulVec_diagonal, Pi.mul_apply,
    ← Finset.mul_sum, sum_laplacian_mulVec, add_zero] at hsum
  simpa using hsum

theorem laplacian_at_max (n : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hi : ∀ j, v j ≤ v i) : 0 ≤ (laplacian n *ᵥ v) i := by
  have hm := laplacian_at_min n (-v) i (fun j => neg_le_neg (hi j))
  simpa only [Matrix.mulVec_neg, Pi.neg_apply, neg_nonpos] using hm

theorem green_column_max (h : ℝ) (hh : 0 < h) (n : ℕ) (j i : Fin (n + 1)) :
    green h n i j ≤ green h n j j := by
  let v : Fin (n + 1) → ℝ := fun k => green h n k j
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  have hm' : ∀ k, v k ≤ v m := fun k => hm k (Finset.mem_univ _)
  by_cases hmj : m = j
  · simpa [v, hmj] using hm' i
  have hsol := green_mulVec_solve h hh n (Pi.single j 1)
  have hrow := congrFun hsol m
  simp only [Matrix.mulVec_single_one] at hrow
  change (shiftedPath h n *ᵥ v) m = (Pi.single j 1 : Fin (n + 1) → ℝ) m at hrow
  rw [Pi.single_eq_of_ne hmj] at hrow
  simp only [shiftedPath, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal,
    Pi.mul_apply] at hrow
  have hlap := laplacian_at_max n v m hm'
  have hm0 : v m ≤ 0 := by nlinarith [sq_pos_of_pos hh]
  have hsum : ∑ k, v k ≤ 0 := Finset.sum_nonpos (fun k _ => (hm' k).trans hm0)
  have hbad := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) hsum
  have hmass := green_column_mass h hh n j
  change h ^ 2 * (∑ k, v k) = 1 at hmass
  linarith

theorem green_diag_pos (h : ℝ) (hh : 0 < h) (n : ℕ) (j : Fin (n + 1)) :
    0 < green h n j j := by
  by_contra hn
  have hn' : green h n j j ≤ 0 := le_of_not_gt hn
  have hsum : ∑ i, green h n i j ≤ 0 :=
    Finset.sum_nonpos (fun i _ => (green_column_max h hh n j i).trans hn')
  have hbad := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) hsum
  have hmass := green_column_mass h hh n j
  linarith

def prefixIndicator {n : ℕ} (i : Fin n) : Fin (n + 1) → ℝ :=
  fun k => if k ≤ i.castSucc then 1 else 0

def prefixSum {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.Iic i.castSucc, v k

theorem dotProduct_prefix {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin n) :
    dotProduct (prefixIndicator i) v = prefixSum v i := by
  classical
  simp only [dotProduct, prefixIndicator, ite_mul, one_mul, zero_mul]
  simp [prefixSum, ← Finset.sum_filter]
  congr 1
  ext k
  simp

theorem incidence_prefix {n : ℕ} (i j : Fin n) :
    (incidence n *ᵥ prefixIndicator i) j = if j = i then -1 else 0 := by
  rw [incidence_mulVec]
  change (if j.val + 1 ≤ i.val then (1 : ℝ) else 0) -
    (if j.val ≤ i.val then 1 else 0) = if j = i then -1 else 0
  by_cases hji : j = i
  · subst j
    simp
  · have hne : j.val ≠ i.val := fun heq => hji (Fin.ext heq)
    have heq : (j.val + 1 ≤ i.val) ↔ (j.val ≤ i.val) := by omega
    simp [hji, heq]

theorem laplacian_prefix_flux {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin n) :
    dotProduct (prefixIndicator i) (laplacian n *ᵥ v) = v i.castSucc - v i.succ := by
  have hp : incidence n *ᵥ prefixIndicator i = Pi.single i (-1) := by
    funext j
    rw [incidence_prefix]
    simp [Pi.single_apply, eq_comm]
  rw [laplacian, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, hp, single_dotProduct, incidence_mulVec]
  ring

theorem shiftedPath_prefix_flux (h : ℝ) {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin n) :
    dotProduct (prefixIndicator i) (shiftedPath h n *ᵥ v) =
      h ^ 2 * prefixSum v i + v i.castSucc - v i.succ := by
  rw [shiftedPath, Matrix.add_mulVec, dotProduct_add, laplacian_prefix_flux]
  have hd : dotProduct (prefixIndicator i) (Matrix.diagonal (fun _ : Fin (n + 1) => h ^ 2) *ᵥ v) =
      h ^ 2 * dotProduct (prefixIndicator i) v := by
    simp only [Matrix.mulVec_diagonal, Pi.mul_apply, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hd, dotProduct_prefix]
  ring

theorem green_prefix_flux (h : ℝ) (hh : 0 < h) (n : ℕ) (j : Fin (n + 1)) (i : Fin n) :
    h ^ 2 * prefixSum (fun k => green h n k j) i + green h n i.castSucc j - green h n i.succ j =
      if j ≤ i.castSucc then 1 else 0 := by
  have hs := green_mulVec_solve h hh n (Pi.single j 1)
  have hd := congrArg (dotProduct (prefixIndicator i)) hs
  simp only [Matrix.mulVec_single_one, shiftedPath_prefix_flux, dotProduct_single, mul_one,
    prefixIndicator] at hd
  exact hd

theorem prefixSum_bounds {n : ℕ} (v : Fin (n + 1) → ℝ) (B : ℝ)
    (hv : ∀ k, 0 ≤ v k ∧ v k ≤ B) (i : Fin n) :
    0 ≤ prefixSum v i ∧ prefixSum v i ≤ (i.val + 1 : ℕ) * B := by
  constructor
  · exact Finset.sum_nonneg (fun k _ => (hv k).1)
  · calc
      _ ≤ ∑ _k ∈ Finset.Iic i.castSucc, B := Finset.sum_le_sum (fun k _ => (hv k).2)
      _ = _ := by simp [Fin.card_Iic]

theorem suffixSum_bounds {n : ℕ} (v : Fin (n + 1) → ℝ) (B : ℝ)
    (hv : ∀ k, 0 ≤ v k ∧ v k ≤ B) (i : Fin n) :
    0 ≤ (∑ k, v k) - prefixSum v i ∧
      (∑ k, v k) - prefixSum v i ≤ (n - i.val : ℕ) * B := by
  have hsplit : (∑ k, v k) - prefixSum v i = ∑ k ∈ Finset.Ioi i.castSucc, v k := by
    have hcomp : (Finset.Iic i.castSucc)ᶜ = Finset.Ioi i.castSucc := by
      ext k
      simp
    have h := Finset.sum_add_sum_compl (Finset.Iic i.castSucc) v
    rw [hcomp] at h
    change prefixSum v i + (∑ k ∈ Finset.Ioi i.castSucc, v k) = ∑ k, v k at h
    linarith
  rw [hsplit]
  constructor
  · exact Finset.sum_nonneg (fun k _ => (hv k).1)
  · calc
      _ ≤ ∑ _k ∈ Finset.Ioi i.castSucc, B := Finset.sum_le_sum (fun k _ => (hv k).2)
      _ = _ := by simp [Fin.card_Ioi]

theorem sequence_variation_bound (f : ℕ → ℝ) (n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    |f i - f j| ≤ ∑ k ∈ Finset.range n, |f (k + 1) - f k| := by
  have hordered (a b : ℕ) (hb : b ≤ n) (hab : a ≤ b) :
      |f a - f b| ≤ ∑ k ∈ Finset.range n, |f (k + 1) - f k| := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico a b, |f (k + 1) - f k| := by
        simpa only [Real.dist_eq, abs_sub_comm] using dist_le_Ico_sum_dist f hab
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro k hk; simp only [Finset.mem_Ico] at hk; exact Finset.mem_range.mpr (by omega))
        (fun _ _ _ => abs_nonneg _)
  rcases le_total i j with hij | hji
  · exact hordered i j hj hij
  · rw [abs_sub_comm]
    exact hordered j i hi hji

theorem path_difference_sq_bound (n : ℕ) (v : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    (v i - v j) ^ 2 ≤ n * ∑ k : Fin n, (v k.succ - v k.castSucc) ^ 2 := by
  let f : ℕ → ℝ := fun k => v ⟨min k n, by omega⟩
  have hi : i.val ≤ n := by omega
  have hj : j.val ≤ n := by omega
  have hfi : f i.val = v i := by simp [f, Nat.min_eq_left hi]
  have hfj : f j.val = v j := by simp [f, Nat.min_eq_left hj]
  have hsum : (∑ k ∈ Finset.range n, |f (k + 1) - f k|) =
      ∑ k : Fin n, |v k.succ - v k.castSucc| := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => |f (k + 1) - f k|) n]
    apply Finset.sum_congr rfl
    intro k _
    have hk0 : k.val ≤ n := by omega
    have hk1 : k.val + 1 ≤ n := by omega
    simp only [f, Nat.min_eq_left hk0, Nat.min_eq_left hk1]
    rfl
  have hv := sequence_variation_bound f n i.val j.val hi hj
  rw [hfi, hfj, hsum] at hv
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun k _ => abs_nonneg _))).2 hv
  rw [sq_abs] at hv2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ))
    (fun k => |v k.succ - v k.castSucc|)
  have hc' : (∑ k : Fin n, |v k.succ - v k.castSucc|) ^ 2 ≤
      n * ∑ k : Fin n, (v k.succ - v k.castSucc) ^ 2 := by
    simpa [sq_abs] using hc
  exact hv2.trans hc'

theorem green_column_energy (h : ℝ) (hh : 0 < h) (n : ℕ) (j : Fin (n + 1)) :
    h ^ 2 * (∑ i, (green h n i j) ^ 2) +
      ∑ i : Fin n, (green h n i.succ j - green h n i.castSucc j) ^ 2 = green h n j j := by
  have hs := green_mulVec_solve h hh n (Pi.single j 1)
  have hd := congrArg (dotProduct (fun i => green h n i j)) hs
  simp only [Matrix.mulVec_single_one, dotProduct_single, mul_one] at hd
  change dotProduct (fun i => green h n i j)
    (shiftedPath h n *ᵥ (fun i => green h n i j)) = green h n j j at hd
  rwa [shiftedPath_energy] at hd

def columnAverage (h : ℝ) (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) * h ^ 2)

theorem columnAverage_pos (h : ℝ) (hh : 0 < h) (n : ℕ) : 0 < columnAverage h n := by
  unfold columnAverage
  positivity

theorem green_gradient_energy (h : ℝ) (hh : 0 < h) (n : ℕ) (j : Fin (n + 1)) :
    ∑ i : Fin n, (green h n i.succ j - green h n i.castSucc j) ^ 2 ≤
      green h n j j - columnAverage h n := by
  let S := ∑ i, green h n i j
  let Q := ∑ i, (green h n i j) ^ 2
  let D := ∑ i : Fin n, (green h n i.succ j - green h n i.castSucc j) ^ 2
  have hmass : h ^ 2 * S = 1 := green_column_mass h hh n j
  have henergy : h ^ 2 * Q + D = green h n j j := green_column_energy h hh n j
  have hc : S ^ 2 ≤ (n + 1 : ℕ) * Q := by
    simpa [S, Q] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin (n + 1) => (1 : ℝ)) (fun i => green h n i j)
  have hcscaled := mul_le_mul_of_nonneg_left hc (sq_nonneg (h ^ 2))
  have hmass2 : (h ^ 2) ^ 2 * S ^ 2 = 1 := by
    calc
      _ = (h ^ 2 * S) ^ 2 := by ring
      _ = 1 := by rw [hmass]; norm_num
  have hden : 0 < (n + 1 : ℕ) * h ^ 2 := by positivity
  have havg : ((n + 1 : ℕ) * h ^ 2) * columnAverage h n = 1 := by
    unfold columnAverage
    exact mul_one_div_cancel hden.ne'
  apply (mul_le_mul_left hden).mp
  change ((n + 1 : ℕ) * h ^ 2) * D ≤ ((n + 1 : ℕ) * h ^ 2) *
    (green h n j j - columnAverage h n)
  have he := congrArg (fun t : ℝ => ((n + 1 : ℕ) * h ^ 2) * t) henergy
  dsimp only at he
  have hvariance : 1 ≤ ((n + 1 : ℕ) * h ^ 2) * (h ^ 2 * Q) := by
    nlinarith only [hcscaled, hmass2]
  calc
    _ = ((n + 1 : ℕ) * h ^ 2) * green h n j j -
      ((n + 1 : ℕ) * h ^ 2) * (h ^ 2 * Q) := by nlinarith only [he]
    _ ≤ ((n + 1 : ℕ) * h ^ 2) * green h n j j - 1 := sub_le_sub_left hvariance _
    _ = _ := by nlinarith only [havg]

theorem green_entry_average_lower (h : ℝ) (hh : 0 < h) (n : ℕ) (hn : 0 < n)
    (i j : Fin (n + 1)) : columnAverage h n - n / 4 ≤ green h n i j := by
  have hg := path_difference_sq_bound n (fun k => green h n k j) j i
  have he := mul_le_mul_of_nonneg_left (green_gradient_energy h hh n j) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hgap := hg.trans he
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (mul_le_mul_left hn').mp
  nlinarith only [hgap, sq_nonneg (green h n j j - green h n i j - (n : ℝ) / 2)]

theorem green_diag_average_upper (h : ℝ) (hh : 0 < h) (n : ℕ) (j : Fin (n + 1)) :
    green h n j j ≤ columnAverage h n + n := by
  let v : Fin (n + 1) → ℝ := fun k => green h n k j
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hmin : ∀ k, v m ≤ v k := fun k => hm k (Finset.mem_univ _)
  have hsum : (n + 1 : ℕ) * v m ≤ ∑ k, v k := by
    calc
      _ = ∑ _k : Fin (n + 1), v m := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k _ => hmin k)
  have hden : 0 < (n + 1 : ℕ) * h ^ 2 := by positivity
  have havg : ((n + 1 : ℕ) * h ^ 2) * columnAverage h n = 1 := by
    unfold columnAverage
    exact mul_one_div_cancel hden.ne'
  have hmavg : v m ≤ columnAverage h n := by
    have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg h)
    have hmass := green_column_mass h hh n j
    change h ^ 2 * (∑ k, v k) = 1 at hmass
    apply (mul_le_mul_left hden).mp
    nlinarith only [hmul, hmass, havg]
  have he := green_gradient_energy h hh n j
  have hsum0 : 0 ≤ ∑ i : Fin n, (green h n i.succ j - green h n i.castSucc j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hBavg : 0 ≤ green h n j j - columnAverage h n := hsum0.trans he
  have hg := path_difference_sq_bound n v j m
  have hhg := hg.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  have hsq : (green h n j j - columnAverage h n) ^ 2 ≤
      (green h n j j - v m) ^ 2 :=
    (sq_le_sq₀ hBavg (by linarith)).2 (by linarith)
  have hfinal := hsq.trans hhg
  by_contra hnot
  have ht : (n : ℝ) < green h n j j - columnAverage h n := by linarith
  have hpos : 0 < green h n j j - columnAverage h n := lt_of_le_of_lt (Nat.cast_nonneg n) ht
  have hp := mul_pos hpos (sub_pos.mpr ht)
  nlinarith only [hfinal, hp]

/-- The normalized inverse bounds in the article, obtained by energy and path
Cauchy–Schwarz rather than assuming the displayed exponential inverse formula.
The last two hypotheses are exactly the ceiling-scale inequalities. -/
theorem green_entry_bounds (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (n : ℕ) (hn : 0 < n) (hsize : 1 ≤ h * (n + 1 : ℕ)) (hsize' : h * n < 1)
    (i j : Fin (n + 1)) :
    1 / (9 * h) < green h n i j ∧ green h n i j ≤ 16 / h := by
  have hApos := columnAverage_pos h hh n
  have hden : 0 < (n + 1 : ℕ) * h ^ 2 := by positivity
  have havg : ((n + 1 : ℕ) * h ^ 2) * columnAverage h n = 1 := by
    unfold columnAverage
    exact mul_one_div_cancel hden.ne'
  have hprod : (h * (n + 1 : ℕ)) * (h * columnAverage h n) = 1 := by
    nlinarith only [havg]
  have hMupper : h * (n + 1 : ℕ) ≤ 5 / 4 := by
    push_cast
    nlinarith only [hsize', hhsmall]
  have hA_lower : (4 / 5 : ℝ) ≤ h * columnAverage h n := by
    have hm := mul_le_mul_of_nonneg_right hMupper (mul_nonneg hh.le hApos.le)
    nlinarith only [hm, hprod]
  have hA_upper : h * columnAverage h n ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hsize (mul_nonneg hh.le hApos.le)
    nlinarith only [hm, hprod]
  constructor
  · have hentry := mul_le_mul_of_nonneg_left (green_entry_average_lower h hh n hn i j) hh.le
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 9 * h)).mpr
    nlinarith only [hentry, hA_lower, hsize']
  · have hdiag := mul_le_mul_of_nonneg_left (green_diag_average_upper h hh n j) hh.le
    have hentry := mul_le_mul_of_nonneg_left (green_column_max h hh n j i) hh.le
    apply (le_div_iff₀ hh).mpr
    nlinarith only [hdiag, hentry, hA_upper, hsize']

def pathSize (h : ℝ) : ℕ := ⌈h⁻¹⌉₊
def pathEdges (h : ℝ) : ℕ := pathSize h - 1

theorem ceiling_scale (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4) :
    pathEdges h + 1 = pathSize h ∧ 0 < pathEdges h ∧
      1 ≤ h * (pathEdges h + 1 : ℕ) ∧ h * pathEdges h < 1 := by
  have hinv : (4 : ℝ) ≤ h⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hh).mpr
    linarith
  have hceil : h⁻¹ ≤ (pathSize h : ℝ) := Nat.le_ceil _
  have hMreal : (4 : ℝ) ≤ pathSize h := hinv.trans hceil
  have hM : 4 ≤ pathSize h := by exact_mod_cast hMreal
  have hE : pathEdges h + 1 = pathSize h := Nat.sub_add_cancel (by omega)
  have hEn : 0 < pathEdges h := by unfold pathEdges; omega
  refine ⟨hE, hEn, ?_, ?_⟩
  · rw [hE]
    have hm := mul_le_mul_of_nonneg_left hceil hh.le
    simpa [mul_inv_cancel₀ hh.ne'] using hm
  · have hc : (pathSize h : ℝ) < h⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.mpr hh.le)
    have hm := mul_lt_mul_of_pos_left hc hh
    have hEc : (pathEdges h : ℝ) + 1 = pathSize h := by exact_mod_cast hE
    have hprod : h * h⁻¹ = 1 := mul_inv_cancel₀ hh.ne'
    rw [← hEc] at hm
    nlinarith only [hm, hprod]

theorem green_entry_bounds_ceil (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (i j : Fin (pathEdges h + 1)) :
    1 / (9 * h) < green h (pathEdges h) i j ∧ green h (pathEdges h) i j ≤ 16 / h := by
  obtain ⟨_, hn, hsize, hsize'⟩ := ceiling_scale h hh hhsmall
  exact green_entry_bounds h hh hhsmall (pathEdges h) hn hsize hsize' i j

theorem pathMatrix_posDef (L h : ℝ) (hL : 0 < L) (hh : 0 < h) (n : ℕ) :
    (pathMatrix L h n).PosDef := by
  have hs := shiftedPath_posDef h hh n
  constructor
  · change (L • shiftedPath h n)ᴴ = L • shiftedPath h n
    have ht : (shiftedPath h n)ᵀ = shiftedPath h n := by
      simpa [Matrix.conjTranspose] using hs.isHermitian.eq
    simp [ht]
  · intro v hv
    simp only [pathMatrix, Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_pos hL (hs.2 v hv)

theorem pathMatrix_inverse (L h : ℝ) (hL : 0 < L) (hh : 0 < h) (n : ℕ) :
    (pathMatrix L h n)⁻¹ = L⁻¹ • green h n := by
  apply Matrix.inv_eq_left_inv
  simp [pathMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    green_shiftedPath h hh n, inv_mul_cancel₀ hL.ne', mul_inv_cancel₀ hL.ne']

/-- Actual scaled inverse, with the exact constants of `ana:lem:green` and
dimension `pathEdges h + 1 = ceil(1/h)` from `ceiling_scale`. -/
theorem pathMatrix_inverse_bounds (L h : ℝ) (hL : 0 < L) (hh : 0 < h)
    (hhsmall : h ≤ 1 / 4) (i j : Fin (pathEdges h + 1)) :
    1 / (9 * L * h) < (pathMatrix L h (pathEdges h))⁻¹ i j ∧
      (pathMatrix L h (pathEdges h))⁻¹ i j ≤ 16 / (L * h) := by
  rw [pathMatrix_inverse L h hL hh]
  change 1 / (9 * L * h) < L⁻¹ * green h (pathEdges h) i j ∧
    L⁻¹ * green h (pathEdges h) i j ≤ 16 / (L * h)
  obtain ⟨hl, hu⟩ := green_entry_bounds_ceil h hh hhsmall i j
  have heq₁ : L⁻¹ * (1 / (9 * h)) = 1 / (9 * L * h) := by
    field_simp
    ring
  have heq₂ : L⁻¹ * (16 / h) = 16 / (L * h) := by
    field_simp
  constructor
  · rw [← heq₁]
    exact mul_lt_mul_of_pos_left hl (inv_pos.mpr hL)
  · rw [← heq₂]
    exact mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hL.le)

theorem laplacian_energy_upper (n : ℕ) (v : Fin (n + 1) → ℝ) :
    dotProduct v (laplacian n *ᵥ v) ≤ 4 * ∑ i, (v i) ^ 2 := by
  rw [laplacian_energy]
  have hpoint : ∀ i : Fin n, (v i.succ - v i.castSucc) ^ 2 ≤
      2 * (v i.succ) ^ 2 + 2 * (v i.castSucc) ^ 2 := by
    intro i
    nlinarith [sq_nonneg (v i.succ + v i.castSucc)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hleft : (∑ i : Fin n, (v i.castSucc) ^ 2) ≤ ∑ i, (v i) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hright : (∑ i : Fin n, (v i.succ) ^ 2) ≤ ∑ i, (v i) ^ 2 := by
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg _)
  linarith

/-- A conservative quadratic-form upper estimate. The manuscript's sharper
`4 L` operator bound is not claimed by this lemma. -/
theorem pathMatrix_energy_bounds (L h : ℝ) (hL : 0 ≤ L) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    L * h ^ 2 * (∑ i, (v i) ^ 2) ≤ dotProduct v (pathMatrix L h n *ᵥ v) ∧
    dotProduct v (pathMatrix L h n *ᵥ v) ≤ L * (h ^ 2 + 4) * (∑ i, (v i) ^ 2) := by
  simp only [pathMatrix, Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
  constructor
  · have hl := mul_le_mul_of_nonneg_left (shiftedPath_coercive h n v) hL
    nlinarith only [hl]
  · have hu := laplacian_energy_upper n v
    have he := shiftedPath_energy h n v
    have hu' : dotProduct v (shiftedPath h n *ᵥ v) ≤ (h ^ 2 + 4) * ∑ i, (v i) ^ 2 := by
      rw [laplacian_energy] at hu
      nlinarith only [hu, he]
    have hl := mul_le_mul_of_nonneg_left hu' hL
    nlinarith only [hl]

def suffixSet (n : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => (n + 2) / 2 ≤ i.val + 1)

theorem last_mem_suffix (n : ℕ) : Fin.last n ∈ suffixSet n := by
  simp only [suffixSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last]
  omega

theorem suffix_card_pos (n : ℕ) : 0 < (suffixSet n).card :=
  Finset.card_pos.mpr ⟨Fin.last n, last_mem_suffix n⟩

def suffixFunction (A : ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => if i ∈ suffixSet n then A / Real.sqrt ((suffixSet n).card : ℝ) else 0

def suffixVector (A : ℝ) (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 _).symm (suffixFunction A n)

def entryVector (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 _).symm (Pi.single 0 1)

theorem suffixFunction_nonneg (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ suffixFunction A n i := by
  unfold suffixFunction
  split_ifs
  · exact div_nonneg hA (Real.sqrt_nonneg _)
  · exact le_refl _

theorem suffixFunction_last_pos (A : ℝ) (hA : 0 < A) (n : ℕ) :
    0 < suffixFunction A n (Fin.last n) := by
  rw [suffixFunction, if_pos (last_mem_suffix n)]
  apply div_pos hA
  exact Real.sqrt_pos.mpr (by exact_mod_cast suffix_card_pos n)

theorem suffixFunction_ne_zero (A : ℝ) (hA : 0 < A) (n : ℕ) :
    suffixFunction A n ≠ 0 := by
  intro heq
  have hp := suffixFunction_last_pos A hA n
  rw [heq] at hp
  exact (lt_irrefl 0) hp

theorem suffixVector_norm (A : ℝ) (hA : 0 ≤ A) (n : ℕ) : ‖suffixVector A n‖ = A := by
  have hs : (0 : ℝ) < (suffixSet n).card := by exact_mod_cast suffix_card_pos n
  have hsqrt : Real.sqrt ((suffixSet n).card : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsum : (∑ i, (suffixFunction A n i) ^ 2) = A ^ 2 := by
    calc
      _ = ((suffixSet n).card : ℝ) * (A / Real.sqrt ((suffixSet n).card : ℝ)) ^ 2 := by
        simp [suffixFunction, Finset.sum_ite]
      _ = A ^ 2 := by
        rw [div_pow, Real.sq_sqrt hs.le]
        exact mul_div_cancel₀ (A ^ 2) hs.ne'
  apply (sq_eq_sq₀ (norm_nonneg _) hA).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simpa only [suffixVector, WithLp.equiv_symm_pi_apply, Real.norm_eq_abs, sq_abs] using hsum

theorem entryVector_norm (n : ℕ) : ‖entryVector n‖ = 1 := by
  simp [entryVector, PiLp.norm_eq_of_L2, Pi.single_apply]

theorem actual_alpha_pos (L h A : ℝ) (hL : 0 < L) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (hA : 0 < A) :
    0 < ⟪suffixVector A (pathEdges h),
      ((pathMatrix L h (pathEdges h))⁻¹).toEuclideanLin (entryVector (pathEdges h))⟫_ℝ := by
  let n := pathEdges h
  have hi (i j : Fin (n + 1)) : 0 < (pathMatrix L h n)⁻¹ i j :=
    (by positivity : (0 : ℝ) < 1 / (9 * L * h)).trans
      (pathMatrix_inverse_bounds L h hL hh hhsmall i j).1
  have hs : 0 < ∑ i : Fin (n + 1), (pathMatrix L h n)⁻¹ i 0 * suffixFunction A n i := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hi i 0).le (suffixFunction_nonneg A hA.le n i)
    · exact ⟨Fin.last n, Finset.mem_univ _, mul_pos (hi _ _) (suffixFunction_last_pos A hA n)⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change 0 < dotProduct (((pathMatrix L h n)⁻¹) *ᵥ (Pi.single 0 1)) (suffixFunction A n)
  rw [Matrix.mulVec_single_one]
  exact hs

theorem actual_beta_pos (L h A : ℝ) (hL : 0 < L) (hh : 0 < h) (hA : 0 < A) (n : ℕ) :
    0 < ⟪suffixVector A n, ((pathMatrix L h n)⁻¹).toEuclideanLin (suffixVector A n)⟫_ℝ := by
  have hp := (pathMatrix_posDef L h hL hh n).inv.2 (suffixFunction A n)
    (suffixFunction_ne_zero A hA n)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  exact hp

/-- The manuscript's actual finite-dimensional block data. Both inverse and
readouts are concrete; the positivity fields are proved from the path bounds. -/
def actualBlockGeometry (L h A : ℝ) (hL : 0 < L) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (hA : 0 < A) : BlockGeometry (EuclideanSpace ℝ (Fin (pathEdges h + 1))) where
  H := (pathMatrix L h (pathEdges h)).toEuclideanLin
  Hinv := ((pathMatrix L h (pathEdges h))⁻¹).toEuclideanLin
  inverse := by
    intro x
    ext i
    change ((pathMatrix L h (pathEdges h)) *ᵥ
      (((pathMatrix L h (pathEdges h))⁻¹) *ᵥ (fun j => x j))) i = x i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((pathMatrix_posDef L h hL hh (pathEdges h)).det_pos.ne'.isUnit), Matrix.one_mulVec]
  symmetric := by
    intro x y
    exact (Matrix.isHermitian_iff_isSymmetric.mp
      (pathMatrix_posDef L h hL hh (pathEdges h)).isHermitian x y).symm
  positive := by
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact (pathMatrix_posDef L h hL hh (pathEdges h)).posSemidef.2 _
  a := suffixVector A (pathEdges h)
  e := entryVector (pathEdges h)
  alpha_pos := actual_alpha_pos L h A hL hh hhsmall hA
  beta_pos := actual_beta_pos L h A hL hh hA (pathEdges h)

theorem actualBlockGeometry_coercive (L h A : ℝ) (hL : 0 < L) (hh : 0 < h)
    (hhsmall : h ≤ 1 / 4) (hA : 0 < A)
    (x : EuclideanSpace ℝ (Fin (pathEdges h + 1))) :
    (L * h ^ 2) * ‖x‖ ^ 2 ≤
      ⟪x, (actualBlockGeometry L h A hL hh hhsmall hA).H x⟫_ℝ := by
  rw [PiLp.norm_sq_eq_of_L2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa only [actualBlockGeometry, Real.norm_eq_abs, sq_abs] using
    (pathMatrix_energy_bounds L h hL.le (pathEdges h) (fun i => x i)).1

end MatchingBounds1005.PathGreen
