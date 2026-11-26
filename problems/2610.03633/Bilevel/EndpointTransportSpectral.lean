import Bilevel.EndpointTransportMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Quantitative quadratic-form bounds for the actual endpoint transport matrix.
The path-energy identity below is derived from its finite matrix entries.
-/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportMatrix

def quadratic (n : ℕ) (A : Matrix (Index n) (Index n) ℝ) (x : Index n → ℝ) : ℝ :=
  ∑ i, x i * A.mulVec x i

def edgeEnergy (n : ℕ) (z : Index n → ℝ) : ℝ :=
  ∑ i : Fin (n+1), (z i.succ - z i.castSucc)^2

def ends (n : ℕ) (z : Index n → ℝ) : ℝ := z 0 ^ 2 + z (Fin.last (n+1)) ^ 2

theorem previous_succ (n : ℕ) (i : Fin (n+1)) : previous i.succ = i.castSucc := by
  apply Fin.ext
  simp [previous]

theorem following_castSucc (n : ℕ) (i : Fin (n+1)) : following i.castSucc = i.succ := by
  apply Fin.ext
  simp only [following, Fin.coe_castSucc, Fin.val_succ]
  exact Nat.min_eq_left (by omega)

theorem left_squares (n : ℕ) (z : Index n → ℝ) :
    (∑ i : Fin (n+1), z i.castSucc ^ 2) =
      (∑ i : Index n, z i ^ 2) - z (Fin.last (n+1)) ^ 2 := by
  rw [Fin.sum_univ_castSucc (fun i : Index n => z i^2)]
  ring

theorem right_squares (n : ℕ) (z : Index n → ℝ) :
    (∑ i : Fin (n+1), z i.succ ^ 2) =
      (∑ i : Index n, z i ^ 2) - z 0 ^ 2 := by
  rw [Fin.sum_univ_succ (fun i : Index n => z i^2)]
  ring

theorem edgeEnergy_expand (n : ℕ) (z : Index n → ℝ) :
    edgeEnergy n z = 2 * (∑ i : Index n, z i ^ 2) - ends n z -
      2 * (∑ i : Fin (n+1), z i.castSucc * z i.succ) := by
  unfold edgeEnergy
  have he (i : Fin (n+1)) : (z i.succ - z i.castSucc)^2 =
      z i.castSucc^2 + z i.succ^2 - 2*(z i.castSucc*z i.succ) := by ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    left_squares, right_squares]
  unfold ends
  ring

theorem base_diagonal_sum (n : ℕ) (z : Index n → ℝ) :
    (∑ i : Index n, z i * (baseDiagonal n i * z i)) =
      2 * (∑ i : Index n, z i^2) - (1 - (n+1:ℝ)⁻¹) * ends n z := by
  have he (i : Fin n) : ¬endpoint i.castSucc.succ := by
    simp only [endpoint, Fin.val_succ, Fin.coe_castSucc]
    omega
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hint (i : Fin n) : i.succ.castSucc = i.castSucc.succ := rfl
  have h0 : (0 : Fin (n+1)).castSucc = (0 : Index n) := rfl
  simp only [hint, h0]
  simp only [baseDiagonal, he, if_false, endpoint, Fin.coe_castSucc, Fin.val_zero,
    Fin.val_last, true_or, or_true, if_true]
  have hsum : (∑ i : Fin n, z i.castSucc.succ * (2 * z i.castSucc.succ)) =
      2 * ∑ i : Fin n, z i.castSucc.succ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  have hfull : (∑ i : Index n, z i^2) =
      z 0^2 + (∑ i : Fin n, z i.castSucc.succ ^ 2) + z (Fin.last (n+1))^2 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    rfl
  rw [hfull]
  unfold ends
  ring

/-- The actual matrix quadratic form equals discrete path energy plus its
two endpoint springs. This identity is proved, not supplied as an assumption. -/
theorem base_quadratic_energy (n : ℕ) (z : Index n → ℝ) :
    quadratic n (baseMatrix n) z = edgeEnergy n z + ends n z / (n+1:ℝ) := by
  have hl : (∑ i : Index n, z i * (if i.val = 0 then 0 else z (previous i))) =
      ∑ i : Fin (n+1), z i.succ * z i.castSucc := by
    rw [Fin.sum_univ_succ]
    simp [previous_succ]
  have hr : (∑ i : Index n, z i * (if i.val = n+1 then 0 else z (following i))) =
      ∑ i : Fin (n+1), z i.castSucc * z i.succ := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last, if_true, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i.castSucc : Index n).val ≠ n+1 := by
      simp only [Fin.coe_castSucc]
      omega
    simp only [if_neg hi, following_castSucc]
  unfold quadratic
  simp_rw [base_mulVec, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hl, hr, base_diagonal_sum,
    edgeEnergy_expand]
  have hc : (∑ i : Fin (n+1), z i.succ * z i.castSucc) =
      ∑ i : Fin (n+1), z i.castSucc * z i.succ := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  ring

theorem scaled_quadratic (n : ℕ) (z : Index n → ℝ) :
    quadratic n (matrix n) (fun i => scale n i * z i) =
      quadratic n (baseMatrix n) z := by
  unfold quadratic
  apply Finset.sum_congr rfl
  intro i _
  rw [matrix_mul_scaled]
  have hs := (scale_pos n i).ne'
  field_simp
  ring

theorem scaled_norm_sq (n : ℕ) (z : Index n → ℝ) :
    (∑ i : Index n, (scale n i * z i)^2) =
      (n+1:ℝ) * ends n z + ∑ i : Fin n, z i.castSucc.succ^2 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hint (i : Fin n) : i.succ.castSucc = i.castSucc.succ := rfl
  have h0 : (0 : Fin (n+1)).castSucc = (0 : Index n) := rfl
  have he (i : Fin n) : ¬endpoint i.castSucc.succ := by
    simp only [endpoint, Fin.val_succ, Fin.coe_castSucc]
    omega
  simp only [hint, h0, scale, he, if_false, endpoint, Fin.coe_castSucc, Fin.val_zero,
    Fin.val_last, true_or, or_true, if_true, one_mul, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))]
  unfold ends
  ring

theorem prefix_difference_sq (f : ℕ → ℝ) (k : ℕ) :
    (f k - f 0)^2 ≤ (k:ℝ) * ∑ j ∈ Finset.range k, (f (j+1) - f j)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k)
    (fun _ => (1:ℝ)) (fun j => f (j+1)-f j)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Finset.sum_range_sub] at h
  exact h

/-- Every coordinate is controlled from both path endpoints. -/
theorem path_coordinate_bound (f : ℕ → ℝ) (m k : ℕ) (hkm : k ≤ m) :
    f k ^ 2 ≤ f 0 ^ 2 + f m ^ 2 + (m:ℝ) *
      ∑ j ∈ Finset.range m, (f (j+1)-f j)^2 := by
  have hpre := prefix_difference_sq f k
  have hpreSum : (∑ j ∈ Finset.range k, (f (j+1)-f j)^2) ≤
      ∑ j ∈ Finset.range m, (f (j+1)-f j)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkm)
      (fun j _ _ => sq_nonneg _)
  have hpre' := hpre.trans (mul_le_mul_of_nonneg_left hpreSum (by positivity : (0:ℝ) ≤ k))
  have hsuf := prefix_difference_sq (fun j => f (k+j)) (m-k)
  have hsplit := Finset.sum_range_add (fun j => (f (j+1)-f j)^2) k (m-k)
  rw [Nat.add_sub_of_le hkm] at hsplit
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range k, (f (j+1)-f j)^2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hsufSum : (∑ j ∈ Finset.range (m-k), (f (k+j+1)-f (k+j))^2) ≤
      ∑ j ∈ Finset.range m, (f (j+1)-f j)^2 := by linarith
  simp only [Nat.add_sub_of_le hkm, Nat.add_zero, ← Nat.add_assoc] at hsuf
  have hsuf' := hsuf.trans (mul_le_mul_of_nonneg_left hsufSum
    (by positivity : (0:ℝ) ≤ (m-k:ℕ)))
  rw [Nat.cast_sub hkm] at hsuf'
  nlinarith [sq_nonneg (f k - 2*f 0), sq_nonneg (f k - 2*f m)]

def path (n : ℕ) (z : Index n → ℝ) (k : ℕ) : ℝ :=
  z ⟨min k (n+1), by omega⟩

theorem path_at (n : ℕ) (z : Index n → ℝ) (i : Index n) : path n z i.val = z i := by
  unfold path
  congr 1
  apply Fin.ext
  simp only [Nat.min_eq_left (by omega : i.val ≤ n+1)]

theorem path_energy (n : ℕ) (z : Index n → ℝ) :
    (∑ j ∈ Finset.range (n+1), (path n z (j+1)-path n z j)^2) = edgeEnergy n z := by
  rw [← Fin.sum_univ_eq_sum_range]
  unfold edgeEnergy
  apply Finset.sum_congr rfl
  intro i _
  change (path n z i.succ.val-path n z i.castSucc.val)^2 = _
  rw [path_at, path_at]

theorem coordinate_energy_bound (n : ℕ) (z : Index n → ℝ) (i : Index n) :
    z i ^ 2 ≤ ends n z + (n+1:ℝ) * edgeEnergy n z := by
  have h := path_coordinate_bound (path n z) (n+1) i.val (by omega)
  rw [path_at, path_energy] at h
  have h0 : path n z 0 = z 0 := path_at n z 0
  have hl : path n z (n+1) = z (Fin.last (n+1)) := path_at n z (Fin.last (n+1))
  rw [h0, hl] at h
  simpa [ends] using h

theorem energy_nonneg (n : ℕ) (z : Index n → ℝ) : 0 ≤ edgeEnergy n z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem ends_nonneg (n : ℕ) (z : Index n → ℝ) : 0 ≤ ends n z := by
  unfold ends
  positivity

/-- This discrete estimate proves the manuscript's lower spectral constant
without assuming an eigenvalue estimate for the interior Dirichlet matrix. -/
theorem scaled_lower_spectral (n : ℕ) (z : Index n → ℝ) :
    (∑ i : Index n, (scale n i*z i)^2) ≤
      2*(n+1:ℝ)^2 * quadratic n (baseMatrix n) z := by
  rw [scaled_norm_sq, base_quadratic_energy]
  have hi : (∑ i : Fin n, z i.castSucc.succ^2) ≤
      (n:ℝ) * (ends n z + (n+1:ℝ) * edgeEnergy n z) := by
    calc
      _ ≤ ∑ _i : Fin n, (ends n z + (n+1:ℝ) * edgeEnergy n z) :=
        Finset.sum_le_sum (fun i _ => coordinate_energy_bound n z i.castSucc.succ)
      _ = _ := by simp; ring
  have hm : (n+1:ℝ) ≠ 0 := by positivity
  have hid : 2*(n+1:ℝ)^2 * (edgeEnergy n z + ends n z / (n+1:ℝ)) =
      2*(n+1:ℝ)^2 * edgeEnergy n z + 2*(n+1:ℝ)*ends n z := by
    field_simp
    ring
  rw [hid]
  have hE := energy_nonneg n z
  have hends := ends_nonneg n z
  have hprod : 0 ≤ ((n:ℝ)^2 + 3*n + 2) * edgeEnergy n z := by positivity
  nlinarith

theorem edgeEnergy_upper (n : ℕ) (z : Index n → ℝ) :
    edgeEnergy n z ≤ 4 * (∑ i : Index n, z i^2) - 2 * ends n z := by
  have hi (i : Fin (n+1)) : (z i.succ-z i.castSucc)^2 ≤
      2*z i.castSucc^2 + 2*z i.succ^2 := by
    nlinarith [sq_nonneg (z i.succ+z i.castSucc)]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) => hi i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    left_squares, right_squares] at h
  unfold edgeEnergy ends
  linarith

theorem scale_ge_one (n : ℕ) (i : Index n) : 1 ≤ scale n i := by
  unfold scale
  split
  · have hs := Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))
    have hp := Real.sqrt_nonneg (n+1:ℝ)
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · exact le_rfl

theorem squares_le_scaled (n : ℕ) (z : Index n → ℝ) :
    (∑ i : Index n, z i^2) ≤ ∑ i : Index n, (scale n i*z i)^2 := by
  apply Finset.sum_le_sum
  intro i _
  have hs := scale_ge_one n i
  have hs2 : 1 ≤ scale n i ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hs2 (sq_nonneg (z i))
  simpa [mul_pow] using hh

theorem scaled_upper_spectral (n : ℕ) (z : Index n → ℝ) :
    quadratic n (baseMatrix n) z ≤ 4 * ∑ i : Index n, (scale n i*z i)^2 := by
  rw [base_quadratic_energy]
  have hE := edgeEnergy_upper n z
  have hend := ends_nonneg n z
  have hm : 0 < (n+1:ℝ) := by positivity
  have hs : ends n z / (n+1:ℝ) ≤ ends n z := by
    apply (div_le_iff₀ hm).2
    have hn : 0 ≤ (n:ℝ) * ends n z := by positivity
    nlinarith
  have hnorm := mul_le_mul_of_nonneg_left (squares_le_scaled n z) (by norm_num : (0:ℝ) ≤ 4)
  linarith

/-- Both quantitative spectral inequalities for the actual finite matrix,
expressed as universally quantified real quadratic-form inequalities. -/
theorem quadratic_spectral_sandwich (n : ℕ) (x : Index n → ℝ) :
    1/(2*(n+1:ℝ)^2) * (∑ i : Index n, x i^2) ≤ quadratic n (matrix n) x ∧
      quadratic n (matrix n) x ≤ 4 * ∑ i : Index n, x i^2 := by
  let z := fun i => x i / scale n i
  have he : (fun i => scale n i*z i) = x := by
    funext i
    have hi := (scale_pos n i).ne'
    dsimp [z]
    field_simp
  rw [← he, scaled_quadratic]
  constructor
  · have hl := scaled_lower_spectral n z
    have hb : (∑ i : Index n, (scale n i*z i)^2) / (2*(n+1:ℝ)^2) ≤
        quadratic n (baseMatrix n) z := by
      apply (div_le_iff₀ (by positivity : 0 < 2*(n+1:ℝ)^2)).2
      nlinarith
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hb
  · exact scaled_upper_spectral n z

/-- The same sandwich with the Euclidean norm made explicit. -/
theorem euclidean_spectral_sandwich (n : ℕ) (x : EuclideanSpace ℝ (Index n)) :
    1/(2*(n+1:ℝ)^2) * ‖x‖^2 ≤ quadratic n (matrix n) (fun i => x i) ∧
      quadratic n (matrix n) (fun i => x i) ≤ 4 * ‖x‖^2 := by
  have hn : ‖x‖^2 = ∑ i : Index n, x i^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hn]
  exact quadratic_spectral_sandwich n (fun i => x i)

/-- The manuscript's Loewner sandwich as two genuine positive-semidefinite
matrix statements, including their Hermitian requirements. -/
theorem spectral_sandwich (n : ℕ) :
    (matrix n - (1/(2*(n+1:ℝ)^2)) • (1 : Matrix (Index n) (Index n) ℝ)).PosSemidef ∧
      ((4:ℝ) • (1 : Matrix (Index n) (Index n) ℝ) - matrix n).PosSemidef := by
  have hA : (matrix n).conjTranspose = matrix n := by
    ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using
      congrArg (fun A : Matrix (Index n) (Index n) ℝ => A i j) (matrix_symmetric n)
  constructor
  · constructor
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA,
        Matrix.conjTranspose_one, star_trivial]
    · intro x
      have h := sub_nonneg.mpr (quadratic_spectral_sandwich n x).1
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, star_trivial]
      simpa [quadratic, dotProduct, pow_two] using h
  · constructor
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA,
        Matrix.conjTranspose_one, star_trivial]
    · intro x
      have h := sub_nonneg.mpr (quadratic_spectral_sandwich n x).2
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, star_trivial]
      simpa [quadratic, dotProduct, pow_two] using h

end Bilevel.EndpointTransportMatrix
