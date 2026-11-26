import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# The endpoint-amplified tridiagonal matrix

This is the actual finite matrix in `tr:lem:matrix` of the chi-refinement.
The parameter `n` counts interior coordinates, so the manuscript's matrix
size is `n+2` and its `m` is `n+1`. The matrix is defined by a diagonally
rescaled path Laplacian with endpoint springs. No inverse entries are assumed.
-/

noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportMatrix

abbrev Index (n : ℕ) := Fin (n + 2)

def previous {n : ℕ} (i : Index n) : Index n :=
  ⟨i.val - 1, by omega⟩

def following {n : ℕ} (i : Index n) : Index n :=
  ⟨min (i.val + 1) (n + 1), by omega⟩

abbrev endpoint {n : ℕ} (i : Index n) : Prop := i.val = 0 ∨ i.val = n + 1

def scale (n : ℕ) (i : Index n) : ℝ :=
  if endpoint i then Real.sqrt (n + 1) else 1

def baseDiagonal (n : ℕ) (i : Index n) : ℝ :=
  if endpoint i then 1 + (n + 1 : ℝ)⁻¹ else 2

def baseMatrix (n : ℕ) : Matrix (Index n) (Index n) ℝ := fun i j =>
  (if j = i then baseDiagonal n i else 0) -
    (if i.val = 0 then 0 else if j = previous i then 1 else 0) -
    (if i.val = n + 1 then 0 else if j = following i then 1 else 0)

def matrix (n : ℕ) : Matrix (Index n) (Index n) ℝ := fun i j =>
  baseMatrix n i j / (scale n i * scale n j)

def affineColumn (n : ℕ) (i : Index n) : ℝ :=
  Real.sqrt (n + 1) * ((n + 1 : ℝ) + i.val) / 3

def endpointColumn (n : ℕ) (i : Index n) : ℝ :=
  scale n i * affineColumn n i

def lastUnit (n : ℕ) (i : Index n) : ℝ :=
  if i.val = n + 1 then 1 else 0

theorem scale_pos (n : ℕ) (i : Index n) : 0 < scale n i := by
  unfold scale
  split
  · exact Real.sqrt_pos.2 (by positivity)
  · norm_num

theorem base_mulVec (n : ℕ) (x : Index n → ℝ) (i : Index n) :
    (baseMatrix n).mulVec x i = baseDiagonal n i * x i -
      (if i.val = 0 then 0 else x (previous i)) -
      (if i.val = n + 1 then 0 else x (following i)) := by
  unfold Matrix.mulVec dotProduct baseMatrix
  simp only [sub_mul, Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h0 : i.val = 0 <;> by_cases hl : i.val = n + 1 <;> simp [h0, hl]

theorem baseMatrix_diagonal (n : ℕ) (i : Index n) :
    baseMatrix n i i = baseDiagonal n i := by
  have hp : i.val ≠ 0 → i ≠ previous i := by
    intro h he
    have hh := congrArg Fin.val he
    simp only [previous] at hh
    omega
  have hf : i.val ≠ n+1 → i ≠ following i := by
    intro h he
    have hh := congrArg Fin.val he
    simp only [following] at hh
    omega
  by_cases h0 : i.val = 0 <;> by_cases hl : i.val = n+1 <;>
    simp [baseMatrix, h0, hl, hp, hf]

theorem matrix_diagonal_endpoint (n : ℕ) (i : Index n) (hi : endpoint i) :
    matrix n i i = ((n+1:ℝ)+1)/(n+1:ℝ)^2 := by
  simp only [matrix, baseMatrix_diagonal, baseDiagonal, scale, hi, if_true]
  rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))]
  have hm : (n+1:ℝ) ≠ 0 := by positivity
  field_simp only [hm]
  ring

theorem matrix_diagonal_interior (n : ℕ) (i : Index n) (hi : ¬endpoint i) :
    matrix n i i = 2 := by
  simp [matrix, baseMatrix_diagonal, baseDiagonal, scale, hi]

theorem baseMatrix_adjacent (n : ℕ) (i j : Index n) (hij : i.val+1 = j.val) :
    baseMatrix n i j = -1 := by
  have hne : j ≠ i := by intro h; have := congrArg Fin.val h; omega
  have hnp : j ≠ previous i := by
    intro h
    have := congrArg Fin.val h
    simp only [previous] at this
    omega
  have hlast : i.val ≠ n+1 := by omega
  have hnext : j = following i := by
    apply Fin.ext
    simp only [following]
    omega
  simp only [baseMatrix, if_neg hne, if_neg hnp, if_neg hlast, if_pos hnext]
  split <;> norm_num

theorem matrix_adjacent (n : ℕ) (i j : Index n) (hij : i.val+1 = j.val) :
    matrix n i j = -(scale n i * scale n j)⁻¹ := by
  simp [matrix, baseMatrix_adjacent n i j hij, div_eq_mul_inv]

theorem baseMatrix_adjacent_reverse (n : ℕ) (i j : Index n) (hij : j.val+1 = i.val) :
    baseMatrix n i j = -1 := by
  have hne : j ≠ i := by intro h; have := congrArg Fin.val h; omega
  have hp : j = previous i := by
    apply Fin.ext
    simp only [previous]
    omega
  have h0 : i.val ≠ 0 := by omega
  have hnf : j ≠ following i := by
    intro h
    have := congrArg Fin.val h
    simp only [following] at this
    omega
  simp only [baseMatrix, if_neg hne, if_neg h0, if_pos hp, if_neg hnf]
  split <;> norm_num

theorem baseMatrix_zero (n : ℕ) (i j : Index n)
    (hne : j ≠ i) (hf : i.val+1 ≠ j.val) (hp : j.val+1 ≠ i.val) :
    baseMatrix n i j = 0 := by
  have hnp : i.val ≠ 0 → j ≠ previous i := by
    intro h0 he
    have := congrArg Fin.val he
    simp only [previous] at this
    omega
  have hnf : i.val ≠ n+1 → j ≠ following i := by
    intro hl he
    have := congrArg Fin.val he
    simp only [following] at this
    omega
  by_cases h0 : i.val = 0 <;> by_cases hl : i.val = n+1 <;>
    simp [baseMatrix, hne, h0, hl, hnp, hnf]

theorem matrix_symmetric (n : ℕ) : (matrix n).transpose = matrix n := by
  ext i j
  by_cases he : i = j
  · subst j
    rfl
  by_cases hf : i.val+1 = j.val
  · simp only [Matrix.transpose_apply, matrix, baseMatrix_adjacent n i j hf,
      baseMatrix_adjacent_reverse n j i hf]
    rw [mul_comm]
  by_cases hp : j.val+1 = i.val
  · simp only [Matrix.transpose_apply, matrix, baseMatrix_adjacent n j i hp,
      baseMatrix_adjacent_reverse n i j hp]
    rw [mul_comm]
  · simp only [Matrix.transpose_apply, matrix,
      baseMatrix_zero n i j (Ne.symm he) hf hp, baseMatrix_zero n j i he hp hf, zero_div]

theorem matrix_adjacent_interior (n : ℕ) (i j : Index n) (hij : i.val+1 = j.val)
    (hi : ¬endpoint i) (hj : ¬endpoint j) : matrix n i j = -1 := by
  simp [matrix_adjacent n i j hij, scale, hi, hj]

theorem matrix_adjacent_endpoint (n : ℕ) (hn : 1 ≤ n) (i j : Index n)
    (hij : i.val+1 = j.val) (he : endpoint i ∨ endpoint j) :
    matrix n i j = -(Real.sqrt (n+1))⁻¹ := by
  rw [matrix_adjacent n i j hij]
  rcases he with (hi | hi) | (hj | hj)
  · have hj0 : j.val ≠ 0 := by omega
    have hjl : j.val ≠ n+1 := by omega
    simp [scale, endpoint, hi, hj0, hjl]
  · omega
  · omega
  · have hi0 : i.val ≠ 0 := by omega
    have hil : i.val ≠ n+1 := by omega
    simp [scale, endpoint, hj, hi0, hil]

/-- Diagonal rescaling cancels the column scaling in the actual matrix product. -/
theorem matrix_mul_scaled (n : ℕ) (x : Index n → ℝ) (i : Index n) :
    (matrix n).mulVec (fun j => scale n j * x j) i =
      (baseMatrix n).mulVec x i / scale n i := by
  unfold Matrix.mulVec dotProduct matrix
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hi := (scale_pos n i).ne'
  have hj := (scale_pos n j).ne'
  field_simp
  ring

theorem base_affine_column (n : ℕ) (i : Index n) :
    (baseMatrix n).mulVec (affineColumn n) i =
      if i.val = n + 1 then Real.sqrt (n + 1) else 0 := by
  rw [base_mulVec]
  have hm : (n + 1 : ℝ) ≠ 0 := by positivity
  by_cases h0 : i.val = 0
  · have hl : i.val ≠ n + 1 := by omega
    have hf : (following i).val = 1 := by simp [following, h0]
    simp only [baseDiagonal, endpoint, h0, true_or, if_true, hl, if_false,
      affineColumn, hf, Nat.cast_zero, Nat.cast_one, add_zero, sub_zero]
    field_simp
    ring
  · by_cases hl : i.val = n + 1
    · have hp : (previous i).val = n := by simp [previous, hl]
      simp only [baseDiagonal, endpoint, hl, or_true, if_true, h0, if_false,
        affineColumn, hp, Nat.cast_add, Nat.cast_one, sub_zero]
      field_simp
      ring
    · have hip : 0 < i.val := by omega
      have hin : i.val < n + 1 := by omega
      have hp : ((previous i).val : ℝ) = (i.val : ℝ) - 1 := by
        simp [previous, Nat.cast_sub (by omega : 1 ≤ i.val)]
      have hf : ((following i).val : ℝ) = (i.val : ℝ) + 1 := by
        simp [following, Nat.min_eq_left (by omega : i.val + 1 ≤ n + 1)]
      simp [baseDiagonal, endpoint, h0, hl, affineColumn, hp, hf]
      ring

/-- The proposed endpoint inverse column solves the actual finite linear system. -/
theorem matrix_endpointColumn (n : ℕ) :
    (matrix n).mulVec (endpointColumn n) = lastUnit n := by
  funext i
  change (matrix n).mulVec (fun j => scale n j * affineColumn n j) i = _
  rw [matrix_mul_scaled, base_affine_column]
  by_cases hl : i.val = n + 1
  · simp [scale, endpoint, lastUnit, hl, (Real.sqrt_pos.2 (by positivity : 0 < (n + 1 : ℝ))).ne']
  · simp [lastUnit, hl]

/-- Discrete harmonicity and the first endpoint spring force an affine kernel
vector. The final endpoint spring then forces that affine vector to vanish. -/
theorem base_kernel_eq_zero (n : ℕ) (x : Index n → ℝ)
    (hx : (baseMatrix n).mulVec x = 0) : x = 0 := by
  have hm : (n+1:ℝ) ≠ 0 := by positivity
  have ha : ∀ k (hk : k < n+2),
      x ⟨k,hk⟩ = (1 + (k:ℝ)/(n+1:ℝ)) * x 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        simp
      by_cases hk1 : k = 1
      · subst k
        have hr := congrFun hx (0 : Index n)
        rw [base_mulVec] at hr
        have hf : following (0 : Index n) = (⟨1,hk⟩ : Index n) := by
          apply Fin.ext
          simp [following]
        simp [baseDiagonal, endpoint, hf] at hr
        simp only [Nat.cast_one, one_div]
        have hi : (⟨1,hk⟩ : Index n) = 1 := by
          apply Fin.ext
          simp
        rw [hi]
        linarith
      · have hkprev : k-1 < n+2 := by omega
        have hkprev2 : k-2 < n+2 := by omega
        have hp0 : (⟨k-1,hkprev⟩ : Index n).val ≠ 0 := by simp only; omega
        have hpl : (⟨k-1,hkprev⟩ : Index n).val ≠ n+1 := by simp only; omega
        have hp : previous (⟨k-1,hkprev⟩ : Index n) = ⟨k-2,hkprev2⟩ := by
          apply Fin.ext
          simp only [previous]
          omega
        have hf : following (⟨k-1,hkprev⟩ : Index n) = ⟨k,hk⟩ := by
          apply Fin.ext
          simp only [following]
          omega
        have hr := congrFun hx (⟨k-1,hkprev⟩ : Index n)
        rw [base_mulVec] at hr
        simp only [baseDiagonal, endpoint, hp0, hpl, false_or, if_false,
          hp, hf, Pi.zero_apply] at hr
        rw [ih (k-1) (by omega) hkprev, ih (k-2) (by omega) hkprev2] at hr
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)] at hr
        norm_num at hr
        field_simp only [hm] at hr ⊢
        nlinarith
  have hr := congrFun hx (Fin.last (n+1))
  rw [base_mulVec] at hr
  have hp : previous (Fin.last (n+1)) = (⟨n,by omega⟩ : Index n) := by
    apply Fin.ext
    simp [previous]
  simp only [baseDiagonal, endpoint, Fin.val_last, or_true, if_true, hp,
    show n+1 ≠ 0 by omega, if_false, sub_zero, Pi.zero_apply] at hr
  change (1 + (n+1:ℝ)⁻¹) * x (⟨n+1,by omega⟩ : Index n) -
    x (⟨n,by omega⟩ : Index n) = 0 at hr
  rw [ha (n+1) (by omega), ha n (by omega)] at hr
  have hx0 : x 0 = 0 := by
    field_simp at hr
    nlinarith
  funext i
  rw [ha i.val i.isLt, hx0, mul_zero]
  rfl

theorem matrix_kernel_eq_zero (n : ℕ) (x : Index n → ℝ)
    (hx : (matrix n).mulVec x = 0) : x = 0 := by
  let z := fun i => x i / scale n i
  have hz : (baseMatrix n).mulVec z = 0 := by
    funext i
    have hr := matrix_mul_scaled n z i
    have he : (fun j => scale n j * z j) = x := by
      funext j
      dsimp [z]
      have hj := (scale_pos n j).ne'
      field_simp
    rw [he, hx, Pi.zero_apply] at hr
    exact (div_eq_zero_iff.mp hr.symm).resolve_right (scale_pos n i).ne'
  have hz0 := base_kernel_eq_zero n z hz
  funext i
  have hi := congrFun hz0 i
  dsimp [z] at hi
  exact (div_eq_zero_iff.mp hi).resolve_right (scale_pos n i).ne'

theorem matrix_mulVec_injective (n : ℕ) : Function.Injective (matrix n).mulVec := by
  intro x y hxy
  have hz : (matrix n).mulVec (x-y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (matrix_kernel_eq_zero n (x-y) hz)

theorem matrix_isUnit (n : ℕ) : IsUnit (matrix n) :=
  Matrix.mulVec_injective_iff_isUnit.mp (matrix_mulVec_injective n)

theorem lastUnit_eq_single (n : ℕ) : lastUnit n = Pi.single (Fin.last (n+1)) 1 := by
  funext i
  simp [lastUnit, Pi.single_apply, Fin.ext_iff, eq_comm]

/-- The endpoint column is now identified with the actual nonsingular inverse. -/
theorem inverse_last_column (n : ℕ) (i : Index n) :
    (matrix n)⁻¹ i (Fin.last (n+1)) = endpointColumn n i := by
  letI := (matrix_isUnit n).invertible
  have h := Matrix.inv_mulVec_eq_vec (matrix_endpointColumn n).symm
  rw [lastUnit_eq_single, Matrix.mulVec_single_one] at h
  exact congrFun h i

theorem endpointColumn_first (n : ℕ) :
    endpointColumn n 0 = (n + 1 : ℝ)^2 / 3 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))
  simp [endpointColumn, scale, endpoint, affineColumn]
  nlinarith

theorem endpointColumn_last (n : ℕ) :
    endpointColumn n (Fin.last (n + 1)) = 2 * (n + 1 : ℝ)^2 / 3 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))
  simp [endpointColumn, scale, endpoint, affineColumn]
  nlinarith

theorem endpointColumn_interior (n : ℕ) (i : Fin n) :
    endpointColumn n i.castSucc.succ =
      Real.sqrt (n + 1) * ((n + 1 : ℝ) + (i.val + 1 : ℕ)) / 3 := by
  have h0 : i.val + 1 ≠ 0 := by omega
  have hl : i.val + 1 ≠ n + 1 := by omega
  simp [endpointColumn, scale, endpoint, affineColumn, h0, hl, ne_of_lt i.isLt]

theorem inverse_last_last (n : ℕ) :
    (matrix n)⁻¹ (Fin.last (n+1)) (Fin.last (n+1)) = 2*(n+1:ℝ)^2/3 := by
  rw [inverse_last_column, endpointColumn_last]

theorem inverse_first_last (n : ℕ) :
    (matrix n)⁻¹ 0 (Fin.last (n+1)) = (n+1:ℝ)^2/3 := by
  rw [inverse_last_column, endpointColumn_first]

theorem inverse_interior_ratio (n : ℕ) (i : Fin n) :
    (matrix n)⁻¹ i.castSucc.succ (Fin.last (n+1)) / (2*(n+1:ℝ)^2/3) =
      ((n+1:ℝ)+(i.val+1:ℕ))/(2*(n+1:ℝ)*Real.sqrt (n+1)) := by
  rw [inverse_last_column, endpointColumn_interior]
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))
  have hp : 0 < Real.sqrt (n+1) := Real.sqrt_pos.2 (by positivity)
  have hm : (n+1:ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination 2*(n+1:ℝ)*((n+1:ℝ)+((i.val:ℝ)+1))*hs

theorem sum_affine_sq (a : ℝ) (n : ℕ) :
    (∑ i : Fin n, (a + (i.val : ℝ))^2) =
      n * a^2 + a * n * (n - 1) + n * (n - 1) * (2*n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- The squared Euclidean response norm is computed from every coordinate,
not merely the two amplified endpoints. -/
theorem endpointColumn_norm_sq (n : ℕ) :
    (∑ i : Index n, endpointColumn n i ^ 2) =
      (44 * (n+1:ℝ)^4 - 15 * (n+1:ℝ)^3 + (n+1:ℝ)^2) / 54 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hfirst : (0 : Fin (n+1)).castSucc = (0 : Index n) := rfl
  have hint (i : Fin n) : i.succ.castSucc = i.castSucc.succ := rfl
  simp only [hfirst, hint, endpointColumn_first, endpointColumn_last,
    endpointColumn_interior]
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))
  have hsum : (∑ i : Fin n,
      (Real.sqrt (n+1) * ((n+1:ℝ) + (i.val+1:ℕ)) / 3)^2) =
      (n+1:ℝ) / 9 * ∑ i : Fin n, ((n+2:ℝ) + (i.val:ℝ))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, mul_pow, hs]
    push_cast
    ring
  rw [hsum, sum_affine_sq]
  ring

/-- The normalized full-response squared norm is the exact gamma formula. -/
theorem normalized_norm_sq (n : ℕ) :
    (∑ i : Index n, endpointColumn n i ^ 2) / (2*(n+1:ℝ)^2/3)^2 =
      11/6 - 5/(8*(n+1:ℝ)) + 1/(24*(n+1:ℝ)^2) := by
  rw [endpointColumn_norm_sq]
  have hm : (n+1:ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem normalized_norm_bounds (n : ℕ) :
    5/4 ≤ (∑ i : Index n, endpointColumn n i ^ 2) / (2*(n+1:ℝ)^2/3)^2 ∧
      (∑ i : Index n, endpointColumn n i ^ 2) / (2*(n+1:ℝ)^2/3)^2 < 11/6 := by
  rw [normalized_norm_sq]
  have hm : (1:ℝ) ≤ n+1 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hp : 0 < (n+1:ℝ) := by positivity
  constructor
  · have hid : (11/6 - 5/(8*(n+1:ℝ)) + 1/(24*(n+1:ℝ)^2)) =
        (44*(n+1:ℝ)^2 - 15*(n+1:ℝ) + 1)/(24*(n+1:ℝ)^2) := by
      field_simp
      ring
    rw [hid]
    apply (le_div_iff₀ (by positivity : 0 < 24*(n+1:ℝ)^2)).2
    nlinarith [sq_nonneg ((n+1:ℝ)-1)]
  · have hid : (11/6 - 5/(8*(n+1:ℝ)) + 1/(24*(n+1:ℝ)^2)) =
        11/6 - (15*(n+1:ℝ)-1)/(24*(n+1:ℝ)^2) := by
      field_simp
      ring
    rw [hid]
    have hpos : 0 < (15*(n+1:ℝ)-1)/(24*(n+1:ℝ)^2) :=
      div_pos (by linarith) (by positivity)
    linarith

def euclideanColumn (n : ℕ) : EuclideanSpace ℝ (Index n) :=
  (WithLp.equiv 2 _).symm (endpointColumn n)

def gamma (n : ℕ) : ℝ := ‖euclideanColumn n‖ / (2*(n+1:ℝ)^2/3)

theorem euclideanColumn_norm_sq (n : ℕ) :
    ‖euclideanColumn n‖^2 = ∑ i : Index n, endpointColumn n i ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [euclideanColumn, Real.norm_eq_abs, sq_abs]

/-- The gamma in this statement uses the Euclidean norm, not the default
supremum norm on a function space. -/
theorem gamma_sq (n : ℕ) :
    gamma n ^ 2 = 11/6 - 5/(8*(n+1:ℝ)) + 1/(24*(n+1:ℝ)^2) := by
  rw [gamma, div_pow, euclideanColumn_norm_sq, normalized_norm_sq]

theorem gamma_sq_bounds (n : ℕ) : 5/4 ≤ gamma n ^ 2 ∧ gamma n ^ 2 < 11/6 := by
  rw [gamma, div_pow, euclideanColumn_norm_sq]
  exact normalized_norm_bounds n

end Bilevel.EndpointTransportMatrix
