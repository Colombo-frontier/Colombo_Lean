import Matvec.Simplex
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# A randomized Walsh testing basis

This is an alternative to the manuscript's Haar basis. The dimension is `2^k`.
Multiplying a normalized Walsh matrix by an independent random sign diagonal
preserves orthogonality and gives subgaussian projections for every fixed
direction. Restricting the hard core to dyadic dimensions and then padding
loses only a universal factor in the final lower bound.
-/

namespace Matvec
namespace RandomOrthogonal

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open scoped Classical
noncomputable section

def sign (b : Bool) : ℝ := if b then 1 else -1

theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

abbrev Cube (k : ℕ) := Fin k → Bool

/-- A Walsh character pairing, with unnormalized entries in `{−1,1}`. -/
def walsh (k : ℕ) : Matrix (Cube k) (Cube k) ℝ :=
  fun x y => ∏ i, (if x i && y i then -1 else 1)

theorem walsh_sq (k : ℕ) (x y : Cube k) : walsh k x y ^ 2 = 1 := by
  unfold walsh
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  split_ifs <;> norm_num

theorem walsh_symmetric (k : ℕ) : (walsh k).transpose = walsh k := by
  ext x y
  simp only [Matrix.transpose_apply, walsh, Bool.and_comm]

theorem walsh_row_inner (k : ℕ) (x y : Cube k) :
    ∑ z, walsh k x z * walsh k y z = if x = y then (2 : ℝ) ^ k else 0 := by
  classical
  have hfactor (i : Fin k) :
      (∑ b : Bool, (if x i && b then (-1 : ℝ) else 1) *
        (if y i && b then (-1 : ℝ) else 1)) = if x i = y i then 2 else 0 := by
    cases hx : x i <;> cases hy : y i <;> norm_num [hx, hy]
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin k) (b : Bool) =>
    (if x i && b then (-1 : ℝ) else 1) * (if y i && b then (-1 : ℝ) else 1))]
  simp_rw [hfactor]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem cube_card (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by
  simp [Cube, Fintype.card_fun]

theorem walsh_gram (k : ℕ) :
    walsh k * (walsh k).transpose = (2 ^ k : ℝ) • (1 : Matrix (Cube k) (Cube k) ℝ) := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, walsh_row_inner, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp

/-- The actual testing basis, random only through a sign vector. -/
def testingBasis (k : ℕ) (σ : Cube k → Bool) : Matrix (Cube k) (Cube k) ℝ :=
  fun i j => (Real.sqrt (2 ^ k : ℝ))⁻¹ * sign (σ i) * walsh k i j

theorem testingBasis_orthogonal (k : ℕ) (σ : Cube k → Bool) :
    testingBasis k σ * (testingBasis k σ).transpose = 1 := by
  classical
  have hp : 0 < (2 ^ k : ℝ) := by positivity
  have hs : Real.sqrt (2 ^ k : ℝ) ^ 2 = 2 ^ k := Real.sq_sqrt hp.le
  have hsne : Real.sqrt (2 ^ k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  ext x y
  rw [Matrix.mul_apply]
  have heq : (∑ z, testingBasis k σ x z * (testingBasis k σ).transpose z y) =
      (Real.sqrt (2 ^ k : ℝ))⁻¹ ^ 2 * sign (σ x) * sign (σ y) *
        (∑ z, walsh k x z * walsh k y z) := by
    simp only [testingBasis, Matrix.transpose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [heq, walsh_row_inner, Matrix.one_apply]
  split_ifs with hxy
  · subst y
    have hsign := sign_sq (σ x)
    field_simp
    nlinarith
  · ring

theorem testingBasis_transpose_orthogonal (k : ℕ) (σ : Cube k → Bool) :
    (testingBasis k σ).transpose * testingBasis k σ = 1 :=
  Matrix.mul_eq_one_comm.mp (testingBasis_orthogonal k σ)

section Signs

variable {ι : Type*} [Fintype ι]

def signedSum (σ : ι → Bool) (a : ι → ℝ) : ℝ := ∑ i, sign (σ i) * a i

def signLaw (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  (PMF.uniformOfFintype (ι → Bool)).toMeasure

instance signLaw_probability : IsProbabilityMeasure (signLaw ι) := by
  unfold signLaw
  infer_instance

theorem signLaw_integral (f : (ι → Bool) → ℝ) :
    (∫ σ, f σ ∂signLaw ι) = (2 ^ Fintype.card ι : ℝ)⁻¹ * ∑ σ, f σ := by
  classical
  rw [signLaw, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    ← Finset.mul_sum]
  norm_num [ENNReal.toReal_pow]

theorem signed_exp_sum (a : ι → ℝ) (t : ℝ) :
    (∑ σ : ι → Bool, Real.exp (t * signedSum σ a)) =
      ∏ i, (Real.exp (t * a i) + Real.exp (-(t * a i))) := by
  simp only [signedSum, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) => Real.exp (t * (sign b * a i)))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [sign, mul_comm, mul_left_comm, mul_assoc, add_comm]

theorem signed_exp_sum_le (a : ι → ℝ) (t : ℝ) :
    (∑ σ : ι → Bool, Real.exp (t * signedSum σ a)) ≤
      2 ^ Fintype.card ι * Real.exp (t ^ 2 / 2 * ∑ i, a i ^ 2) := by
  rw [signed_exp_sum]
  calc
    _ ≤ ∏ i, (2 * Real.exp ((t * a i) ^ 2 / 2)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hc := Real.cosh_le_exp_half_sq (t * a i)
        rw [Real.cosh_eq] at hc
        linarith
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← Real.exp_sum, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem signedSum_subgaussian (a : ι → ℝ) (R : ℝ)
    (ha : ∑ i, a i ^ 2 ≤ R ^ 2) :
    HasSubgaussianMGF (fun σ => signedSum σ a) ⟨R ^ 2, sq_nonneg R⟩ (signLaw ι) := by
  constructor
  · intro t
    exact Integrable.of_finite
  · intro t
    rw [mgf, signLaw_integral]
    have h := mul_le_mul_of_nonneg_left (signed_exp_sum_le a t)
      (by positivity : 0 ≤ (2 ^ Fintype.card ι : ℝ)⁻¹)
    have hp : (2 ^ Fintype.card ι : ℝ) ≠ 0 := by positivity
    rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have hmul := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ t ^ 2 / 2)
    change t ^ 2 / 2 * (∑ i, a i ^ 2) ≤ R ^ 2 * t ^ 2 / 2
    nlinarith

theorem signedSum_abs_tail (a : ι → ℝ) (R : ℝ)
    (ha : ∑ i, a i ^ 2 ≤ R ^ 2) {τ : ℝ} (hτ : 0 ≤ τ) :
    (signLaw ι).real {σ | τ ≤ |signedSum σ a|} ≤
      2 * Real.exp (-τ ^ 2 / (2 * R ^ 2)) := by
  have hp := (signedSum_subgaussian a R ha).measure_ge_le hτ
  have hn := (signedSum_subgaussian (-a) R (by simpa using ha)).measure_ge_le hτ
  have hneg (σ : ι → Bool) : signedSum σ (-a) = -signedSum σ a := by
    simp [signedSum, Finset.sum_neg_distrib]
  simp only [hneg, NNReal.coe_mk] at hn hp
  have heq : {σ : ι → Bool | τ ≤ |signedSum σ a|} =
      {σ | τ ≤ signedSum σ a} ∪ {σ | τ ≤ -signedSum σ a} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [heq]
  have hu := measureReal_union_le (μ := signLaw ι)
    {σ | τ ≤ signedSum σ a} {σ | τ ≤ -signedSum σ a}
  linarith

theorem simultaneous_signedSum_tail {J : Type*} [Fintype J]
    (a : J → ι → ℝ) (R : ℝ) (ha : ∀ j, ∑ i, a j i ^ 2 ≤ R ^ 2)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (signLaw ι).real {σ | ∃ j, τ ≤ |signedSum σ (a j)|} ≤
      2 * Fintype.card J * Real.exp (-τ ^ 2 / (2 * R ^ 2)) := by
  have heq : {σ : ι → Bool | ∃ j, τ ≤ |signedSum σ (a j)|} =
      ⋃ j : J, {σ | τ ≤ |signedSum σ (a j)|} := by ext σ; simp
  rw [heq]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    signedSum_abs_tail (a j) R (ha j) hτ)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc,
    mul_left_comm, mul_comm] using hsum

theorem simultaneous_signedSum_good {J : Type*} [Fintype J]
    (a : J → ι → ℝ) (R : ℝ) (ha : ∀ j, ∑ i, a j i ^ 2 ≤ R ^ 2)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    1 - 2 * Fintype.card J * Real.exp (-τ ^ 2 / (2 * R ^ 2)) ≤
      (signLaw ι).real {σ | ∀ j, |signedSum σ (a j)| < τ} := by
  classical
  have hbad := simultaneous_signedSum_tail a R ha hτ
  have hm : MeasurableSet {σ : ι → Bool | ∃ j, τ ≤ |signedSum σ (a j)|} :=
    (Set.toFinite _).measurableSet
  have hcomp := measureReal_compl (μ := signLaw ι) hm
  have heq : {σ : ι → Bool | ∃ j, τ ≤ |signedSum σ (a j)|}ᶜ =
      {σ | ∀ j, |signedSum σ (a j)| < τ} := by ext σ; simp
  rw [heq, measureReal_univ_eq_one] at hcomp
  linarith

end Signs

theorem testingBasis_projection (k : ℕ) (σ : Cube k → Bool) (a : Cube k → ℝ)
    (j : Cube k) :
    ((testingBasis k σ).transpose *ᵥ a) j =
      (Real.sqrt (2 ^ k : ℝ))⁻¹ * signedSum σ (fun i => walsh k i j * a i) := by
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, testingBasis,
    signedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem walsh_coefficients_energy (k : ℕ) (a : Cube k → ℝ) (j : Cube k) :
    ∑ i, (walsh k i j * a i) ^ 2 = ∑ i, a i ^ 2 := by
  simp only [mul_pow, walsh_sq, one_mul]

end
end RandomOrthogonal
end Matvec
