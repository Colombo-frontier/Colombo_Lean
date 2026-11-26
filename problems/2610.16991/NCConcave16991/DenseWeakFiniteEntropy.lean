import NCConcave16991.DenseWeakEntropy
import Mathlib.Analysis.Convex.Jensen

/-! # Finite probability masses and the exact Shannon chain rule

Zero-probability histories are included through the continuous negMulLog
convention and zero conditional masses. No information inequality or adaptive
experiment law is postulated.
-/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

structure FiniteLaw (I : Type*) [Fintype I] where
  mass : I → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  sum_one : ∑ i, mass i = 1

def finiteEntropy {I : Type*} [Fintype I] (mass : I → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (mass i)

def rowMass {I J : Type*} [Fintype J] (mass : I × J → ℝ) (i : I) : ℝ :=
  ∑ j, mass (i, j)

def conditionalMass {I J : Type*} [Fintype J] (mass : I × J → ℝ) (i : I) (j : J) : ℝ :=
  mass (i, j) / rowMass mass i

theorem rowMass_nonneg {I J : Type*} [Fintype J] (mass : I × J → ℝ)
    (hp : ∀ z, 0 ≤ mass z) (i : I) : 0 ≤ rowMass mass i :=
  Finset.sum_nonneg (fun j _ ↦ hp (i, j))

theorem conditionalMass_nonneg {I J : Type*} [Fintype J] (mass : I × J → ℝ)
    (hp : ∀ z, 0 ≤ mass z) (i : I) (j : J) : 0 ≤ conditionalMass mass i j :=
  div_nonneg (hp _) (rowMass_nonneg mass hp i)

theorem conditionalMass_sum {I J : Type*} [Fintype J] (mass : I × J → ℝ)
    (i : I) (hi : rowMass mass i ≠ 0) : ∑ j, conditionalMass mass i j = 1 := by
  simp only [conditionalMass, div_eq_mul_inv, ← Finset.sum_mul]
  change rowMass mass i * (rowMass mass i)⁻¹ = 1
  exact mul_inv_cancel₀ hi

theorem rowMass_zero_entry {I J : Type*} [Fintype J] (mass : I × J → ℝ)
    (hp : ∀ z, 0 ≤ mass z) (i : I) (hi : rowMass mass i = 0) (j : J) : mass (i, j) = 0 := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset J)) ↦ hp (i, k))
    (Finset.mem_univ j)
  change mass (i, j) ≤ rowMass mass i at h
  rw [hi] at h
  exact le_antisymm h (hp _)

theorem row_entropy_identity {I J : Type*} [Fintype J] (mass : I × J → ℝ)
    (hp : ∀ z, 0 ≤ mass z) (i : I) :
    (∑ j, Real.negMulLog (mass (i, j))) = Real.negMulLog (rowMass mass i) +
      rowMass mass i * finiteEntropy (conditionalMass mass i) := by
  by_cases hi : rowMass mass i = 0
  · have hz := rowMass_zero_entry mass hp i hi
    simp only [hz, hi, Real.negMulLog_zero, Finset.sum_const_zero, zero_mul, add_zero]
  · have he (j : J) : Real.negMulLog (mass (i, j)) =
        conditionalMass mass i j * Real.negMulLog (rowMass mass i) +
          rowMass mass i * Real.negMulLog (conditionalMass mass i j) := by
      rw [← Real.negMulLog_mul]
      congr 1
      unfold conditionalMass
      field_simp
    rw [Finset.sum_congr rfl (fun j _ ↦ he j), Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, conditionalMass_sum mass i hi, one_mul]
    rfl

/-- The genuine finite Shannon chain rule, including histories of mass zero. -/
theorem finiteEntropy_chain_rule {I J : Type*} [Fintype I] [Fintype J]
    (mass : I × J → ℝ) (hp : ∀ z, 0 ≤ mass z) :
    finiteEntropy mass = finiteEntropy (rowMass mass) +
      ∑ i, rowMass mass i * finiteEntropy (conditionalMass mass i) := by
  unfold finiteEntropy
  rw [Fintype.sum_prod_type]
  have hsum := Finset.sum_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ row_entropy_identity mass hp i)
  rw [hsum, Finset.sum_add_distrib]
  rfl

namespace FiniteLaw

variable {I J : Type*} [Fintype I] [Fintype J]

theorem mass_le_one (P : FiniteLaw I) (i : I) : P.mass i ≤ 1 := by
  rw [← P.sum_one]
  exact Finset.single_le_sum (fun j _ ↦ P.nonneg j) (Finset.mem_univ i)

def fst (P : FiniteLaw (I × J)) : FiniteLaw I where
  mass := rowMass P.mass
  nonneg := rowMass_nonneg P.mass P.nonneg
  sum_one := by
    simpa only [rowMass, Fintype.sum_prod_type] using P.sum_one

def snd (P : FiniteLaw (I × J)) : FiniteLaw J where
  mass := fun j ↦ ∑ i, P.mass (i, j)
  nonneg := fun j ↦ Finset.sum_nonneg (fun i _ ↦ P.nonneg (i, j))
  sum_one := by
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using P.sum_one

def product (P : FiniteLaw I) (Q : FiniteLaw J) : FiniteLaw (I × J) where
  mass := fun z ↦ P.mass z.1 * Q.mass z.2
  nonneg := fun z ↦ mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  sum_one := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Q.sum_one, mul_one, P.sum_one]

def entropy (P : FiniteLaw I) : ℝ := finiteEntropy P.mass

def mutualInformation (P : FiniteLaw (I × J)) : ℝ :=
  P.fst.entropy + P.snd.entropy - P.entropy

theorem product_entropy (P : FiniteLaw I) (Q : FiniteLaw J) :
    (P.product Q).entropy = P.entropy + Q.entropy := by
  simp only [entropy, finiteEntropy, product, Fintype.sum_prod_type, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, P.sum_one, Q.sum_one,
    mul_one, one_mul]

end FiniteLaw

end NCConcave16991.DenseWeakHiding
