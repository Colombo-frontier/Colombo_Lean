import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Dimension-free gate-product estimates

Algebraic estimates and actual derivative certificates for the prefix products
used in `lem:B-bounds`. These results do not by themselves construct the smooth
step, the localized summand, or the complete split chain.
-/

noncomputable section
namespace Smoothness2601
namespace PrefixProducts
open Finset
open scoped BigOperators RealInnerProductSpace

variable {ι : Type*} [DecidableEq ι]

def oneFailure (s : Finset ι) (a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (1 - a i) * ∏ j ∈ s.erase i, a j

theorem oneFailure_insert {s : Finset ι} {k : ι} (hk : k ∉ s) (a : ι → ℝ) :
    oneFailure (insert k s) a = (1 - a k) * (∏ j ∈ s, a j) + a k * oneFailure s a := by
  unfold oneFailure
  rw [sum_insert hk, erase_insert hk, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hki : k ≠ i := by intro h; subst i; exact hk hi
  rw [erase_insert_of_ne hki, prod_insert (not_mem_mono (erase_subset i s) hk)]
  ring

theorem oneFailure_nonneg (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) : 0 ≤ oneFailure s a := by
  apply sum_nonneg
  intro i hi
  exact mul_nonneg (sub_nonneg.mpr (ha i hi).2)
    (prod_nonneg fun j hj => (ha j (mem_of_mem_erase hj)).1)

/-- A stronger form of eq:exact-one: zero or exactly one failure has mass ≤ 1. -/
theorem oneFailure_add_product_le_one (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    oneFailure s a + ∏ i ∈ s, a i ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp [oneFailure]
  | @insert k s hk ih =>
    have hak := ha k (mem_insert_self _ _)
    have has : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1 := fun i hi => ha i (mem_insert_of_mem hi)
    have hprod := Finset.prod_le_one (fun i hi => (has i hi).1) (fun i hi => (has i hi).2)
    have hsum := ih has
    rw [oneFailure_insert hk, prod_insert hk]
    nlinarith [mul_le_mul_of_nonneg_left hsum hak.1,
      mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hak.2)]

theorem oneFailure_le_one (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) : oneFailure s a ≤ 1 := by
  have h := oneFailure_add_product_le_one s a ha
  have hp := prod_nonneg (fun i hi => (ha i hi).1)
  linarith

/-- The actual coefficients of the derivative of a finite product have a
dimension-free sum of squares, including at zero gates. -/
theorem derivative_coefficients_sq_sum_le (s : Finset ι) (a d : ι → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1)
    (hd : ∀ i ∈ s, d i ^ 2 ≤ C * a i * (1 - a i)) :
    ∑ i ∈ s, (d i * ∏ j ∈ s.erase i, a j) ^ 2 ≤ C := by
  have hterm : ∀ i ∈ s,
      (d i * ∏ j ∈ s.erase i, a j) ^ 2 ≤ C * ((1 - a i) * ∏ j ∈ s.erase i, a j) := by
    intro i hi
    let P := ∏ j ∈ s.erase i, a j
    have hP0 : 0 ≤ P := prod_nonneg fun j hj => (ha j (mem_of_mem_erase hj)).1
    have hP1 : P ≤ 1 := Finset.prod_le_one (fun j hj => (ha j (mem_of_mem_erase hj)).1)
      (fun j hj => (ha j (mem_of_mem_erase hj)).2)
    have hai := ha i hi
    have hP2 : a i * P ^ 2 ≤ P := by nlinarith [mul_nonneg (sub_nonneg.mpr hai.2) (sq_nonneg P)]
    have h1 := mul_le_mul_of_nonneg_right (hd i hi) (sq_nonneg P)
    have h2 := mul_le_mul_of_nonneg_left hP2 (mul_nonneg hC (sub_nonneg.mpr hai.2))
    change (d i * P) ^ 2 ≤ C * ((1 - a i) * P)
    nlinarith
  calc
    _ ≤ ∑ i ∈ s, C * ((1 - a i) * ∏ j ∈ s.erase i, a j) := sum_le_sum hterm
    _ = C * oneFailure s a := by simp only [oneFailure, mul_sum]
    _ ≤ C := by nlinarith [mul_le_mul_of_nonneg_left (oneFailure_le_one s a ha) hC]

/-- The weighted logarithmic slopes remain controlled even with zero gates;
Lean's zero division gives ratio zero there and the inequality remains valid. -/
theorem weighted_ratio_sq_sum_le (s : Finset ι) (a d : ι → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1)
    (hd : ∀ i ∈ s, d i ^ 2 ≤ C * a i * (1 - a i)) :
    (∏ j ∈ s, a j) * (∑ i ∈ s, (d i / a i) ^ 2) ≤ C := by
  have hterm : ∀ i ∈ s,
      (∏ j ∈ s, a j) * (d i / a i) ^ 2 ≤ C * ((1 - a i) * ∏ j ∈ s.erase i, a j) := by
    intro i hi
    have hP0 : 0 ≤ ∏ j ∈ s.erase i, a j :=
      prod_nonneg fun j hj => (ha j (mem_of_mem_erase hj)).1
    by_cases hai : a i = 0
    · simp only [hai, div_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, one_mul]
      exact mul_nonneg hC hP0
    · have hai0 := lt_of_le_of_ne (ha i hi).1 (Ne.symm hai)
      have h := mul_le_mul_of_nonneg_right (hd i hi)
        (div_nonneg hP0 hai0.le)
      rw [← mul_prod_erase s a hi]
      convert h using 1 <;> field_simp <;> ring
  rw [mul_sum]
  calc
    _ ≤ ∑ i ∈ s, C * ((1 - a i) * ∏ j ∈ s.erase i, a j) := sum_le_sum hterm
    _ = C * oneFailure s a := by simp only [oneFailure, mul_sum]
    _ ≤ C := by nlinarith [mul_le_mul_of_nonneg_left (oneFailure_le_one s a ha) hC]

variable [Fintype ι]

def diagonalOperator (c : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => c i • EuclideanSpace.proj i)

omit [DecidableEq ι] in
@[simp] theorem diagonalOperator_apply (c : ι → ℝ) (u : EuclideanSpace ℝ ι) (i : ι) :
    diagonalOperator c u i = c i * u i := rfl

omit [DecidableEq ι] in
theorem euclidean_norm_sq (u : EuclideanSpace ℝ ι) : ‖u‖ ^ 2 = ∑ i, u i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [pow_two]

omit [DecidableEq ι] in
theorem diagonalOperator_norm_le (c : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ i, |c i| ≤ M) : ‖diagonalOperator c‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro u
  have hsq : ‖diagonalOperator c u‖ ^ 2 ≤ (M * ‖u‖) ^ 2 := by
    rw [euclidean_norm_sq, mul_pow, euclidean_norm_sq, Finset.mul_sum]
    apply sum_le_sum
    intro i _
    rw [diagonalOperator_apply, mul_pow]
    have hs : c i ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs (c i), mul_self_le_mul_self (abs_nonneg (c i)) (hc i)]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1 hsq

def ratioVector (a d : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm fun i => d i / a i

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem ratioVector_apply (a d : ι → ℝ) (i : ι) : ratioVector a d i = d i / a i := rfl

def rankOneOperator (b : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (InnerProductSpace.toDual ℝ _ b).smulRight b

omit [DecidableEq ι] in
@[simp] theorem rankOneOperator_apply (b u : EuclideanSpace ℝ ι) :
    rankOneOperator b u = ⟪b, u⟫ • b := rfl

omit [DecidableEq ι] in
theorem scaled_rankOne_norm_le (b : EuclideanSpace ℝ ι) {P C : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hb : P * ‖b‖ ^ 2 ≤ C) :
    ‖P • rankOneOperator b‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  simp only [ContinuousLinearMap.smul_apply, rankOneOperator_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hP]
  have h1 := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm b u) hP
  have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg b)
  have h3 := mul_le_mul_of_nonneg_right hb (norm_nonneg u)
  nlinarith

/-- The normalized Hessian formula from the manuscript, expressed as an actual
continuous linear operator rather than an unspecified matrix norm. -/
def normalizedHessian (a d e : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (∏ i, a i) • rankOneOperator (ratioVector a d) -
    diagonalOperator (fun i => (∏ j, a j) * (d i / a i) ^ 2) +
    diagonalOperator (fun i => e i * ∏ j ∈ univ.erase i, a j)

theorem normalizedHessian_norm_le (a d e : ι → ℝ) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hd : ∀ i, d i ^ 2 ≤ C * a i * (1 - a i)) (he : ∀ i, |e i| ≤ M) :
    ‖normalizedHessian a d e‖ ≤ 2 * C + M := by
  have hP : 0 ≤ ∏ i, a i := prod_nonneg fun i _ => (ha i).1
  have hb := weighted_ratio_sq_sum_le univ a d hC (fun i _ => ha i) (fun i _ => hd i)
  have hbnorm : (∏ i, a i) * ‖ratioVector a d‖ ^ 2 ≤ C := by
    simpa only [euclidean_norm_sq, ratioVector_apply] using hb
  have hRank := scaled_rankOne_norm_le (ratioVector a d) hP hC hbnorm
  have hDiag : ‖diagonalOperator (fun i => (∏ j, a j) * (d i / a i) ^ 2)‖ ≤ C := by
    apply diagonalOperator_norm_le _ hC
    intro i
    rw [abs_of_nonneg (mul_nonneg hP (sq_nonneg _))]
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => sq_nonneg (d j / a j)) (mem_univ i)
    exact (mul_le_mul_of_nonneg_left hi hP).trans hb
  have hLast : ‖diagonalOperator (fun i => e i * ∏ j ∈ univ.erase i, a j)‖ ≤ M := by
    apply diagonalOperator_norm_le _ hM
    intro i
    have hq0 := prod_nonneg fun j (_ : j ∈ univ.erase i) => (ha j).1
    have hq1 := Finset.prod_le_one (fun j (_ : j ∈ univ.erase i) => (ha j).1)
      (fun j (_ : j ∈ univ.erase i) => (ha j).2)
    rw [abs_mul, abs_of_nonneg hq0]
    exact (mul_le_mul (he i) hq1 hq0 hM).trans_eq (mul_one M)
  unfold normalizedHessian
  calc
    _ ≤ ‖(∏ i, a i) • rankOneOperator (ratioVector a d) -
        diagonalOperator (fun i => (∏ j, a j) * (d i / a i) ^ 2)‖ +
        ‖diagonalOperator (fun i => e i * ∏ j ∈ univ.erase i, a j)‖ := norm_add_le _ _
    _ ≤ (‖(∏ i, a i) • rankOneOperator (ratioVector a d)‖ +
        ‖diagonalOperator (fun i => (∏ j, a j) * (d i / a i) ^ 2)‖) +
        ‖diagonalOperator (fun i => e i * ∏ j ∈ univ.erase i, a j)‖ :=
      add_le_add_right (norm_sub_le _ _) _
    _ ≤ 2 * C + M := by linarith

theorem offDiagonal_coefficient (a d : ι → ℝ) (hzero : ∀ i, a i = 0 → d i = 0)
    {i j : ι} (hij : i ≠ j) :
    d i * d j * (∏ k ∈ (univ.erase i).erase j, a k) =
      (∏ k, a k) * (d i / a i) * (d j / a j) := by
  by_cases hai : a i = 0
  · simp [hai, hzero i hai]
  by_cases haj : a j = 0
  · simp [haj, hzero j haj]
  have hj : j ∈ (univ : Finset ι).erase i := mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩
  rw [← mul_prod_erase univ a (mem_univ i), ← mul_prod_erase (univ.erase i) a hj]
  field_simp
  ring

theorem normalizedHessian_apply_formula (a d e : ι → ℝ)
    (hzero : ∀ i, a i = 0 → d i = 0) (u : EuclideanSpace ℝ ι) (i : ι) :
    normalizedHessian a d e u i =
      e i * (∏ k ∈ univ.erase i, a k) * u i +
        ∑ j ∈ univ.erase i, (d i * d j * ∏ k ∈ (univ.erase i).erase j, a k) * u j := by
  have hsum : (∑ j, (d j / a j) * u j) =
      (∑ j ∈ univ.erase i, (d j / a j) * u j) + (d i / a i) * u i :=
    (sum_erase_add _ _ (mem_univ i)).symm
  have heq : ∑ j ∈ univ.erase i, (d i * d j * ∏ k ∈ (univ.erase i).erase j, a k) * u j =
      (∏ k, a k) * (d i / a i) * ∑ j ∈ univ.erase i, (d j / a j) * u j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [offDiagonal_coefficient a d hzero (Ne.symm (mem_erase.mp hj).1)]
    ring
  have hinner : ⟪ratioVector a d, u⟫ = ∑ j, (d j / a j) * u j := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, ratioVector_apply]
    apply sum_congr rfl
    intro j _
    ring
  rw [heq]
  simp only [normalizedHessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, rankOneOperator_apply, diagonalOperator_apply,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hinner, ratioVector_apply]
  rw [hsum]
  ring

def productFunction (a : ℝ → ℝ) (z : EuclideanSpace ℝ ι) : ℝ := ∏ i, a (z i)

omit [DecidableEq ι] in
theorem productFunction_bounds {a : ℝ → ℝ} (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1)
    (z : EuclideanSpace ℝ ι) : 0 ≤ productFunction a z ∧ productFunction a z ≤ 1 := by
  constructor
  · exact prod_nonneg fun i _ => (ha (z i)).1
  · exact Finset.prod_le_one (fun i _ => (ha (z i)).1) (fun i _ => (ha (z i)).2)

def productGradient (a d : ℝ → ℝ) (z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm fun i => d (z i) * ∏ j ∈ univ.erase i, a (z j)

@[simp] theorem productGradient_apply (a d : ℝ → ℝ) (z : EuclideanSpace ℝ ι) (i : ι) :
    productGradient a d z i = d (z i) * ∏ j ∈ univ.erase i, a (z j) := rfl

/-- The displayed vector is the genuine Fréchet gradient, with no derivative
formula or gradient bound assumed. -/
theorem hasGradientAt_productFunction (a d : ℝ → ℝ) (z : EuclideanSpace ℝ ι)
    (hd : ∀ i, HasDerivAt a (d (z i)) (z i)) :
    HasGradientAt (productFunction a) (productGradient a d z) z := by
  have hi : ∀ i ∈ (univ : Finset ι), HasFDerivAt (fun x : EuclideanSpace ℝ ι => a (x i))
      (d (z i) • EuclideanSpace.proj (𝕜 := ℝ) i) z := by
    intro i _
    exact (hd i).comp_hasFDerivAt z (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have hp := HasFDerivAt.finset_prod hi
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hp using 1
  ext v
  simp [InnerProductSpace.toDual_apply, PiLp.inner_apply, productGradient,
    mul_assoc, mul_comm, mul_left_comm]

theorem productGradient_norm_sq (a d : ℝ → ℝ) (z : EuclideanSpace ℝ ι) :
    ‖productGradient a d z‖ ^ 2 =
      ∑ i, (d (z i) * ∏ j ∈ univ.erase i, a (z j)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [productGradient, pow_two]

theorem productGradient_norm_le {a d : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hd : ∀ t, d t ^ 2 ≤ C * a t * (1 - a t))
    (z : EuclideanSpace ℝ ι) : ‖productGradient a d z‖ ≤ Real.sqrt C := by
  have h := derivative_coefficients_sq_sum_le univ (fun i => a (z i)) (fun i => d (z i))
    hC (fun i _ => ha (z i)) (fun i _ => hd (z i))
  rw [← productGradient_norm_sq a d z] at h
  exact (Real.le_sqrt (norm_nonneg _) hC).2 h

theorem gradient_productFunction_norm_le {a d : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hd : ∀ t, d t ^ 2 ≤ C * a t * (1 - a t))
    (hderiv : ∀ t, HasDerivAt a (d t) t) (z : EuclideanSpace ℝ ι) :
    ‖gradient (productFunction a) z‖ ≤ Real.sqrt C := by
  rw [(hasGradientAt_productFunction a d z (fun i => hderiv _)).gradient]
  exact productGradient_norm_le hC ha hd z

/-- Actual second derivative certificate for the product, including zero gates. -/
theorem hasFDerivAt_productGradient (a d e : ℝ → ℝ) (z : EuclideanSpace ℝ ι)
    (ha : ∀ i, HasDerivAt a (d (z i)) (z i))
    (hd : ∀ i, HasDerivAt d (e (z i)) (z i))
    (hzero : ∀ i, a (z i) = 0 → d (z i) = 0) :
    HasFDerivAt (productGradient a d)
      (normalizedHessian (fun i => a (z i)) (fun i => d (z i)) (fun i => e (z i))) z := by
  let row : ι → EuclideanSpace ℝ ι →L[ℝ] ℝ := fun i =>
    d (z i) • (∑ j ∈ univ.erase i,
      (∏ k ∈ (univ.erase i).erase j, a (z k)) • (d (z j) • EuclideanSpace.proj j)) +
      (∏ j ∈ univ.erase i, a (z j)) • (e (z i) • EuclideanSpace.proj i)
  have hrow : ∀ i, HasFDerivAt
      (fun x : EuclideanSpace ℝ ι => d (x i) * ∏ j ∈ univ.erase i, a (x j)) (row i) z := by
    intro i
    apply HasFDerivAt.mul
    · exact (hd i).comp_hasFDerivAt z (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    · apply HasFDerivAt.finset_prod
      intro j _
      exact (ha j).comp_hasFDerivAt z (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
  have hpi := hasFDerivAt_pi.mpr hrow
  have h := (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp z hpi
  convert h using 1
  ext v i
  rw [normalizedHessian_apply_formula _ _ _ hzero]
  simp [row, ContinuousLinearMap.sum_apply, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm, add_comm]
  rw [mul_sub, Finset.mul_sum]

/-- Dimension-free operator norm bound for the actual Hessian of the product. -/
theorem hessian_productFunction_norm_le {a d e : ℝ → ℝ} {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1)
    (hd : ∀ t, d t ^ 2 ≤ C * a t * (1 - a t)) (he : ∀ t, |e t| ≤ M)
    (hderiv : ∀ t, HasDerivAt a (d t) t) (hsecond : ∀ t, HasDerivAt d (e t) t)
    (z : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (gradient (productFunction a)) z‖ ≤ 2 * C + M := by
  have hgf : gradient (productFunction (ι := ι) a) = productGradient a d := by
    funext x
    exact (hasGradientAt_productFunction a d x (fun i => hderiv _)).gradient
  have hzero : ∀ i, a (z i) = 0 → d (z i) = 0 := by
    intro i hi
    have h := hd (z i)
    rw [hi] at h
    nlinarith [sq_nonneg (d (z i))]
  rw [hgf, (hasFDerivAt_productGradient a d e z (fun i => hderiv _) (fun i => hsecond _) hzero).fderiv]
  exact normalizedHessian_norm_le _ _ _ hC hM (fun i => ha _) (fun i => hd _) (fun i => he _)

end PrefixProducts
end Smoothness2601
