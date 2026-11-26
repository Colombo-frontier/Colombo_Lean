import GradientHessian.HigherHierarchyRegularityArithmetic

/-! Explicit summable majorants, proved from the source scales rather than
assumed recurrence fields. They retain additive inherited coefficients. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open CouplingCost RegularityArithmetic
open scoped BigOperators

def crossConstant : ℝ := 24*weightConstant
def firstConstant (K : ℝ) : ℝ := FirstHeight.firstDerivativeConstant + amplitudeConstant K
def secondConstant (K : ℝ) : ℝ :=
  FirstHeight.firstDerivativeConstant + crossConstant*(4*firstConstant K) + amplitudeConstant K
def thirdConstant (K : ℝ) : ℝ :=
  FirstHeight.firstDerivativeConstant + crossConstant*(18*secondConstant K+4*firstConstant K) + amplitudeConstant K

theorem crossConstant_pos : 0 < crossConstant := mul_pos (by norm_num) weightConstant_pos
theorem firstConstant_pos {K : ℝ} (hK : 0 ≤ K) : 0 < firstConstant K :=
  add_pos FirstHeight.firstDerivativeConstant_pos (amplitudeConstant_pos hK)
theorem secondConstant_pos {K : ℝ} (hK : 0 ≤ K) : 0 < secondConstant K := by
  have h1 := firstConstant_pos hK
  have hC := crossConstant_pos
  have hA := amplitudeConstant_pos hK
  have hF := FirstHeight.firstDerivativeConstant_pos
  unfold secondConstant
  positivity
theorem thirdConstant_pos {K : ℝ} (hK : 0 ≤ K) : 0 < thirdConstant K := by
  have h1 := firstConstant_pos hK
  have h2 := secondConstant_pos hK
  have hC := crossConstant_pos
  have hA := amplitudeConstant_pos hK
  have hF := FirstHeight.firstDerivativeConstant_pos
  unfold thirdConstant
  positivity

def firstIncrement (K : ℝ) (m t : ℕ) : ℝ :=
  firstConstant K*((m+1:ℝ)^2*(1/3)^t+(8/3)^t+2^t+1)
def secondShape (t : ℕ) : ℝ := (1/3)^t+(1/9)^t+(8/9)^t+(1/3)^t+(2/3)^t
def thirdShape (t : ℕ) : ℝ := (1/3)^t+(1/9)^t+(1/27)^t+(8/27)^t+(2/9)^t+(1/9)^t
def secondIncrement (K : ℝ) (m t : ℕ) : ℝ := secondConstant K*(m+1)*secondShape t
def thirdIncrement (K : ℝ) (t : ℕ) : ℝ := thirdConstant K*thirdShape t
def firstMajorant (K : ℝ) (m t : ℕ) : ℝ := firstConstant K*(m+1:ℝ)^2 + ∑ j ∈ Finset.range t, firstIncrement K m j
def secondMajorant (K : ℝ) (m t : ℕ) : ℝ := secondConstant K*(m+1) + ∑ j ∈ Finset.range t, secondIncrement K m j
def thirdMajorant (K : ℝ) (t : ℕ) : ℝ := thirdConstant K + ∑ j ∈ Finset.range t, thirdIncrement K j

theorem firstMajorant_succ (K : ℝ) (m t : ℕ) :
    firstMajorant K m (t+1) = firstMajorant K m t + firstIncrement K m t := by
  simp only [firstMajorant, Finset.sum_range_succ]; ring
theorem secondMajorant_succ (K : ℝ) (m t : ℕ) :
    secondMajorant K m (t+1) = secondMajorant K m t + secondIncrement K m t := by
  simp only [secondMajorant, Finset.sum_range_succ]; ring
theorem thirdMajorant_succ (K : ℝ) (t : ℕ) :
    thirdMajorant K (t+1) = thirdMajorant K t + thirdIncrement K t := by
  simp only [thirdMajorant, Finset.sum_range_succ]; ring

theorem firstMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (m t : ℕ) : 0 ≤ firstMajorant K m t := by
  have hC := (firstConstant_pos hK).le
  unfold firstMajorant firstIncrement
  positivity
theorem secondMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (m t : ℕ) : 0 ≤ secondMajorant K m t := by
  have hC := (secondConstant_pos hK).le
  unfold secondMajorant secondIncrement secondShape
  positivity
theorem thirdMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (t : ℕ) : 0 ≤ thirdMajorant K t := by
  have hC := (thirdConstant_pos hK).le
  unfold thirdMajorant thirdIncrement thirdShape
  positivity

theorem firstMajorant_bound {K : ℝ} (hK : 0 ≤ K) (m t : ℕ) :
    firstMajorant K m t ≤ 4*firstConstant K*((m+1:ℝ)^2+(8/3)^t) :=
  first_order (firstMajorant K m) (firstConstant_pos hK).le (by simp [firstMajorant])
    (fun j => (firstMajorant_succ K m j).le) t
theorem secondMajorant_bound {K : ℝ} (hK : 0 ≤ K) (m t : ℕ) :
    secondMajorant K m t ≤ 18*secondConstant K*(m+1) :=
  second_order (secondMajorant K m) (by positivity) (secondConstant_pos hK).le
    (by simp [secondMajorant]) (fun j => (secondMajorant_succ K m j).le) t
theorem thirdMajorant_bound {K : ℝ} (hK : 0 ≤ K) (t : ℕ) :
    thirdMajorant K t ≤ 9*thirdConstant K :=
  third_order (thirdMajorant K) (thirdConstant_pos hK).le (by simp [thirdMajorant])
    (fun j => (thirdMajorant_succ K j).le) t

theorem first_increment_covers {K : ℝ} (hK : 0 ≤ K) (m t : ℕ) :
    newAmplitude m K t/width m t ≤ firstIncrement K m t := by
  have hA := (amplitudeConstant_pos hK).le
  have hC := (firstConstant_pos hK).le
  have hAC : amplitudeConstant K ≤ firstConstant K := by unfold firstConstant; linarith [FirstHeight.firstDerivativeConstant_pos]
  have h1 := div_le_div_of_nonneg_right (newAmplitude_bound m hK t) (width_pos m t).le
  have h2 := mul_le_mul_of_nonneg_left (envelope_div_one m t) hA
  have h3 := mul_le_mul_of_nonneg_right hAC
    (by positivity : 0 ≤ (m+1:ℝ)^2*(1/3)^t+(8/3)^t)
  have h4 : 0 ≤ firstConstant K*(2^t+1) := mul_nonneg hC (by positivity)
  unfold firstIncrement
  rw [mul_div_assoc] at h1
  nlinarith

theorem second_increment_covers {K : ℝ} (hK : 0 ≤ K) (m t : ℕ) :
    crossConstant*firstMajorant K m t/width m t + newAmplitude m K t/width m t^2 ≤
      secondIncrement K m t := by
  have hC := crossConstant_pos.le
  have hA := (amplitudeConstant_pos hK).le
  have h1C : 0 ≤ 4*firstConstant K := mul_nonneg (by norm_num) (firstConstant_pos hK).le
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (firstMajorant_bound hK m t) hC) (width_pos m t).le
  have h2 := mul_le_mul_of_nonneg_left (first_shape_div_one m t) (mul_nonneg hC h1C)
  have h3 := div_le_div_of_nonneg_right (newAmplitude_bound m hK t) (sq_nonneg (width m t))
  have h4 := mul_le_mul_of_nonneg_left (envelope_div_two m t) hA
  have hshape1 : (1/3:ℝ)^t+(8/9)^t ≤ secondShape t := by
    unfold secondShape
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/9) t,
      pow_nonneg (by norm_num : (0:ℝ) ≤ 1/3) t, pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) t]
  have hshape2 : (1/9:ℝ)^t+(8/9)^t ≤ secondShape t := by
    unfold secondShape
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/3) t, pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) t]
  have hs1 := mul_le_mul_of_nonneg_left hshape1
    (mul_nonneg (mul_nonneg hC h1C) (by positivity : (0:ℝ) ≤ m+1))
  have hs2 := mul_le_mul_of_nonneg_left hshape2 (mul_nonneg hA (by positivity : (0:ℝ) ≤ m+1))
  have hf := mul_nonneg FirstHeight.firstDerivativeConstant_pos.le
    (mul_nonneg (by positivity : (0:ℝ) ≤ m+1) (by unfold secondShape; positivity : 0 ≤ secondShape t))
  rw [mul_div_assoc] at h3
  have h1' : crossConstant*firstMajorant K m t/width m t ≤
      crossConstant*(4*firstConstant K)*((m+1)*((1/3)^t+(8/9)^t)) := by
    apply h1.trans
    convert h2 using 1; ring
  unfold secondIncrement secondConstant
  nlinarith

theorem third_increment_covers {K : ℝ} (hK : 0 ≤ K) (m t : ℕ) :
    crossConstant*secondMajorant K m t/width m t + crossConstant*firstMajorant K m t/width m t^2 +
      newAmplitude m K t/width m t^3 ≤ thirdIncrement K t := by
  have hC := crossConstant_pos.le
  have hA := (amplitudeConstant_pos hK).le
  have h1C : 0 ≤ 4*firstConstant K := mul_nonneg (by norm_num) (firstConstant_pos hK).le
  have h2C : 0 ≤ 18*secondConstant K := mul_nonneg (by norm_num) (secondConstant_pos hK).le
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (secondMajorant_bound hK m t) hC) (width_pos m t).le
  have h2 := mul_le_mul_of_nonneg_left (tasks_div_width m t) (mul_nonneg hC h2C)
  have h3 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (firstMajorant_bound hK m t) hC) (sq_nonneg (width m t))
  have h4 := mul_le_mul_of_nonneg_left (first_shape_div_two m t) (mul_nonneg hC h1C)
  have h5 := div_le_div_of_nonneg_right (newAmplitude_bound m hK t) (pow_nonneg (width_pos m t).le 3)
  have h6 := mul_le_mul_of_nonneg_left (envelope_div_three m t) hA
  have ht0 : 0 ≤ thirdShape t := by unfold thirdShape; positivity
  have ht1 : (1/3:ℝ)^t ≤ thirdShape t := by
    unfold thirdShape
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/9) t, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/27) t,
      pow_nonneg (by norm_num : (0:ℝ) ≤ 8/27) t, pow_nonneg (by norm_num : (0:ℝ) ≤ 2/9) t]
  have ht2 : (1/9:ℝ)^t+(8/27)^t ≤ thirdShape t := by
    unfold thirdShape
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/3) t, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/27) t,
      pow_nonneg (by norm_num : (0:ℝ) ≤ 1/9) t, pow_nonneg (by norm_num : (0:ℝ) ≤ 2/9) t]
  have ht3 : (1/27:ℝ)^t+(8/27)^t ≤ thirdShape t := by
    unfold thirdShape
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/3) t, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/9) t,
      pow_nonneg (by norm_num : (0:ℝ) ≤ 2/9) t]
  have hs1 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hC h2C)
  have hs2 := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hC h1C)
  have hs3 := mul_le_mul_of_nonneg_left ht3 hA
  have hf := mul_nonneg FirstHeight.firstDerivativeConstant_pos.le ht0
  have ha : crossConstant*secondMajorant K m t/width m t ≤ crossConstant*(18*secondConstant K)*(1/3)^t := by
    apply h1.trans
    convert h2 using 1; ring
  have hb : crossConstant*firstMajorant K m t/width m t^2 ≤
      crossConstant*(4*firstConstant K)*((1/9)^t+(8/27)^t) := by
    apply h3.trans
    convert h4 using 1; ring
  rw [mul_div_assoc] at h5
  unfold thirdIncrement thirdConstant
  nlinarith

end GradientHessian.HigherHierarchy

