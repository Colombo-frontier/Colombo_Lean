import SecondOrder.TriangularPairs
import Mathlib.Analysis.InnerProductSpace.Dual

open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def coordinateDifference (e : UpperPair d) : Point d →L[ℝ] ℝ :=
  EuclideanSpace.proj e.1.1-EuclideanSpace.proj e.1.2

@[simp] theorem coordinateDifference_apply (e : UpperPair d) (x : Point d) :
    coordinateDifference e x = x e.1.1-x e.1.2 := rfl

def pairDirection (e : UpperPair d) : Point d :=
  (InnerProductSpace.toDual ℝ (Point d)).symm (coordinateDifference e)

@[simp] theorem pairDirection_inner (e : UpperPair d) (v : Point d) :
    ⟪pairDirection e,v⟫_ℝ = v e.1.1-v e.1.2 := by
  rw [pairDirection, InnerProductSpace.toDual_symm_apply, coordinateDifference_apply]

theorem coordinateDifference_bound (e : UpperPair d) (v : Point d) :
    |coordinateDifference e v| ≤ 2*‖v‖ := by
  have h1 := PiLp.norm_apply_le (p := (2:ENNReal)) v e.1.1
  have h2 := PiLp.norm_apply_le (p := (2:ENNReal)) v e.1.2
  change |v e.1.1| ≤ ‖v‖ at h1
  change |v e.1.2| ≤ ‖v‖ at h2
  change |v e.1.1-v e.1.2| ≤ _
  exact (abs_sub _ _).trans (by linarith)

theorem pair_difference_cross_sum (u v : Point d) :
    (∑ e : UpperPair d, |coordinateDifference e u| * |coordinateDifference e v|) ≤
      (d:ℝ)*‖u‖*‖v‖ := by
  have hu := pair_difference_sq_sum_le u
  have hv := pair_difference_sq_sum_le v
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun e : UpperPair d => |coordinateDifference e u|) (fun e : UpperPair d => |coordinateDifference e v|)
  simp only [sq_abs, coordinateDifference_apply] at hc
  have hm := mul_le_mul hu hv (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  have hs : (∑ e : UpperPair d, |coordinateDifference e u| * |coordinateDifference e v|)^2 ≤
      ((d:ℝ)*‖u‖*‖v‖)^2 := by
    simpa only [coordinateDifference_apply] using (by nlinarith [hc.trans hm] :
      (∑ e : UpperPair d, |u e.1.1-u e.1.2| * |v e.1.1-v e.1.2|)^2 ≤
        ((d:ℝ)*‖u‖*‖v‖)^2)
  have hn : 0 ≤ (d:ℝ)*‖u‖*‖v‖ := by positivity
  nlinarith

theorem pair_difference_abs_sum (v : Point d) :
    (∑ e : UpperPair d, |coordinateDifference e v|) ≤ (d:ℝ)*Real.sqrt d*‖v‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : UpperPair d => (1:ℝ)) (fun e : UpperPair d => |coordinateDifference e v|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs, coordinateDifference_apply, upperPair_card_real] at hc
  have hd : (d:ℝ)*((d:ℝ)-1)/2 ≤ (d:ℝ)^2 := by nlinarith [sq_nonneg (d:ℝ), Nat.cast_nonneg (α := ℝ) d]
  have hm := mul_le_mul hd (pair_difference_sq_sum_le v)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg (d:ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  have hp : ((d:ℝ)*Real.sqrt d*‖v‖)^2 = (d:ℝ)^3*‖v‖^2 := by rw [mul_pow, mul_pow, hs]; ring
  have hn : 0 ≤ (d:ℝ)*Real.sqrt d*‖v‖ := by positivity
  change (∑ e : UpperPair d, |v e.1.1-v e.1.2|) ≤ _
  nlinarith [hc.trans hm]

def pairVectorSum (b : UpperPair d → ℝ) : Point d := ∑ e, b e • pairDirection e

def pairLaplacian (b : UpperPair d → ℝ) : Point d →L[ℝ] Point d :=
  ∑ e, b e • (coordinateDifference e).smulRight (pairDirection e)

theorem pairVectorSum_inner (b : UpperPair d → ℝ) (v : Point d) :
    ⟪pairVectorSum b,v⟫_ℝ = ∑ e, b e*coordinateDifference e v := by
  simp only [pairVectorSum, sum_inner, inner_smul_left, RCLike.conj_to_real,
    pairDirection_inner, coordinateDifference_apply]

theorem pairLaplacian_inner (b : UpperPair d → ℝ) (u v : Point d) :
    ⟪pairLaplacian b u,v⟫_ℝ = ∑ e, b e*coordinateDifference e u*coordinateDifference e v := by
  simp only [pairLaplacian, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, sum_inner, inner_smul_left, RCLike.conj_to_real,
    pairDirection_inner, coordinateDifference_apply, mul_assoc]

theorem pairVectorSum_norm_bound (b : UpperPair d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ e, |b e| ≤ A) : ‖pairVectorSum b‖ ≤ A*(d:ℝ)*Real.sqrt d := by
  have he (v : Point d) : |⟪pairVectorSum b,v⟫_ℝ| ≤ A*(d:ℝ)*Real.sqrt d*‖v‖ := by
    rw [pairVectorSum_inner]
    calc
      _ ≤ ∑ e, |b e*coordinateDifference e v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e, A*|coordinateDifference e v| := Finset.sum_le_sum (fun e _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb e) (abs_nonneg _))
      _ = A*∑ e, |coordinateDifference e v| := (Finset.mul_sum _ _ _).symm
      _ ≤ A*((d:ℝ)*Real.sqrt d*‖v‖) := mul_le_mul_of_nonneg_left (pair_difference_abs_sum v) hA
      _ = _ := by ring
  have hh := he (pairVectorSum b)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
  have hn : 0 ≤ A*(d:ℝ)*Real.sqrt d := by positivity
  nlinarith [norm_nonneg (pairVectorSum b)]

theorem pairLaplacian_norm_bound (b : UpperPair d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ e, |b e| ≤ A) : ‖pairLaplacian b‖ ≤ A*(d:ℝ) := by
  have he (u v : Point d) : |⟪pairLaplacian b u,v⟫_ℝ| ≤ A*(d:ℝ)*‖u‖*‖v‖ := by
    rw [pairLaplacian_inner]
    calc
      _ ≤ ∑ e, |b e*coordinateDifference e u*coordinateDifference e v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e, A*(|coordinateDifference e u| * |coordinateDifference e v|) :=
        Finset.sum_le_sum (fun e _ => by
          simp only [abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (hb e) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = A*∑ e, |coordinateDifference e u| * |coordinateDifference e v| := (Finset.mul_sum _ _ _).symm
      _ ≤ A*((d:ℝ)*‖u‖*‖v‖) := mul_le_mul_of_nonneg_left (pair_difference_cross_sum u v) hA
      _ = _ := by ring
  apply (pairLaplacian b).opNorm_le_bound (by positivity)
  intro u
  have hh := he u (pairLaplacian b u)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
  have hn : 0 ≤ A*(d:ℝ)*‖u‖ := by positivity
  nlinarith [norm_nonneg (pairLaplacian b u)]

theorem pairLaplacian_sub (a b : UpperPair d → ℝ) :
    pairLaplacian a-pairLaplacian b = pairLaplacian (fun e => a e-b e) := by
  unfold pairLaplacian
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  exact (sub_smul (a e) (b e) _).symm

end
end SecondOrder
