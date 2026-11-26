import GradientHessian.NalenMidpoint
import GradientHessian.NalenTrajectory

/-! Averaging cancels the linear Hessian term in the actual gradient.
The resulting estimate depends on the Hessian Lipschitz constant and the
diameter of the averaging block, not on the Hessian norm. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

section Normed
variable [NormedSpace ℝ E]

def blockMean (q : ℕ) (y : ℕ → E) : E := (q : ℝ)⁻¹ • ∑ j ∈ Finset.range q,y j

theorem sum_sub_blockMean (q : ℕ) (hq : 1 ≤ q) (y : ℕ → E) :
    ∑ j ∈ Finset.range q,(y j-blockMean q y)=0 := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℝ]
  simp [blockMean,smul_smul,hq']

theorem blockMean_distance (q : ℕ) (hq : 1 ≤ q) (y : ℕ → E) {R : ℝ}
    (hdiam : ∀ i < q,∀ j < q,‖y i-y j‖ ≤ R) (j : ℕ) (hj : j < q) :
    ‖y j-blockMean q y‖ ≤ R := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : y j-blockMean q y=(q : ℝ)⁻¹ • ∑ i ∈ Finset.range q,(y j-y i) := by
    simp [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ,smul_sub,smul_smul,hq',blockMean]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q))]
  calc
    (q : ℝ)⁻¹*‖∑ i ∈ Finset.range q,(y j-y i)‖ ≤
        (q : ℝ)⁻¹*∑ i ∈ Finset.range q,‖y j-y i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ ≤ (q : ℝ)⁻¹*∑ _i ∈ Finset.range q,R :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi => hdiam j hj i (Finset.mem_range.mp hi)))
        (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = R := by simp [hq']

end Normed

section Hilbert
variable [InnerProductSpace ℝ E] [CompleteSpace E]

theorem averaging_gradient_error {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f)))
    (q : ℕ) (hq : 1 ≤ q) (y : ℕ → E) {R : ℝ} (hR : 0 ≤ R)
    (hd : ∀ j < q,‖y j-blockMean q y‖ ≤ R) :
    ‖(∑ j ∈ Finset.range q,gradient f (y j))-(q : ℝ) • gradient f (blockMean q y)‖ ≤
      (q : ℝ)*R^2 := by
  let c := blockMean q y
  let r (j : ℕ) := gradient f (y j)-gradient f c-hessianOperator f c (y j-c)
  have he : (∑ j ∈ Finset.range q,r j)=
      (∑ j ∈ Finset.range q,gradient f (y j))-(q : ℝ) • gradient f c := by
    have hz : (∑ j ∈ Finset.range q,y j)-(∑ _j ∈ Finset.range q,c)=0 := by
      rw [← Finset.sum_sub_distrib]
      exact sum_sub_blockMean q hq y
    simp only [r,Finset.sum_sub_distrib,← map_sum]
    rw [hz,map_zero,sub_zero,
      Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℝ]
  rw [← he]
  calc
    ‖∑ j ∈ Finset.range q,r j‖ ≤ ∑ j ∈ Finset.range q,‖r j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range q,R^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have ht := gradient_taylor hf hL c (y j)
      simp only [NNReal.coe_one,one_mul] at ht
      exact ht.trans ((sq_le_sq₀ (norm_nonneg _) hR).2 (hd j (Finset.mem_range.mp hj)))
    _ = _ := by simp

theorem averaging_gradient_norm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f)))
    (q : ℕ) (hq : 1 ≤ q) (y : ℕ → E) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : ∀ i < q,∀ j < q,‖y i-y j‖ ≤ R) :
    (q : ℝ)*‖gradient f (blockMean q y)‖ ≤
      ‖∑ j ∈ Finset.range q,gradient f (y j)‖+(q : ℝ)*R^2 := by
  have h := averaging_gradient_error hf hL q hq y hR (blockMean_distance q hq y hdiam)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((q : ℝ) • gradient f (blockMean q y)) (∑ j ∈ Finset.range q,gradient f (y j)) 0
  rw [sub_zero,sub_zero,norm_sub_rev,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg q)] at ht
  linarith

theorem ValidSteps.queryPoint_distance {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (p q : ℕ) (hpq : p+q ≤ N)
    (i j : ℕ) (hi : i < q) (hj : j < q) :
    ‖s.queryPoint (p+i)-s.queryPoint (p+j)‖ ≤ (q : ℝ)*D := by
  have hdir (i j : ℕ) (hi : i < q) (hj : j < q) (hij : i ≤ j) :
      ‖s.queryPoint (p+i)-s.queryPoint (p+j)‖ ≤ (q : ℝ)*D := by
    have he : p+i+(j-i)=p+j := by omega
    have hd := hs.displacement (p+i) (j-i) (by rw [he]; omega)
    rw [he,norm_sub_rev] at hd
    have hm := norm_midpoint_sub (s.x (p+i)) (s.x (p+j)) (s.δ (p+i+1)) (s.δ (p+j+1))
    have hδ := (norm_sub_le (s.δ (p+i+1)) (s.δ (p+j+1))).trans
      (add_le_add (hs.delta_norm _ (by omega)) (hs.delta_norm _ (by omega)))
    have hspan : ((j-i : ℕ) : ℝ)+1 ≤ (q : ℝ) := by exact_mod_cast (show j-i+1 ≤ q by omega)
    have hb := mul_le_mul_of_nonneg_right hspan hs.radius_nonneg
    change ‖midpoint _ _-midpoint _ _‖ ≤ _
    nlinarith only [hd,hm,hδ,hb]
  rcases le_total i j with hij | hji
  · exact hdir i j hi hj hij
  · rw [norm_sub_rev]
    exact hdir j i hj hi hji

theorem ValidSteps.candidate_gradient_norm {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f)))
    (q k : ℕ) (hq : 1 ≤ q) (hkq : k*q+q ≤ N) :
    (q : ℝ)*‖gradient f (s.candidate q k)‖ ≤
      ‖∑ j ∈ Finset.range q,gradient f (s.queryPoint (k*q+j))‖+(q : ℝ)^3*D^2 := by
  have hD := hs.radius_nonneg
  have h := averaging_gradient_norm hf hL q hq (fun j => s.queryPoint (k*q+j))
    (show 0 ≤ (q : ℝ)*D by positivity) (fun i hi j hj => hs.queryPoint_distance (k*q) q hkq i j hi hj)
  change (q : ℝ)*‖gradient f (s.candidate q k)‖ ≤ _ at h
  convert h using 1
  ring

end Hilbert
end GradientHessian.Nalen
