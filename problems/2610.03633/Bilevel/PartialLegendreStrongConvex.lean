import Bilevel.PartialLegendreBasic

/-! Sharp lower strong-convexity modulus of the actual conjugate and exact
response of its linearly coupled lower objective. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {δ : NNReal} (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G)
  (P : E → ℝ) (hP : ∀ z,HasGradientAt P (G z) z)
include hG hP

theorem primal_upper_model (z d : E) :
    primal P (z+d) ≤ primal P z+⟪z+G z,d⟫+(1+(δ:ℝ))/2*‖d‖^2 := by
  have hl (x y : E) : ‖G x-G y‖ ≤ (δ:ℝ)*‖x-y‖ := by
    simpa only [dist_eq_norm] using hG.dist_le_mul x y
  have ht := JointDerivative.gradient_taylor P G (δ:ℝ) hP hl z d
  have hp : P (z+d)-P z-⟪G z,d⟫ ≤ (δ:ℝ)/2*‖d‖^2 :=
    (le_abs_self _).trans ht
  have hs := norm_add_sq_real z d
  unfold primal
  rw [inner_add_left]
  nlinarith

theorem conjugate_strong_model (y w : E) :
    conjugate hδ hG P y+⟪solution hδ hG y,w-y⟫+
      1/(2*(1+(δ:ℝ)))*‖w-y‖^2 ≤ conjugate hδ hG P w := by
  let c := 1+(δ:ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  let z := solution hδ hG y
  let d := (1/c) • (w-y)
  have hmax := conjugate_maximizes hδ hG P hP w (z+d)
  have hprimal := primal_upper_model hG P hP z d
  have heq : z+G z=y := solution_equation hδ hG y
  rw [heq] at hprimal
  have hid : ⟪w,z+d⟫-primal P z-⟪y,d⟫-c/2*‖d‖^2 =
      conjugate hδ hG P y+⟪z,w-y⟫+1/(2*c)*‖w-y‖^2 := by
    have hzy : ⟪z,y⟫ = ⟪y,z⟫ := real_inner_comm _ _
    have hzw : ⟪z,w⟫ = ⟪w,z⟫ := real_inner_comm _ _
    have hlin : ⟪w,z+d⟫-primal P z-⟪y,d⟫ =
        conjugate hδ hG P y+⟪z,w-y⟫+⟪w-y,d⟫ := by
      rw [inner_add_right,inner_sub_right,inner_sub_left,hzy,hzw]
      change _ = (⟪y,z⟫-primal P z)+_+_
      ring
    rw [hlin]
    dsimp [d]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,
      Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hc)]
    field_simp
    ring
  change primal P (z+d) ≤ primal P z+⟪y,d⟫+c/2*‖d‖^2 at hprimal
  change conjugate hδ hG P y+⟪z,w-y⟫+1/(2*c)*‖w-y‖^2 ≤ _
  rw [← hid]
  linarith

omit hP in
def coupledLower (m : ℝ) (b y : E) : ℝ := m*conjugate hδ hG P y-⟪b,y⟫

theorem coupledLower_growth {m : ℝ} (hm : 0 < m) (z y : E) :
    m/(2*(1+(δ:ℝ)))*‖y-(z+G z)‖^2 ≤
      coupledLower hδ hG P m (m • z) y-coupledLower hδ hG P m (m • z) (z+G z) := by
  have hs : solution hδ hG (z+G z)=z :=
    (solution_of_equation hδ hG (z+G z) z rfl).symm
  have hh := conjugate_strong_model hδ hG P hP (z+G z) y
  rw [hs] at hh
  have hmH := mul_le_mul_of_nonneg_left hh hm.le
  unfold coupledLower
  simp only [real_inner_smul_left]
  rw [inner_sub_right] at hmH
  ring_nf at hmH ⊢
  linarith

theorem coupledLower_minimizes {m : ℝ} (hm : 0 < m) (z y : E) :
    coupledLower hδ hG P m (m • z) (z+G z) ≤ coupledLower hδ hG P m (m • z) y := by
  have hh := coupledLower_growth hδ hG P hP hm z y
  have hp : 0 ≤ m/(2*(1+(δ:ℝ)))*‖y-(z+G z)‖^2 := by positivity
  linarith

theorem coupledLower_unique {m : ℝ} (hm : 0 < m) (z y : E) :
    (∀ w, coupledLower hδ hG P m (m • z) y ≤ coupledLower hδ hG P m (m • z) w) ↔
      y=z+G z := by
  constructor
  · intro hy
    have hh := coupledLower_growth hδ hG P hP hm z y
    have hm0 : 0 < m/(2*(1+(δ:ℝ))) := by positivity
    have ht := hy (z+G z)
    have hs : ‖y-(z+G z)‖^2=0 := by nlinarith [sq_nonneg ‖y-(z+G z)‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
  · rintro rfl w
    exact coupledLower_minimizes hδ hG P hP hm z w

end Bilevel.PartialLegendre
