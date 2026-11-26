import Smoothness2601.RadialWrapper

/-! A dimension-independent gradient barrier for the actual quadratic radial
wrapper, including arbitrarily large queries. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Smoothness2601.RadialWrapper
open Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem scale_half_radius {R : ℝ} (hR : 0 < R) (w : E) (hw : ‖w‖ ≤ R/2) :
    4/5 ≤ scale R w := by
  have hn : ‖w‖^2 ≤ R^2/4 := by nlinarith [norm_nonneg w]
  have hq : ‖w‖^2/R^2 ≤ 1/4 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith)
  have hs := root_square R w
  have hp := root_pos R w
  have hr : Real.sqrt (1+‖w‖^2/R^2) ≤ 5/4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hr (scale_pos R w).le
  rw [scale_inverse_root] at hm
  linarith

omit [CompleteSpace E] in
theorem radial_coefficient_bound {R G : ℝ} (hG : 1 ≤ G) (hR : R = 64*G)
    (w q : E) (hw : ‖w‖ ≤ R/2) (hq : ‖q‖ ≤ G) :
    |(1/16:ℝ)-scale R w^3/R^2*⟪w,q⟫| ≤ 9/128 := by
  have hRp : 0 < R := by linarith
  have hγ := scale_pos R w
  have hγ1 := scale_le_one R w
  have hpow : scale R w^3 ≤ 1 := pow_le_one₀ hγ.le hγ1
  have hi : |⟪w,q⟫| ≤ (R/2)*G :=
    (abs_real_inner_le_norm w q).trans (mul_le_mul hw hq (norm_nonneg q) (by positivity))
  have hc : |scale R w^3/R^2*⟪w,q⟫| ≤ 1/128 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ scale R w^3/R^2)]
    calc
      _ ≤ (1/R^2)*((R/2)*G) := mul_le_mul
        (div_le_div_of_nonneg_right hpow (sq_nonneg R)) hi (abs_nonneg _) (by positivity)
      _ = 1/128 := by rw [hR]; field_simp; ring
  exact (abs_sub _ _).trans (by
    rw [abs_of_pos (by norm_num : (0:ℝ)<1/16)]
    linarith)

omit [CompleteSpace E] in
/-- The only chain inputs are its bounded gradient and a hidden coordinate
whose gradient is at most -1. The compression and penalty are concrete. -/
theorem arbitrary_query_barrier {R G : ℝ} (hG : 1 ≤ G) (hR : R = 64*G)
    (w q u : E) (hq : ‖q‖ ≤ G) (hu : ‖u‖ = 1)
    (hhidden : |⟪compress R w,u⟫| ≤ 1) (hcoord : ⟪q,u⟫ ≤ -1) :
    (1/2:ℝ) ≤ ‖compressDerivative R w q+(1/16:ℝ) • w‖ := by
  have hRp : 0 < R := by linarith
  by_cases hw : R/2 ≤ ‖w‖
  · have hn := compressDerivative_norm_le R hRp w q
    have htri : ‖(1/16:ℝ) • w‖ ≤
        ‖compressDerivative R w q+(1/16:ℝ) • w‖+‖compressDerivative R w q‖ := by
      have ht := norm_sub_le (compressDerivative R w q+(1/16:ℝ) • w) (compressDerivative R w q)
      simpa only [add_sub_cancel_left] using ht
    rw [norm_smul,Real.norm_eq_abs] at htri
    rw [abs_of_pos (by norm_num : (0:ℝ)<1/16)] at htri
    nlinarith
  · have hw' := (lt_of_not_ge hw).le
    have hγ := scale_pos R w
    have hγl := scale_half_radius hRp w hw'
    have hc := radial_coefficient_bound hG hR w q hw' hq
    have hwu : |⟪w,u⟫| ≤ 5/4 := by
      have hh : scale R w*|⟪w,u⟫| ≤ 1 := by
        simpa only [compress,real_inner_smul_left,abs_mul,abs_of_pos hγ] using hhidden
      nlinarith [abs_nonneg ⟪w,u⟫]
    have he : compressDerivative R w q+(1/16:ℝ) • w =
        scale R w • q+((1/16:ℝ)-scale R w^3/R^2*⟪w,q⟫) • w := by
      rw [compressDerivative_apply,sub_smul]
      abel
    have hi : ⟪compressDerivative R w q+(1/16:ℝ) • w,u⟫ ≤ -1/2 := by
      rw [he,inner_add_left,real_inner_smul_left,real_inner_smul_left]
      have h1 := mul_le_mul_of_nonneg_left hcoord hγ.le
      have h2 : ((1/16:ℝ)-scale R w^3/R^2*⟪w,q⟫)*⟪w,u⟫ ≤ (9/128)*(5/4) := by
        calc
          _ ≤ |((1/16:ℝ)-scale R w^3/R^2*⟪w,q⟫)*⟪w,u⟫| := le_abs_self _
          _ = _ := abs_mul _ _
          _ ≤ _ := mul_le_mul hc hwu (abs_nonneg _) (by norm_num)
      linarith
    have hn := abs_real_inner_le_norm (compressDerivative R w q+(1/16:ℝ) • w) u
    rw [hu,mul_one] at hn
    have ha := neg_le_abs ⟪compressDerivative R w q+(1/16:ℝ) • w,u⟫
    linarith

end Smoothness2601.RadialWrapper
