import Smoothness2601.SineLift
import Bilevel.PrimitiveGeometry
import Mathlib.Analysis.Calculus.MeanValue

/-! Global product estimates for the complete sine signal and its Hessian
blocks. Bounds are on arbitrary joint queries, not just on the lower solution. -/
noncomputable section
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.SineGeometry

theorem sin_difference (u v : ℝ) : |Real.sin u-Real.sin v| ≤ |u-v| := by
  simpa only [Real.norm_eq_abs,one_mul] using
    (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := (1:ℝ))
      (fun z _ => (Real.hasDerivAt_sin z).hasDerivWithinAt)
      (fun z _ => Real.abs_cos_le_one z) convex_univ (Set.mem_univ v) (Set.mem_univ u))

theorem cos_difference (u v : ℝ) : |Real.cos u-Real.cos v| ≤ |u-v| := by
  simpa only [Real.norm_eq_abs,one_mul] using
    (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := (1:ℝ))
      (fun z _ => (Real.hasDerivAt_cos z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs,abs_neg] using Real.abs_sin_le_one z)
      convex_univ (Set.mem_univ v) (Set.mem_univ u))

variable {X E : Type*} [NormedAddCommGroup X] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem product_difference {h L C : ℝ} (hh : 0 < h) (_hL : 0 ≤ L) (_hC : 0 ≤ C)
    (F : ℝ → ℝ) (g : X → E) (hF : ∀ t, |F t| ≤ 1)
    (hFl : ∀ u v, |F u-F v| ≤ |u-v|)
    (hg : ∀ x, ‖g x‖ ≤ C) (hgl : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖)
    (x z : X) (y w : ℝ) :
    ‖F (y/h) • g x-F (w/h) • g z‖ ≤ L*‖x-z‖+(C/h)*|y-w| := by
  have he : F (y/h) • g x-F (w/h) • g z =
      F (y/h) • (g x-g z)+(F (y/h)-F (w/h)) • g z := by
    simp only [smul_sub,sub_smul]
    abel
  have hd : |F (y/h)-F (w/h)| ≤ |y-w|/h := by
    convert hFl (y/h) (w/h) using 1
    rw [← sub_div,abs_div,abs_of_pos hh]
  rw [he]
  calc
    _ ≤ ‖F (y/h) • (g x-g z)‖+‖(F (y/h)-F (w/h)) • g z‖ := norm_add_le _ _
    _ = |F (y/h)| * ‖g x-g z‖+|F (y/h)-F (w/h)| * ‖g z‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ 1*(L*‖x-z‖)+(|y-w|/h)*C :=
      add_le_add (mul_le_mul (hF _) (hgl _ _) (norm_nonneg _) zero_le_one)
        (mul_le_mul hd (hg _) (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem scaled_product_difference {h L C : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (F : ℝ → ℝ) (g : X → E) (hF : ∀ t, |F t| ≤ 1)
    (hFl : ∀ u v, |F u-F v| ≤ |u-v|)
    (hg : ∀ x, ‖g x‖ ≤ C) (hgl : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖)
    (c : ℝ) (x z : X) (y w : ℝ) :
    ‖(c*F (y/h)) • g x-(c*F (w/h)) • g z‖ ≤
      |c| * (L*‖x-z‖+(C/h)*|y-w|) := by
  rw [mul_smul,mul_smul,← smul_sub,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (product_difference hh hL hC F g hF hFl hg hgl x z y w)
    (abs_nonneg c)

section Joint
variable [InnerProductSpace ℝ X]

theorem joint_norm_le_sum (x : X) (y : ℝ) : ‖pack x y‖ ≤ ‖x‖+|y| := by
  have hn := norm_sq (pack x y)
  change ‖pack x y‖^2 = ‖x‖^2+‖y‖^2 at hn
  rw [Real.norm_eq_abs] at hn
  nlinarith [norm_nonneg (pack x y),norm_nonneg x,abs_nonneg y]

theorem joint_difference_components (x z : X) (y w : ℝ) :
    ‖x-z‖ ≤ ‖pack x y-pack z w‖ ∧ |y-w| ≤ ‖pack x y-pack z w‖ := by
  have hn := norm_sq (pack x y-pack z w)
  change ‖pack x y-pack z w‖^2 = ‖x-z‖^2+‖y-w‖^2 at hn
  rw [Real.norm_eq_abs] at hn
  constructor <;> nlinarith [norm_nonneg (pack x y-pack z w),norm_nonneg (x-z),abs_nonneg (y-w),
    sq_nonneg ‖x-z‖,sq_nonneg |y-w|]

theorem scalar_lipschitz_of_gradient_bound [CompleteSpace X] {B : X → ℝ} {gB : X → X} {C : ℝ}
    (hg : ∀ x, HasGradientAt B (gB x) x) (hC : ∀ x, ‖gB x‖ ≤ C) (x z : X) :
    |B x-B z| ≤ C*‖x-z‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hg x).hasFDerivAt.hasFDerivWithinAt)
    (fun x _ => by simpa only [LinearIsometryEquiv.norm_map] using hC x)
    convex_univ (Set.mem_univ z) (Set.mem_univ x)

end Joint
end Smoothness2601.SineGeometry
