import Smoothness2601.SinePopulation

/-! Baseline source admissibility of the actual sine functions. Calibration
contains only numerical inequalities, never full-gradient/Population axioms. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped RealInnerProductSpace
namespace Smoothness2601.SineGeometry
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem smulRight_one_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) : ‖(1 : ℝ →L[ℝ] ℝ).smulRight u-(1 : ℝ →L[ℝ] ℝ).smulRight v‖ = ‖u-v‖ := by
  have he : (1 : ℝ →L[ℝ] ℝ).smulRight u-(1 : ℝ →L[ℝ] ℝ).smulRight v =
      (1 : ℝ →L[ℝ] ℝ).smulRight (u-v) := by
    apply ContinuousLinearMap.ext
    intro t
    simp [smul_sub]
  rw [he,ContinuousLinearMap.norm_smulRight_apply,norm_one,one_mul]

namespace Profiles
variable (F : Profiles X)

theorem mixed_variation {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 < h)
    (x x' : X) (y y' : ℝ) :
    ‖mixedBlock F.gB m a h x y-mixedBlock F.gB m a h x' y'‖ ≤
      m*a*(F.C₂+F.C₁/h)*‖pack x y-pack x' y'‖ := by
  rw [mixedBlock,mixedBlock,smulRight_one_difference]
  have he : (-m*a*Real.cos (y/h)) • F.gB x-(-m*a*Real.cos (y'/h)) • F.gB x' =
      (-m*a) • (Real.cos (y/h) • F.gB x-Real.cos (y'/h) • F.gB x') := by
    simp only [smul_sub,mul_smul]
  rw [he,norm_smul,Real.norm_eq_abs]
  rw [show |-m*a| = m*a by rw [abs_mul,abs_neg,abs_of_nonneg hm,abs_of_nonneg ha]]
  exact (mul_le_mul_of_nonneg_left
    (F.profile_joint_difference hh Real.cos Real.abs_cos_le_one cos_difference (pack x y) (pack x' y'))
    (by positivity)).trans_eq (by ring)

theorem lower_variation {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 < h)
    (x x' : X) (y y' : ℝ) :
    ‖lowerBlock F.B m a h x y-lowerBlock F.B m a h x' y'‖ ≤
      (m*a/h)*(F.C₁+F.C₀/h)*‖pack x y-pack x' y'‖ := by
  rw [lowerBlock,lowerBlock,smulRight_one_difference,Real.norm_eq_abs]
  have he : m*(1+(a/h)*F.B x*Real.sin (y/h))-m*(1+(a/h)*F.B x'*Real.sin (y'/h)) =
      (m*a/h)*(Real.sin (y/h)*F.B x-Real.sin (y'/h)*F.B x') := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ m*a/h)]
  exact (mul_le_mul_of_nonneg_left
    (F.value_joint_difference hh Real.sin Real.abs_sin_le_one sin_difference (pack x y) (pack x' y'))
    (by positivity)).trans_eq (by ring)

theorem upper_gradient_difference (c : ℝ) (z w : Joint X ℝ) :
    ‖upperGradient F.gA c z-upperGradient F.gA c w‖ ≤ F.LA*‖z-w‖ := by
  change ‖pack (F.gA z.fst-F.gA w.fst) (c-c)‖ ≤ _
  rw [sub_self]
  apply (joint_norm_le_sum _ _).trans
  rw [abs_zero,add_zero]
  exact (F.lip_gA _ _).trans (mul_le_mul_of_nonneg_left
    (joint_difference_components z.fst w.fst z.snd w.snd).1 F.LA_nonneg)

theorem lower_strong {m a h μ : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 < h)
    (hc : μ ≤ m*(1-(a/h)*F.C₀)) (x : X) (u v : ℝ) :
    lower F.B m a h (pack x u)+⟪(lowerGradient F.B F.gB m a h (pack x u)).snd,v-u⟫+
      μ/2*‖v-u‖^2 ≤ lower F.B m a h (pack x v) := by
  have hb : |(a/h)*F.B x| ≤ (a/h)*F.C₀ := by
    rw [abs_mul,abs_of_nonneg (div_nonneg ha hh.le)]
    exact mul_le_mul_of_nonneg_left (F.bound_B x) (div_nonneg ha hh.le)
  have hm' : μ ≤ m*(1-|(a/h)*F.B x|) := hc.trans
    (mul_le_mul_of_nonneg_left (by linarith) hm)
  simpa only [lower,lowerGradient,pack,
    Real.norm_eq_abs,sq_abs,RCLike.inner_apply,conj_trivial,mul_comm] using
    SineLift.lower_strong_convexity hm hh.ne' hm' u v

structure Calibration (b : Budgets) where
  m : ℝ
  a : ℝ
  h : ℝ
  c : ℝ
  m_nonneg : 0 ≤ m
  a_nonneg : 0 ≤ a
  h_pos : 0 < h
  upper_y : |c| ≤ b.L₀
  upper_smooth : F.LA ≤ b.L₁
  strong : b.μ ≤ m*(1-(a/h)*F.C₀)
  lower_smooth : m+F.signalLipschitz m a h ≤ b.L₁
  mixed_lipschitz : m*a*(F.C₂+F.C₁/h) ≤ b.L₂
  lower_lipschitz : (m*a/h)*(F.C₁+F.C₀/h) ≤ b.L₂

def population {b : Budgets} (S : F.Calibration b) : Population (X := X) (Y := ℝ) b where
  f := upper F.A S.c
  g := lower F.B S.m S.a S.h
  grad_f := upperGradient F.gA S.c
  grad_g := lowerGradient F.B F.gB S.m S.a S.h
  has_f := upper_hasGradientAt F.A F.gA F.has_A S.c
  has_g := lower_hasGradientAt F.B F.gB F.has_B S.m S.a S.h_pos.ne'
  gyy := lowerBlock F.B S.m S.a S.h
  gxy := mixedBlock F.gB S.m S.a S.h
  has_gyy := has_lowerBlock F.B F.gB S.m S.a S.h
  has_gxy := has_mixedBlock F.B F.gB S.m S.a S.h_pos.ne'
  strong_convex := F.lower_strong S.m_nonneg S.a_nonneg S.h_pos S.strong
  lipschitz_f_y := by
    intro x u v
    change ‖(F.A x+S.c*u)-(F.A x+S.c*v)‖ ≤ _
    rw [show (F.A x+S.c*u)-(F.A x+S.c*v) = S.c*(u-v) by ring,
      Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right S.upper_y (abs_nonneg _)
  smooth_f := fun z w => (F.upper_gradient_difference S.c z w).trans
    (mul_le_mul_of_nonneg_right S.upper_smooth (norm_nonneg _))
  smooth_g := fun z w => (F.full_gradient_difference S.m_nonneg S.a_nonneg S.h_pos z w).trans
    (mul_le_mul_of_nonneg_right S.lower_smooth (norm_nonneg _))
  variation_yy := fun x x' y y' => (F.lower_variation S.m_nonneg S.a_nonneg S.h_pos x x' y y').trans
    (mul_le_mul_of_nonneg_right S.lower_lipschitz (norm_nonneg _))
  variation_xy := fun x x' y y' => (F.mixed_variation S.m_nonneg S.a_nonneg S.h_pos x x' y y').trans
    (mul_le_mul_of_nonneg_right S.mixed_lipschitz (norm_nonneg _))

end Profiles
end Smoothness2601.SineGeometry
