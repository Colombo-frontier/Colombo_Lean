import Smoothness2601.SineGeometry
import Smoothness2601.SineProductBounds

/-! A genuine Population constructor for the sine instance. Every baseline
budget follows from scalar/profile estimates, rather than being assumed for
the final full-gradient functions. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped RealInnerProductSpace
namespace Smoothness2601.SineGeometry
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

structure Profiles (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] where
  A : X → ℝ
  B : X → ℝ
  gA : X → X
  gB : X → X
  LA : ℝ
  C₀ : ℝ
  C₁ : ℝ
  C₂ : ℝ
  LA_nonneg : 0 ≤ LA
  C₀_nonneg : 0 ≤ C₀
  C₁_nonneg : 0 ≤ C₁
  C₂_nonneg : 0 ≤ C₂
  has_A : ∀ x, HasGradientAt A (gA x) x
  has_B : ∀ x, HasGradientAt B (gB x) x
  bound_B : ∀ x, |B x| ≤ C₀
  bound_gB : ∀ x, ‖gB x‖ ≤ C₁
  lip_gA : ∀ x z, ‖gA x-gA z‖ ≤ LA*‖x-z‖
  lip_gB : ∀ x z, ‖gB x-gB z‖ ≤ C₂*‖x-z‖

namespace Profiles
variable (F : Profiles X)

theorem lip_B (x z : X) : |F.B x-F.B z| ≤ F.C₁*‖x-z‖ :=
  scalar_lipschitz_of_gradient_bound F.has_B F.bound_gB x z

def signal (m a h : ℝ) (z : Joint X ℝ) : Joint X ℝ :=
  pack ((-m*a*h*Real.sin (z.snd/h)) • F.gB z.fst)
    ((-m*a*Real.cos (z.snd/h))*F.B z.fst)

theorem lowerGradient_decompose (m a h : ℝ) (z : Joint X ℝ) :
    lowerGradient F.B F.gB m a h z = pack (0:X) (m*z.snd)+F.signal m a h z := by
  apply (WithLp.equiv 2 (X × ℝ)).injective
  apply Prod.ext
  · simp [lowerGradient,signal,pack]
  · simp [lowerGradient,signal,pack,SineLift.lowerGradient]
    ring

theorem signal_norm {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (z : Joint X ℝ) : ‖F.signal m a h z‖ ≤ m*a*h*F.C₁+m*a*F.C₀ := by
  apply (joint_norm_le_sum _ _).trans
  have hx : ‖(-m*a*h*Real.sin (z.snd/h)) • F.gB z.fst‖ ≤ m*a*h*F.C₁ := by
    rw [norm_smul,Real.norm_eq_abs]
    have hc : |-m*a*h*Real.sin (z.snd/h)| ≤ m*a*h := by
      rw [abs_mul,abs_mul,abs_mul,abs_neg,abs_of_nonneg hm,abs_of_nonneg ha,abs_of_nonneg hh]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)).trans_eq (by ring)
    exact mul_le_mul hc (F.bound_gB _) (norm_nonneg _) (by positivity)
  have hy : |(-m*a*Real.cos (z.snd/h))*F.B z.fst| ≤ m*a*F.C₀ := by
    rw [abs_mul]
    have hc : |-m*a*Real.cos (z.snd/h)| ≤ m*a := by
      rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hm,abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)).trans_eq (by ring)
    exact mul_le_mul hc (F.bound_B _) (abs_nonneg _) (by positivity)
  exact add_le_add hx hy

theorem profile_joint_difference {h : ℝ} (hh : 0 < h)
    (trig : ℝ → ℝ) (ht : ∀ y, |trig y| ≤ 1)
    (hl : ∀ y w, |trig y-trig w| ≤ |y-w|)
    (z w : Joint X ℝ) :
    ‖trig (z.snd/h) • F.gB z.fst-trig (w.snd/h) • F.gB w.fst‖ ≤
      (F.C₂+F.C₁/h)*‖z-w‖ := by
  have hp := product_difference hh F.C₂_nonneg F.C₁_nonneg trig F.gB ht hl
    F.bound_gB F.lip_gB z.fst w.fst z.snd w.snd
  have hc := joint_difference_components z.fst w.fst z.snd w.snd
  change ‖z.fst-w.fst‖ ≤ ‖z-w‖ ∧ |z.snd-w.snd| ≤ ‖z-w‖ at hc
  exact hp.trans ((add_le_add (mul_le_mul_of_nonneg_left hc.1 F.C₂_nonneg)
    (mul_le_mul_of_nonneg_left hc.2 (div_nonneg F.C₁_nonneg hh.le))).trans_eq (by ring))

theorem value_joint_difference {h : ℝ} (hh : 0 < h)
    (trig : ℝ → ℝ) (ht : ∀ y, |trig y| ≤ 1)
    (hl : ∀ y w, |trig y-trig w| ≤ |y-w|)
    (z w : Joint X ℝ) :
    |trig (z.snd/h)*F.B z.fst-trig (w.snd/h)*F.B w.fst| ≤
      (F.C₁+F.C₀/h)*‖z-w‖ := by
  have hp := product_difference hh F.C₁_nonneg F.C₀_nonneg trig F.B ht hl
    F.bound_B F.lip_B z.fst w.fst z.snd w.snd
  have hc := joint_difference_components z.fst w.fst z.snd w.snd
  change ‖z.fst-w.fst‖ ≤ ‖z-w‖ ∧ |z.snd-w.snd| ≤ ‖z-w‖ at hc
  exact hp.trans ((add_le_add (mul_le_mul_of_nonneg_left hc.1 F.C₁_nonneg)
    (mul_le_mul_of_nonneg_left hc.2 (div_nonneg F.C₀_nonneg hh.le))).trans_eq (by ring))

def signalLipschitz (m a h : ℝ) : ℝ := m*a*h*F.C₂+2*m*a*F.C₁+m*a*F.C₀/h

theorem signal_difference {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 < h)
    (z w : Joint X ℝ) : ‖F.signal m a h z-F.signal m a h w‖ ≤
      F.signalLipschitz m a h*‖z-w‖ := by
  have hx := F.profile_joint_difference hh Real.sin Real.abs_sin_le_one sin_difference z w
  have hy := F.value_joint_difference hh Real.cos Real.abs_cos_le_one cos_difference z w
  have he : F.signal m a h z-F.signal m a h w =
      pack ((-m*a*h) • (Real.sin (z.snd/h) • F.gB z.fst-Real.sin (w.snd/h) • F.gB w.fst))
        ((-m*a)*(Real.cos (z.snd/h)*F.B z.fst-Real.cos (w.snd/h)*F.B w.fst)) := by
    apply (WithLp.equiv 2 (X × ℝ)).injective
    apply Prod.ext
    · simp only [signal,pack,smul_sub,mul_smul]
      rfl
    · change (-m*a*Real.cos (z.snd/h))*F.B z.fst-(-m*a*Real.cos (w.snd/h))*F.B w.fst =
        (-m*a)*(Real.cos (z.snd/h)*F.B z.fst-Real.cos (w.snd/h)*F.B w.fst)
      ring
  rw [he]
  apply (joint_norm_le_sum _ _).trans
  rw [norm_smul,Real.norm_eq_abs,
    show |-m*a*h| = m*a*h by rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hm,abs_of_nonneg ha,abs_of_pos hh],
    abs_mul,
    show |-m*a| = m*a by rw [abs_mul,abs_neg,abs_of_nonneg hm,abs_of_nonneg ha]]
  exact (add_le_add (mul_le_mul_of_nonneg_left hx (by positivity))
    (mul_le_mul_of_nonneg_left hy (by positivity))).trans_eq (by
      unfold signalLipschitz
      field_simp
      ring)

theorem full_gradient_difference {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 < h)
    (z w : Joint X ℝ) :
    ‖lowerGradient F.B F.gB m a h z-lowerGradient F.B F.gB m a h w‖ ≤
      (m+F.signalLipschitz m a h)*‖z-w‖ := by
  rw [F.lowerGradient_decompose,F.lowerGradient_decompose]
  have he : pack (0:X) (m*z.snd)+F.signal m a h z-(pack (0:X) (m*w.snd)+F.signal m a h w) =
      pack (0:X) (m*(z.snd-w.snd))+(F.signal m a h z-F.signal m a h w) := by
    have hp : pack (0:X) (m*z.snd)-pack (0:X) (m*w.snd) = pack (0:X) (m*(z.snd-w.snd)) := by
      apply (WithLp.equiv 2 (X × ℝ)).injective
      apply Prod.ext
      · simp [pack]
      · change m*z.snd-m*w.snd = m*(z.snd-w.snd)
        ring
    rw [← hp]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hb : ‖pack (0:X) (m*(z.snd-w.snd))‖ ≤ m*‖z-w‖ := by
    apply (joint_norm_le_sum _ _).trans
    rw [norm_zero,zero_add,abs_mul,abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_left (joint_difference_components z.fst w.fst z.snd w.snd).2 hm
  exact (add_le_add hb (F.signal_difference hm ha hh z w)).trans_eq (by ring)

end Profiles
end Smoothness2601.SineGeometry
